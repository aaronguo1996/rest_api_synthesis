import json
import re
from fuzzer.error import InvalidSwaggerDoc, InvalidSchemaType
from fuzzer.request import Connection
from openapi import defs

class PreProcessor:
    def __init__(self, doc_path: str):
        self._doc_path = doc_path
        self._union_types = {}
        self._counter = 0
        self._new_refs = {}

    def preprocess(self, output_file):
        # restructure the input file to make it satisfy the OpenAPI format
        with open(self._doc_path, 'r') as f:
            doc_obj = json.loads(f.read())
            # we can only preprocess OpenAPI v2
            if doc_obj.get(defs.DOC_VERSION) != defs.DOC_V2:
                raise InvalidSwaggerDoc

            doc_obj_v2 = self._fix_items_types(doc_obj)
            # add new definitions into doc
            doc_obj_v2[defs.DOC_RESPONSES] = {}
            for path, ref in self._new_refs.items():
                assert len(path) == 2
                doc_obj_v2[path[0]][path[1]] = ref
            doc_obj_v3 = self._to_openapi_v3(doc_obj_v2)
            # doc_obj_final = doc_obj_v3
            doc_obj_final = self._fix_union_types(doc_obj_v3)
            self._write_to_file(doc_obj_final, output_file)

    def _not_none_type(self, t):
        if isinstance(t, str):
            return t != defs.TYPE_NONE and t is not None
        elif isinstance(t, dict):
            return t.get(defs.DOC_TYPE) != defs.TYPE_NONE
        else:
            raise InvalidSchemaType

    def _create_ref_type(self, addition_path, typ):
        if defs.DOC_REF in typ or not isinstance(typ, dict):
            return typ
        else:
            # create a new reference type
            new_ref = "objs_ref_" + str(self._counter)
            self._counter += 1

            fixed_typ = self._fix_items_in_schema(
                addition_path + [new_ref], addition_path, typ)
            ref_path = addition_path + [new_ref]
            self._new_refs[tuple(ref_path)] = fixed_typ

            ref_path = [defs.DOC_LOCALREF] + addition_path + [new_ref]
            ref_path_str = '/'.join(ref_path) 
            return {defs.DOC_REF: ref_path_str}

    def _fix_list_types(self, path, addition_path, typs):
        true_types = [item for item in typs if self._not_none_type(item)]
        fixed_types = [self._create_ref_type(addition_path, t)
                       for t in true_types]

        if len(fixed_types) > 1:
            # keep track of them item list internally and
            # temporarily select the first one to fit into v2.0
            # restore it after the conversion to v3.0
            self._union_types[tuple(path)] = fixed_types

        return fixed_types

    def _fix_items_in_schema(self, path, addition_path, schema):
        if isinstance(schema, str):
            return schema
        elif isinstance(schema, dict):
            properties = schema.get(defs.DOC_PROPERTIES)
            schema_type = schema.get(defs.DOC_TYPE)
            schema_items = schema.get(defs.DOC_ITEMS)
            
            # TODO: get rid of this once the bug in convertor is fixed
            schema.pop(defs.DOC_ADDITIONAL_PROP, None)

            # first, sanitize the schema_type if exists
            if schema_type:
                if isinstance(schema_type, list):
                    fixed_types = self._fix_list_types(
                        path, addition_path, schema_type)
                    schema[defs.DOC_TYPE] = fixed_types[0]
                elif schema_type and schema_type == "none":
                    schema[defs.DOC_TYPE] = defs.TYPE_STRING

            # second, sanitize the properties and items
            schema_type = schema.get(defs.DOC_TYPE)
            if properties:
                for field in properties:
                    curr_path = path + [defs.DOC_PROPERTIES, field]
                    new_schema = self._fix_items_in_schema(
                        curr_path, addition_path, properties.get(field))
                    properties[field] = new_schema

            elif schema_items and schema_type != defs.TYPE_ARRAY:
                fixed_types = self._fix_list_types(
                    path, addition_path, schema_items)
                schema.pop(defs.DOC_ITEMS)
                return fixed_types[0]

            elif schema_items and schema_type == defs.TYPE_ARRAY:
                curr_path = path + [defs.DOC_ITEMS]
                new_schema = self._fix_items_in_schema(
                    curr_path, addition_path, schema_items)
                schema[defs.DOC_ITEMS] = new_schema

            return schema
        elif isinstance(schema, list):
            fixed_obj = {"items": schema}
            return self._fix_items_in_schema(path, addition_path, fixed_obj)
        else:
            raise InvalidSchemaType(path, schema)

    def _fix_items_types(self, doc):
        # operation over OpenAPI v2.0
        definitions = doc.get(defs.DOC_DEFINITIONS)
        if not definitions:
            raise InvalidSwaggerDoc

        for schema_name, schema in definitions.items():
            curr_path = [
                defs.DOC_DEFINITIONS,
                schema_name,
            ]
            fixed_schema = self._fix_items_in_schema(
                curr_path, [defs.DOC_DEFINITIONS], schema)
            definitions[schema_name] = fixed_schema

        paths = doc.get(defs.DOC_PATHS)
        if not paths:
            raise InvalidSwaggerDoc

        for path, path_def in paths.items():
            for method, method_def in path_def.items():
                responses = method_def.get(defs.DOC_RESPONSES)
                for code, response_def in responses.items():
                    curr_path = [
                        defs.DOC_PATHS, 
                        path, 
                        method, 
                        defs.DOC_RESPONSES, 
                        code, 
                        defs.DOC_SCHEMA,
                    ]
                    new_schema = self._fix_items_in_schema(
                        curr_path, [defs.DOC_DEFINITIONS],
                        response_def.get(defs.DOC_SCHEMA))
                    responses[code][defs.DOC_SCHEMA] = new_schema

        return doc

    def _correct_ref_in_path(self, path_str):
        path = path_str.split('/')
        if (path[0] == defs.DOC_LOCALREF and
            path[1] == defs.DOC_DEFINITIONS):
            fixed_path = [
                defs.DOC_LOCALREF,
                defs.DOC_COMPONENTS,
                defs.DOC_SCHEMAS
            ]
            return '/'.join(fixed_path + path[2:])
        else:
            raise InvalidSchemaType(path_str)

    def _correct_ref(self, obj):
        if isinstance(obj, dict):
            for field in obj:
                if field == defs.DOC_REF:
                    obj[defs.DOC_REF] = self._correct_ref_in_path(obj[field])
                else:
                    obj[field] = self._correct_ref(obj[field])

            return obj
        elif isinstance(obj, list):
            return [self._correct_ref(item) for item in obj]
        else:
            return obj

    def _fix_union_types(self, doc):
        for path, typs in reversed(self._union_types.items()):
            try:
                fixed_typs = [self._correct_ref(item) for item in typs]
                if path[0] == defs.DOC_DEFINITIONS:
                    # mapping to components/schemas in v3
                    obj = doc.get(defs.DOC_COMPONENTS)
                    obj = obj.get(defs.DOC_SCHEMAS)
                    for field in path[1:-1]:
                        obj = obj.get(field)    
                else:
                    obj = doc
                    for i in range(len(path[:-1])):
                        field = path[i]
                        prev_field = path[i-1] if i > 0 else None
                        obj = obj.get(field)
                        # if field is default or response code
                        field_regex = r"^([0-9]{3})$|^(default)$"
                        if (prev_field == defs.DOC_RESPONSES and
                            re.search(field_regex, field)):
                            obj = obj.get(defs.DOC_CONTENT)
                            obj = obj.get(defs.HEADER_JSON)
                    
                last_field = path[-1]
                obj[last_field] = {"oneOf": fixed_typs}
            except Exception:
                print(path, typs)

        return doc

    def _to_openapi_v3(self, doc):
        conn = Connection("converter.swagger.io", "/api")
        _, response = conn.send_and_recv(
            "/convert", 
            {defs.HEADER_CONTENT: defs.HEADER_JSON}, 
            doc
        )
        # print(response[1])
        return json.loads(response)

    def _write_to_file(self, doc, output_file):
        with open(output_file, 'w+') as output:
            output.write(json.dumps(doc))