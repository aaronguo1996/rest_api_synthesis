from collections import defaultdict
import re
import random

from openapi import defs
from schemas import types
from analyzer.utils import ignore_arg_name
import consts

class ErrorResponse:
    def __init__(self, msg):
        self._error_msg = msg

    def __str__(self):
        return f"error: {self._error_msg}"

    def __repr__(self):
        return self.__str__()

    def __eq__(self, other):
        if isinstance(other, ErrorResponse):
            return NotImplemented

        return self._error_msg == other._error_msg
        
class Parameter:
    def __init__(self, method, arg_name, func_name, 
        path, is_required, array_level, typ, value):
        self.method = method
        self.arg_name = arg_name
        self.func_name = func_name
        self.value = value
        self.type = typ
        self.is_required = is_required
        self.path = path
        self.array_level = array_level

    def _flatten_object(self, path_to_defs, skip_fields):
        results = []
        values = defaultdict(list)

        try:
            # store the value into a mapping
            if self.type is not None and str(self.type) != "None":
                values[str(self.type)].append(self.value)
            
            for k, v in self.value.items():
                if k in skip_fields:
                    continue

                field_schema, is_required = self.type.get_object_field(k)                
                if field_schema is None: # field not defined in the doc
                    continue

                p = Parameter(
                    self.method, k, self.func_name,
                    self.path + [k],
                    is_required and self.is_required,
                    self.array_level, 
                    field_schema, v
                )
                fd_results, fd_values = p.flatten(path_to_defs, skip_fields)
                results += fd_results
                for t in fd_values:
                    values[t] += fd_values[t]

        except:
            pass
            # return results, values
            # raise Exception(self.method, self.func_name, self.path, self.is_required, self.value, self.type)
        
        return results, values

    def _flatten_array(self, path_to_defs, skip_fields):
        results = []
        values = defaultdict(list)

        for i in range(len(self.value)):
            if self.type is not None and str(self.type) != "None":
                values[str(self.type)].append(self.value)

            if self.array_level is None:
                array_level = None
            else:
                array_level = self.array_level + 1

            try:
                item_type = self.type.get_item()
                p = Parameter(
                    self.method, defs.INDEX_ANY, self.func_name,
                    self.path + [defs.INDEX_ANY], self.is_required,
                    array_level, item_type, self.value[i])
            except:
                raise Exception(self.method, self.func_name, self.path, self.is_required, self.value, self.type)

            it_results, it_values = p.flatten(path_to_defs, skip_fields)
            results += it_results
            for t in it_values:
                values[t] += it_values[t]

        return results, values

    def flatten(self, path_to_defs, skip_fields):
        if ignore_arg_name(skip_fields, self.arg_name):
            return [], {}

        if isinstance(self.value, dict):
            return self._flatten_object(path_to_defs, skip_fields)
        elif isinstance(self.value, list):
            return self._flatten_array(path_to_defs, skip_fields)
        else:
            return [self], {}

    def flatten_ad_hoc(self, skip_fields):
        results = []
        
        if ignore_arg_name([defs.DOC_TOKEN], self.arg_name):
            return results

        if self.type is not None:
            # the arg itself is an ad-hoc object when the name is None
            # although we know its type, we still want to fuzz different field for it
            # so we flatten the object
            if ((isinstance(self.type, types.SchemaObject) and 
                self.arg_name is None) or
                isinstance(self.type, types.ObjectType)):
                fields = self.type.get_fields()
                required_fields = self.type.get_requires()
                for field, field_typ in fields.items():
                    value = None if self.value is None else self.value[field]
                    is_required = self.is_required and field in required_fields
                    p = Parameter(
                        self.method, field, self.func_name,
                        self.path + [field], is_required,
                        self.array_level, field_typ, value)
                    results += p.flatten_ad_hoc(skip_fields)
            elif isinstance(self.type, types.ArrayType):
                item_type = self.type.item
                value = None if self.value is None else self.value[0]
                array_level = None if self.array_level is None \
                    else self.array_level + 1
                p = Parameter(
                    self.method, defs.INDEX_ANY, self.func_name,
                    self.path + [defs.INDEX_ANY], self.is_required,
                    array_level, item_type, value
                )
                results += p.flatten_ad_hoc(skip_fields)
            elif isinstance(self.type, types.UnionType):
                items = self.type.items
                p = Parameter(
                    self.method, self.arg_name, self.func_name,
                    self.path, self.is_required, self.array_level,
                    items[0], self.value # TODO: is this sufficient?
                )
                results += p.flatten_ad_hoc(skip_fields)
            else:
                results.append(self)
        else:
            results.append(self)

        return results

    def flatten_ad_hoc_by_value(self, skip_fields):
        results = []

        if self.arg_name in skip_fields:
            return results

        if self.type is not None:
            # the arg itself is an ad-hoc object when the name is None
            # although we know its type, we still want to fuzz different field for it
            # so we flatten the object
            if ((isinstance(self.type, types.SchemaObject) and 
                self.arg_name is None) or
                isinstance(self.type, types.ObjectType)):
                fields = self.type.get_fields()
                for field in self.value:
                    value = self.value[field]
                    is_required = (
                        self.is_required and 
                        field in self.type.required_fields)
                    p = Parameter(
                        self.method, field, self.func_name,
                        self.path + [field], is_required,
                        self.array_level, fields[field], value)
                    results += p.flatten_ad_hoc_by_value(skip_fields)
            elif isinstance(self.type, types.ArrayType):
                if len(self.value) == 0:
                    results.append(self)
                else:
                    item_type = self.type.item
                    value = None if self.value is None else self.value[0]
                    array_level = None if self.array_level is None \
                        else self.array_level + 1
                    p = Parameter(
                        self.method, defs.INDEX_ANY, self.func_name,
                        self.path + [defs.INDEX_ANY], self.is_required,
                        array_level, item_type, value
                    )
                    results += p.flatten_ad_hoc_by_value(skip_fields)
            elif isinstance(self.type, types.UnionType):
                items = self.type.items
                p = Parameter(
                    self.method, self.arg_name, self.func_name,
                    self.path, self.is_required, self.array_level,
                    items[0], self.value # TODO: is this sufficient?
                )
                results += p.flatten_ad_hoc_by_value(skip_fields)
            else:
                results.append(self)
        else:
            results.append(self)

        return results

    def project_ad_hoc(self, analyzer):
        projections = []
        if isinstance(self.type, types.ObjectType):
            fields = self.type.object_fields
            for field, field_typ in fields.items():
                field_path = self.path + [field]
                p = Parameter(
                    self.method,         # method
                    field,      # arg name
                    self.func_name,  # func name
                    field_path, # path
                    True,       # is required
                    0,          # array level
                    field_typ,
                    None,
                )
                in_param = analyzer.set_type(self)
                out_param = analyzer.set_type(p)
                proj_name = f"projection({in_param.type}, {field})"
                proj_field = TraceEntry(
                    proj_name,
                    "",
                    None,
                    [in_param],
                    out_param
                )
                projections.append(proj_field)
                projections += p.project_ad_hoc(analyzer)
        elif isinstance(self.type, types.ArrayType):
            p = Parameter(
                self.method,
                self.arg_name, 
                self.func_name,
                self.path + [defs.INDEX_ANY],
                True,
                self.array_level + 1,
                self.type.item,
                None,
            )
            projections += p.project_ad_hoc(analyzer)
        elif isinstance(self.type, types.UnionType):
            for t in self.type.items:
                p = Parameter(
                    self.method,
                    self.arg_name,
                    self.func_name,
                    self.path,
                    True,
                    self.array_level,
                    t,
                    None,
                )
                projections += p.project_ad_hoc(analyzer)

        return projections

    def __eq__(self, other): 
        if not isinstance(other, Parameter):
            # don't attempt to compare against unrelated types
            return NotImplemented

        same_array_level = (
            (self.array_level is None and other.array_level is None) or
            (self.array_level is not None and other.array_level is not None)
        )

        return (self.arg_name == other.arg_name and
                self.func_name == other.func_name and
                self.method.upper() == other.method.upper() and
                same_array_level and
                self.path == other.path)

    def __str__(self):
        return self.arg_name + '_' + self.func_name + '_' + \
            self.method.upper() + '_' + '.'.join(self.path)

    def __repr__(self):
        return self.__str__()

    def __hash__(self):
        return hash((
            self.arg_name,
            self.func_name,
            self.method.upper(),
            tuple(self.path)
        ))

    @staticmethod
    def from_openapi(endpoint, method, arg_name, 
        type_def, is_required, array_level):
        # pass definition here and construct a type for it
        typ = types.construct_type(None, type_def)
        path = [] if arg_name is None else [arg_name]
        return Parameter(
            method, arg_name, endpoint,
            path, is_required, array_level, typ, None)

class TraceEntry:
    def __init__(self, endpoint, method, content_type, parameters, response):
        self.endpoint = endpoint
        self.method = method
        self.parameters = parameters
        self.response = response
        self.content_type = content_type

    def __str__(self):
        param_strs = map(str, self.parameters)
        return (self.method.upper() + " " + self.endpoint + "\n" +
                ",".join(param_strs) + "\n" + str(self.response))

    def __repr__(self):
        return self.__str__()

    def __eq__(self, other):
        if not isinstance(other, TraceEntry):
            return NotImplemented

        return (self.endpoint == other.endpoint and
            self.method == other.method and
            self.parameters == other.parameters and
            self.response == other.response)

    @staticmethod
    def from_openapi_params(doc, endpoint, method, entry_def):
        entry_params = []
        
        # read parameters
        parameters = entry_def.get(defs.DOC_PARAMS, {})
        content_type = defs.HEADER_FORM
        for p in parameters:
            name = p.get(defs.DOC_NAME)
            if name == defs.DOC_TOKEN:
                continue

            param = Parameter.from_openapi(
                endpoint, method, name,
                p.get(defs.DOC_SCHEMA),
                p.get(defs.DOC_REQUIRED, False), None)
            entry_params.append(param)

        # read request body
        try:
            request_params = entry_def.get(defs.DOC_REQUEST)
            if request_params is not None:
                request_body = request_params \
                    .get(defs.DOC_CONTENT) \
                    .get(defs.HEADER_FORM)
                content_type = defs.HEADER_FORM
                if request_body is None:
                    request_body = request_params \
                        .get(defs.DOC_CONTENT) \
                        .get(defs.HEADER_JSON)
                    content_type = defs.HEADER_JSON

                if request_body is not None:
                    schema = request_body.get(defs.DOC_SCHEMA)
                    ref_properties = schema.get(defs.DOC_REF)
                    if ref_properties is not None:
                        typ_name = ref_properties[len(consts.REF_PREFIX):]
                        schema = types.get_ref_type(doc, typ_name)

                    requires = schema.get(defs.DOC_REQUIRED, [])
                    properties = schema.get(defs.DOC_PROPERTIES)

                    if properties is not None:
                        for name, typ_def in properties.items():
                            if name == defs.DOC_TOKEN:
                                continue

                            param = Parameter.from_openapi(
                                endpoint, method, name, typ_def,
                                name in requires, None,
                            )
                            entry_params.append(param)
                    else:
                        raise Exception(
                            "Unhandled parameter case in", endpoint, method
                        )

        except Exception:
            print(endpoint, method)
            raise Exception
        
        return entry_params, content_type

    @staticmethod
    def from_openapi(doc, endpoint, method, entry_def):
        """read definition from openapi and generate several entries
        """
        entry_params, content_type = TraceEntry.from_openapi_params(
            doc, endpoint, method, entry_def)

        # read responses
        responses = entry_def.get(defs.DOC_RESPONSES)
        response_content = responses \
            .get(str(defs.CODE_OK)) \
            .get(defs.DOC_CONTENT)
        response_json = response_content.get(defs.HEADER_JSON)

        if response_json:
            response_schema = response_json.get(defs.DOC_SCHEMA)
        else:
            response_schema = response_content \
                .get(defs.HEADER_FORM) \
                .get(defs.DOC_SCHEMA)

        # response_name = make_response_name(endpoint, method)
        response_typ = types.construct_type(None, response_schema)
        entry_response = Parameter(
            method, "", endpoint, [], True, 
            int(response_schema.get(defs.DOC_TYPE) == defs.TYPE_ARRAY), 
            response_typ, None
        )

        return TraceEntry(
            endpoint, method, content_type, 
            entry_params, entry_response)

    def same_signature(self, other):
        if not isinstance(other, TraceEntry):
            return NotImplemented

        param_types = [str(param.type) for param in self.parameters]
        ret_type = str(self.response.type)

        other_types = [str(param.type) for param in other.parameters]
        other_ret = str(other.response.type)

        return (
            param_types == other_types and
            ret_type == other_ret
        )
