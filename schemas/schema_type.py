import re

from openapi import defs
from schemas.utils import value_size
from openapi.utils import blacklist

class SchemaType:
    doc_obj = {}

    def __init__(self, name, obj, parent = None):
        self.name = name
        self.schema = obj
        self.parent = parent
        self.is_object = True
        self.fields = []

    @staticmethod
    def to_python_type(typ):
        if typ == "string":
            return str
        elif typ == "none":
            return type(None)
        elif typ == "integer":
            return int
        elif typ == "boolean":
            return bool
        elif typ == "number":
            return (int, float)
        elif typ == "object":
            return dict
        elif isinstance(typ, list):
            meaningful_typs = list(filter(lambda x: x != "none", typ))
            return SchemaType.to_python_type(meaningful_typs[0])
        else:
            raise Exception(f"Unknown type {typ} from json to python")

    @staticmethod
    def is_array_type(expected_type):
        typ = expected_type.get("properties", expected_type)
        if "items" in typ and typ.get("type", None) == "array":
            return typ
        else:
            return None

    def of_array_type(self, obj, expected_type):
        array_type = self.is_array_type(expected_type)
        if array_type:
            # print("*******checking array type")
            # if the field has type array of items
            if not isinstance(obj, list):
                return None, -1

            item_schema = array_type.get(defs.DOC_ITEMS)
            if item_schema is not None:
                field_type = SchemaType(self.name, item_schema)
            else:
                raise Exception(f"Invalid array type definition for {array_type}")

            score = 1
            for o in obj:
                _, field_score = field_type.is_type_of(o)
                if field_score < 0:
                    return None, -1
                else:
                    score += field_score

            return field_type, score

        return None, -1

    @staticmethod
    def is_union_type(expected_type):
        return expected_type.get("oneOf") or expected_type.get("anyOf")

    def of_union_type(self, obj, expected_type):
        union_type = self.is_union_type(expected_type)
        if union_type is not None:
            # print("=====checking union type")
            for i in range(len(union_type)):
                t = union_type[i]
                # print(t)
                # TODO: shall we have different names for each type in the union type
                field_type = SchemaType(self.name, t)
                # if the field matches any of the union type
                _, field_score = field_type.is_type_of(obj)
                if field_score >= 0:
                    return field_type, field_score

        # none of match, returns false
        return None, -1

    def of_regex_type(self, obj, expected_type):
        if isinstance(obj, str) and expected_type.get("type") == "string":
            pattern = expected_type.get("pattern")
            enum = expected_type.get("enum")
            # print(f"checking string {obj} against pattern {pattern}")
            if ((pattern and re.search(pattern, obj)) or
                (enum and obj in enum) or
                (pattern is None and enum is None)):
                return self, 1

        return None, -1

    def is_type_of(self, obj):
        """[summary]

        Args:
            obj ([type]): [description]

        Returns:
            score: number of matched fields, find the best fit
        """
        try:
            # print(f"checking {obj} against {self.schema}")
            if not obj:
                return self, 0

            self.get_ref_type()
            if SchemaType.is_array_type(self.schema):
                return self.of_array_type(obj, self.schema)

            if SchemaType.is_union_type(self.schema):
                # print("checking union type")
                return self.of_union_type(obj, self.schema)

            if isinstance(self.schema, dict) and defs.DOC_PROPERTIES in self.schema:
                # print(f"checking {obj} against {self.schema}")
                score = 0
                if not isinstance(obj, dict):
                    return None, -1

                for k, v in obj.items():
                    # if k == "latest":
                    #     print(self.name, k, v)
                    types = self.schema.get(defs.DOC_PROPERTIES)
                    if not types: # if no properties is given, assume anything matches
                        continue

                    if k in types:
                        # print(f"{k} is in the type definition, has type {types[k]}")
                        field_type = SchemaType(k, types[k])
                        _, field_score = field_type.is_type_of(v)
                        if field_score < 0:
                            # if 'aggregate_usage' in obj.keys():
                            #     print("checking fails with field", k, "in", obj, "with type", self.name)
                            return None, -1
                        else:
                            # print("checking object succeeds")
                            if field_type.fields:
                                self.fields = [[k].extend(f) for f in field_type.fields]
                            else:
                                self.fields = [[k]]

                            score += field_score + 1
                    else:
                        # print(f"{k} is not in the type definition")
                        # if the object contains fields not in the type definition
                        # it doesn't belong to this type
                        # return None, -1
                        # TODO: should we allow additional fields? I guess it is okay
                        pass
                # if all checks
                return self, score
            else:
                self.is_object = False
                if isinstance(obj, str):
                    return self.of_regex_type(obj, self.schema)
                else:

                    typ = self.schema.get("type")
                    if typ:
                        py_typ = SchemaType.to_python_type(typ)
                        if py_typ is dict:
                            return self, value_size(obj)
                        elif isinstance(obj, py_typ):
                            return self, 1
                        else:
                            # print("checking fails for obj", obj, "with type",)
                            return self, -1
                    else:
                        return None, -1
        except Exception as e:
            print(e)
            print("Failed to check type for", obj, "against", self.schema)
            return None, -1

    @classmethod
    def get_object_def(cls, path):
        # decode the path into list of field names
        obj = cls.doc_obj

        fields = path.split('/')
        if fields[0] != "#":
            raise Exception(f"Resolution of non-local reference {path} is not supported.")

        for f in fields[1:]:
            if f[0] == '[' and f[-1] == ']':
                obj = obj[f[1:-1]]
            else:
                obj = obj.get(f, None)

            if not obj:
                raise Exception(f"Cannot find the field {f} in the given object.")

        return obj

    def get_ref_type(self):
        if "$ref" in self.schema:
            ref_path = self.schema["$ref"]
            self.schema = self.get_object_def(ref_path)

    def get_field_schema(self, k):
        self.get_ref_type()
        if k in self.schema:
            return self.schema.get(k)
        elif defs.DOC_ONEOF in self.schema or defs.DOC_ANYOF in self.schema:
            oneofs = self.schema.get(defs.DOC_ONEOF, [])
            anyofs = self.schema.get(defs.DOC_ANYOF, [])
            for sch in oneofs + anyofs:
                typ = SchemaType(self.name, sch)
                field_sch = typ.get_field_schema(k)
                if field_sch is not None:
                    return field_sch
        elif defs.DOC_PROPERTIES in self.schema:
            t = self.schema.get(defs.DOC_PROPERTIES)
            return t.get(k)
        # elif (defs.DOC_ITEMS in self.schema and 
        #     self.schema.get(defs.DOC_TYPE) == "array"):
        #     sch = self.schema.get(defs.DOC_ITEMS)
        #     typ = SchemaType(self.name, sch)
        #     return typ.get_field_schema(k)

        return None

    @staticmethod
    def infer_type_for(path_to_defs, skip_fields, value):
        # print(f"Try to find object types from doc for {value}")
        obj_defs = SchemaType.get_object_def(path_to_defs)
        obj_candidates = []
        for obj_name, obj in obj_defs.items():
            # skip added helper types
            if obj_name in skip_fields or blacklist(obj_name):
                continue

            obj_type = SchemaType(obj_name, obj)
            # TODO: do we want to use the returned obj_type? there is a difference for union types
            obj_type, obj_score = obj_type.is_type_of(value)
            if obj_score > 0:
                # if a candidate match only a small number of fields, do not add
                sz = value_size(value)
                if obj_score >= sz * 0.6:
                    # print("find object type", obj_name, "with score", obj_score)
                    obj_candidates.append((obj_type, obj_score))

        # return the one with the greatest score
        rank = lambda x: (x[1], int(not re.search("ref_\d+", x[0].name)))
        obj_candidates = sorted(obj_candidates, key=rank)
        if obj_candidates:
            # print("choose", obj_candidates[-1][0])
            # TODO: add the type partitioning here or after this returns, record the partitions somewhere
            return obj_candidates[-1][0]
        else:
            # print("choose nothing")
            return None

    def get_oldest_parent(self):
        if self.parent is not None and "unknown_obj" not in self.parent.name:
            return self.parent.get_oldest_parent()
        else:
            return self

    def __str__(self):
        return self.name

    def __repr__(self):
        return self.name
