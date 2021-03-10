# definition of types
import re
from openapi import defs

def type_partition(value, typ):
    schema = typ.schema
    

class SchemaType:
    doc_obj = {}
    
    def __init__(self, name, obj, parent = None):
        self.name = name
        self.schema = obj
        self.parent = parent

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

            return expected_type, score
        
        return None, -1

    @staticmethod
    def is_union_type(expected_type):
        return expected_type.get("oneOf")
        
    def of_union_type(self, obj, expected_type):
        union_type = self.is_union_type(expected_type)
        if union_type:
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
            # print(f"checking string {obj} against pattern {pattern}")
            if not pattern:
                return self, 0
            elif re.search(pattern, obj):
                return self, 1
    
        # print(f"checking {obj} for pattern")
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
            # print("Does this match:", obj, self.schema)
            if obj is None:
                return self, 0

            expected_type = self.get_ref_type()
            if SchemaType.is_array_type(expected_type):
                return self.of_array_type(obj, expected_type)

            if SchemaType.is_union_type(expected_type):
                # print("checking union type")
                return self.of_union_type(obj, expected_type)

            if isinstance(self.schema, dict) and defs.DOC_PROPERTIES in self.schema:
                # print(f"checking {obj} against {self.schema}")
                score = 0
                if not isinstance(obj, dict):
                    return None, -1
                    
                for k, v in obj.items():
                    # if k == "latest":
                    #     print(self.name, k, v)
                    types = expected_type.get(defs.DOC_PROPERTIES)
                    if not types: # if no properties is given, assume anything matches
                        continue

                    if k in types:
                        # print(f"{k} is in the type definition, has type {types[k]}")
                        field_type = SchemaType(k, types[k])
                        # if k == "latest":
                        #     print(types[k])
                        _, field_score = field_type.is_type_of(v)
                        if field_score < 0:
                            # if k == "latest":
                            #     print(f"{k} type check fails")
                            return None, -1
                        else:
                            # if k == "latest":
                            #     print(f"get {field_score} for {k}")
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
                if isinstance(obj, str):
                    return self.of_regex_type(obj, expected_type)
                else:
                    typ = expected_type.get("type")
                    if typ:
                        py_typ = SchemaType.to_python_type(typ)
                        # print(py_typ)
                        # print(obj)
                        if py_typ == dict:
                            return self, 0
                        else:
                            return self, int(isinstance(obj, py_typ)) or -1
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

        if obj.get("type", None) == "object":
            return obj.get("properties", None)
        else:
            return obj

    def get_ref_type(self):
        if "$ref" in self.schema:
            ref_path = self.schema["$ref"]
            return self.get_object_def(ref_path)
        else:
            return self.schema

    def get_field_schema(self, k):
        if k in self.schema:
            return self.schema.get(k)
        elif defs.DOC_PROPERTIES in self.schema:
            t = self.schema.get(defs.DOC_PROPERTIES)
            if k in t:
                return t.get(k)
            else:
                pass
                # print(f"Cannot find field {k} in type {self.schema}")
        
        return None

    @staticmethod
    def infer_type_for(path_to_defs, skip_fields, value):
        # print(f"Try to find object types from doc for {value}")
        obj_defs = SchemaType.get_object_def(path_to_defs)
        obj_candidates = []
        for obj_name, obj in obj_defs.items():
            # skip added helper types
            if obj_name in skip_fields or re.search("ref_\d+", obj_name):
                continue

            obj_type = SchemaType(obj_name, obj)
            # TODO: do we want to use the returned obj_type? there is a difference for union types
            obj_type, obj_score = obj_type.is_type_of(value)
            if obj_score > 0:
                # self.type = obj_type
                # print("find object type", obj_name, "with score", obj_score)
                # break
                obj_candidates.append((obj_type, obj_score))

        # return the one with the greatest score
        rank = lambda x: (x[1], int(not re.search("ref_\d+", x[0].name)))
        obj_candidates = sorted(obj_candidates, key=rank)
        if obj_candidates:
            # print("choose", obj_candidates[-1][0])
            # TODO: add the type partitioning here or after this returns, record the partitions somewhere
            type_partition(value, obj_candidates[-1][0].schema)
            return obj_candidates[-1][0]
        else:
            return None

    def get_oldest_parent(self):
        if self.parent:
            return self.parent.get_oldest_parent()
        else:
            return self

    def __str__(self):
        return self.name

    def __repr__(self):
        return self.name