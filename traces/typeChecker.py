import re

class Type:
    doc_obj = {}
    
    def __init__(self, name, obj):
        self.name = name
        self.schema = obj

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
            return float
        elif typ == "object":
            return dict
        elif isinstance(typ, list):
            meaningful_typs = list(filter(lambda x: x != "none", typ))
            return Type.to_python_type(meaningful_typs[0])
        else:
            raise Exception(f"Unknown type {typ} from json to python")

    def is_array_type(self, expected_type):
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
                return False

            field_type = Type(self.name, array_type["items"]["properties"])
            for o in obj:
                if not field_type.is_type_of(o):
                    return False

            return True
        
        return False

    def is_union_type(self, expected_type):
        typ = expected_type.get("properties", expected_type)
        if "items" in expected_type and "type" not in expected_type:
            return typ
        else:
            return None

    def of_union_type(self, obj, expected_type):
        union_type = self.is_union_type(expected_type)
        if union_type:
            # print("=====checking union type")
            for i in range(len(expected_type["items"])):
                t = expected_type["items"][i]
                field_type = Type(self.name + "_" + str(i), t)
                # if the field matches any of the union type
                if field_type.is_type_of(obj):
                    return True

        # none of match, returns false
        return False

    def of_regex_type(self, obj, expected_type):
        if isinstance(obj, str) and expected_type.get("type", None) == "string":
            pattern = expected_type.get("pattern", None)
            if pattern:
                return re.search(pattern, obj)
            else:
                return True
                
        return False

    def is_type_of(self, obj):
        try:
            # print("Does this match:", obj, self.schema)
            expected_type = self.get_ref_type()
            if self.is_array_type(expected_type):
                return self.of_array_type(obj, expected_type)

            if self.is_union_type(expected_type):
                return self.of_union_type(obj, expected_type)

            if isinstance(self.schema, dict):
                if not isinstance(obj, dict):
                    return False
                    
                for k, v in obj.items():
                    types = expected_type.get("properties", {})
                    if k in types:
                        field_type = Type(k, types[k])
                        if not field_type.is_type_of(v):
                            return False
                    else:
                        # if the object contains fields not in the type definition
                        # it doesn't belong to this type
                        return False
                # if all checks
                return True
            elif self.of_regex_type(obj, expected_type):
                return True
            else:
                typ = expected_type.get("type", None)
                if typ:
                    py_typ = Type.to_python_type(typ)
                    return isinstance(obj, py_typ)
                else:
                    return False
        except Exception as e:
            print(e)
            print("Failed to check type for", obj, "against", self.schema)

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