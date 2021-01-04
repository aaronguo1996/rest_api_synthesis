import re

class Type:
    def __init__(self, name, obj):
        self.name = name
        self.type = obj

    def isTypeOf(self, obj):
        if isinstance(obj, dict):
            for k, v in obj.items():
                if k in self.type:
                    if not self.type.isTypeOf(v):
                        return False
                else:
                    # if the object contains fields not in the type definition
                    # it doesn't belong to this type
                    return False
        elif self.type["type"] == "string":
            pattern = self.type.get("pattern")
            if pattern:
                return re.match(pattern, obj)

        return True

    def isSupertypeOf(self, other):
        if isinstance(other, dict):
            for k, v in other.items():
                if k in self.type:
                    if not self.type.isSupertypeOf(v):
                        return False
                else:
                    return False

            return True
        else:
            return True