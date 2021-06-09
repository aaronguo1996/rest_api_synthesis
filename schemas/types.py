import re

from openapi import defs
import schemas.utils as utils
from openapi.utils import blacklist
import consts

class BaseType:
    object_lib = {}

    def __init__(self, name, parent):
        self.name = name
        self.parent = parent
        self.aliases = set()

    def __str__(self):
        return self.name

    def __repr__(self):
        return self.__str__()

    @staticmethod
    def to_python_type(typ):
        if typ == defs.TYPE_STRING:
            return str
        elif typ == defs.TYPE_NONE:
            return type(None)
        elif typ == defs.TYPE_INT:
            return int
        elif typ == defs.TYPE_BOOL:
            return bool
        elif typ == defs.TYPE_NUM:
            return (int, float)
        elif typ == defs.TYPE_OBJECT:
            return dict
        elif isinstance(typ, list):
            meaningful_typs = list(filter(lambda x: x != defs.TYPE_NONE, typ))
            return BaseType.to_python_type(meaningful_typs[0])
        else:
            raise Exception(f"Unknown type {typ} from json to python")

    def is_type_of(self, obj):
        py_typ = BaseType.to_python_type(self.name)
        if isinstance(obj, py_typ):
            return self, 1
        else:
            return None, -1

    def ignore_array(self):
        return self

class PrimInt(BaseType):
    def __init__(self, name=defs.TYPE_INT):
        name = defs.TYPE_INT if name is None else name
        super().__init__(name, None)

class PrimBool(BaseType):
    def __init__(self, name=defs.TYPE_BOOL):
        name = defs.TYPE_BOOL if name is None else name
        super().__init__(name, None)

class PrimNum(BaseType):
    def __init__(self, name=defs.TYPE_NUM):
        name = defs.TYPE_NUM if name is None else name
        super().__init__(name, None)

class PrimString(BaseType):
    def __init__(self, name=defs.TYPE_STRING, pattern=None):
        name = defs.TYPE_STRING if name is None else name
        super().__init__(name, None)
        self._pattern = pattern

    def is_type_of(self, obj):
        if isinstance(obj, str):
            if (self._pattern is not None and
                re.search(self._pattern, obj)):
                return self, 1
            elif self._pattern is None:
                return self, 0.5

        return None, -1

class PrimEnum(BaseType):
    def __init__(self, name=defs.TYPE_STRING, enums=[]):
        name = defs.TYPE_STRING if name is None else name
        super().__init__(name, None)
        self.enums = enums

    def is_type_of(self, obj):
        if isinstance(obj, str) and obj in self.enums:
            return self, 1

        return None, -1

class SchemaObject(BaseType):
    def __init__(self, name, parent=None):
        super().__init__(name, parent)

    def is_type_of(self, obj):
        # get the object definition from the library
        schema = BaseType.object_lib.get(self.name)
        if schema is None:
            raise Exception("Unknown definition for", self.name)

        return schema.is_type_of(obj)

    def get_object_field(self, field):
        schema = BaseType.object_lib.get(self.name)
        # print("SchemaObject: get_object_field from", self.name, "field", field, "type", type(schema))
        if schema is None:
            raise Exception("Unknown object definition", self.name)

        return schema.get_object_field(field)

    def get_fields(self):
        schema = BaseType.object_lib.get(self.name)
        if schema is None:
            raise Exception("Unknown object definition", self.name)

        return schema.get_fields()
    
class ObjectType(BaseType):
    """Ad-hoc objects

    """
    def __init__(self, name, fields, required_fields=[], parent=None):
        super().__init__(name, parent)
        self.object_fields = fields
        self.required_fields = required_fields
        self.fields = []

    def __str__(self):
        return str(self.object_fields)

    @staticmethod
    def is_schema_type(expected_type):
        typ = expected_type.get(defs.DOC_PROPERTIES)
        if typ is not None:
            return typ
        else:
            return None

    def _is_object_type(self, obj):
        score = 0
        if not isinstance(obj, dict):
            return None, -1

        for k, v in obj.items():
            if not self.object_fields: # if no properties is given, assume anything matches
                continue

            if k in self.object_fields:
                field_type = self.object_fields[k]
                _, field_score = field_type.is_type_of(v)
                if field_score < 0:
                    return None, -1
                else:
                    if field_type.fields:
                        self.fields = [[k].extend(f) for f in field_type.fields]
                    else:
                        self.fields = [[k]]

                    score += field_score + 1
            else:
                # TODO: should we allow additional fields? I guess it is okay
                pass
        # if all checks
        return self, score

    def is_type_of(self, obj):
        if not obj:
            return self, 0

        if isinstance(obj, dict):
            return self._is_object_type(obj)
        else:
            return None, -1

    def get_object_field(self, field):
        # print("get_object_field from", self.name, "field name", field, "with fields", self.object_fields.keys())
        field_type = self.object_fields.get(field)
        if field_type is not None and self.name is not None:
            field_type.aliases.add(f"{self.name}.{field}")

        return field_type, (field in self.required_fields)

    def get_fields(self):
        return self.object_fields

class ArrayType(BaseType):
    def __init__(self, name, item_typ, parent=None):
        super().__init__(name, parent)
        self.item = item_typ

    def __str__(self):
        return f"[{self.item.name}]"

    @staticmethod
    def is_array_type(expected_type):
        typ = expected_type.get(defs.DOC_PROPERTIES, expected_type)
        if (defs.DOC_ITEMS in typ and
            typ.get(defs.DOC_TYPE, None) == defs.TYPE_ARRAY):
            return typ
        else:
            return None

    def _of_array_type(self, obj):
        # if the field has type array of items
        if not isinstance(obj, list):
            return None, -1

        score = 1
        for o in obj:
            _, field_score = self.item.is_type_of(o)
            if field_score < 0:
                return None, -1
            else:
                score += field_score

        return self, score

    def is_type_of(self, obj):
        return self._of_array_type(obj)

    def get_schema_type(self, k):
        return None

    def get_item(self):
        return self.item

    def ignore_array(self):
        return self.item.ignore_array()

class UnionType(BaseType):
    def __init__(self, name, items, parent=None):
        super().__init__(name, parent)
        self.items = items
        for item in self.items:
            self.aliases.add(str(item))

    def __str__(self):
        if self.name is not None:
            return self.name
        else:
            return str(self.items[0])

    @staticmethod
    def is_union_type(expected_type):
        return (
            expected_type.get(defs.DOC_ONEOF) or
            expected_type.get(defs.DOC_ANYOF) or
            expected_type.get(defs.DOC_ALLOF)
        )

    def _of_union_type(self, obj):
        for t in self.items:
            # if the field matches any of the union type
            _, field_score = t.is_type_of(obj)
            if field_score >= 0:
                return t, field_score

    def is_type_of(self, obj):
        return self._of_union_type(obj)

    def get_object_field(self, field):
        for t in self.items:
            if (isinstance(t, UnionType) or
                isinstance(t, ObjectType) or
                isinstance(t, SchemaObject)):
                field_type, is_required = t.get_object_field(field)
                if field_type is not None:
                    if self.name is not None:
                        field_type.aliases.add(f"{self.name}.{field}")

                    return field_type, is_required

        return None, False

    def get_item(self):
        for t in self.items:
            if isinstance(t, UnionType) or isinstance(t, ArrayType):
                item_type = t.get_item()
                if item_type is not None:
                    return item_type

        raise Exception("No item type found")

    def ignore_array(self):
        items = []
        for t in self.items:
            items.append(t.ignore_array())

        return UnionType(self.name, items)

def construct_prim_type(name, schema):
    typ = schema.get(defs.DOC_TYPE)
    ref = schema.get(defs.DOC_REF)
    if ref is not None:
        obj_name = ref[len(consts.REF_PREFIX):]
        return SchemaObject(obj_name)
    elif typ == defs.TYPE_INT:
        return PrimInt(name=name)
    elif typ == defs.TYPE_BOOL:
        return PrimBool(name=name)
    elif typ == defs.TYPE_STRING:
        if defs.DOC_ENUM in schema:
            enums = schema.get(defs.DOC_ENUM)
            return PrimEnum(name=name, enums=enums)

        pattern = schema.get(defs.DOC_PATTERN)
        return PrimString(name=name, pattern=pattern)
    elif typ == defs.TYPE_NUM:
        return PrimNum(name=name)
    elif typ == defs.TYPE_OBJECT:
        return ObjectType(None, {})
    else:
        raise Exception("Unknown primitive type", schema)

def construct_type(name, schema):
    ret_type = None

    array_schema = ArrayType.is_array_type(schema)
    if array_schema is not None:
        item_schema = array_schema.get(defs.DOC_ITEMS)
        item_type = construct_type(name, item_schema)
        ret_type = ArrayType(name, item_type)

    if ret_type is None:
        union_schema = UnionType.is_union_type(schema)
        if union_schema is not None:
            item_types = []
            ret_type = UnionType(name, item_types)
            for item_schema in union_schema:
                item_type = construct_type(name, item_schema)
                item_types.append(item_type)

    if ret_type is None:
        object_schema = ObjectType.is_schema_type(schema)
        required_fields = schema.get(defs.DOC_REQUIRED, [])
        if object_schema is not None:
            fields = {}
            for k, v in object_schema.items():
                field_name = None if name is None else f"{name}.{k}"
                field_type = construct_type(field_name, v)
                fields[k] = field_type

            ret_type = ObjectType(name, fields, required_fields)
        else:
            ret_type = construct_prim_type(name, schema)

    return ret_type

def infer_type_for(path_to_defs, skip_fields, value):
    # print(f"Try to find object types from doc for {value}")
    obj_defs = utils.get_object_def(BaseType.doc_obj, path_to_defs)
    obj_candidates = []
    for obj_name, obj in obj_defs.items():
        # skip added helper types
        if obj_name in skip_fields or blacklist(obj_name):
            continue

        obj_type = construct_type(obj_name, obj)
        obj_type, obj_score = obj_type.is_type_of(value)
        if obj_score > 0:
            # if a candidate match only a small number of fields, do not add
            sz = utils.value_size(value)
            if obj_score >= sz * consts.OBJ_MATCH_THRESHOLD:
                obj_candidates.append((obj_type, obj_score))

    # return the one with the greatest score
    obj_candidates = sorted(obj_candidates, key=lambda x: x[1])
    if obj_candidates:
        return obj_candidates[-1][0]
    else:
        return None

def get_ref_type(doc, name):
    schemas = doc.get(defs.DOC_COMPONENTS).get(defs.DOC_SCHEMAS)
    return schemas.get(name)