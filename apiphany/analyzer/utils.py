import re

from openapi import defs
from openapi.utils import blacklist
import consts

def get_representative(group):
    candidates = set()
    for param in group:
        if param.type is None:
            continue

        if (param.type.name is not None and
            param.type.name != defs.TYPE_STRING and
            param.type.name != defs.TYPE_INT and
            param.type.name != defs.TYPE_NUM and
            param.type.name != defs.TYPE_BOOL and
            param.type.name != defs.TYPE_OBJECT):
            candidates.add(param.type.name)

        candidates = candidates.union(param.type.aliases)

    candidates = [n for n in candidates if not blacklist(n)]
    if candidates:
        rep = min(candidates, key=lambda x: (x.count("."), len(x), x)) # we prefer names with fewer dots
        return rep
    else:
        return None

def name_to_path(name):
    fields = []
    field = ""
    for c in name:
        if c == '[':
            if field and not fields:
                fields.append(field)

            field = ""
        elif c == ']':
            if re.search(r"^\d+$", field) or field == "":
                field = defs.INDEX_ANY

            if field:
                fields.append(field)
        else:
            field += c
            field = field.strip()

    if c != ']' and field:
        fields.append(field)

    return fields

def path_to_name(path):
    if not path:
        return ""
        
    name = path[0]
    for field in path[1:]:
        if field == defs.INDEX_ANY:
            name += "[0]"
        else:
            name += f"[{field}]"

    return name

def same_type_name(typ1, typ2):
    return (
        typ1 is not None and 
        typ2 is not None and (
            (
                typ1.name is not None and 
                typ2.name is not None and 
                typ1.name == typ2.name
            ) or
            typ1.name in typ2.aliases or 
            typ2.name in typ1.aliases or 
            len(typ1.aliases.intersection(typ2.aliases)) != 0
        )
    )

def ignore_arg_name(skip_fields, arg_name):
    return (arg_name is not None and
        (arg_name in skip_fields or
        consts.CUSTOM_PREFIX == arg_name[:2]))

def make_response_name(endpoint, method):
    return f"{endpoint}_{method.upper()}_response"