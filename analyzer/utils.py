import re

from openapi import defs

def get_representative(group):
    rep = ""
    rep_type = None
    for param in group:
        if param.type is None or param.type.name is None:
            continue

        path_str = str(param.type)
        
        if not rep or len(rep) >= len(path_str):
            if len(rep) == len(path_str) and path_str >= rep:
                continue

            rep = path_str
            rep_type = param.type

    return rep, rep_type

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
    name = path[0]
    for field in path[1:]:
        if field == defs.INDEX_ANY:
            name += "[0]"
        else:
            name += f"[{field}]"

    return name