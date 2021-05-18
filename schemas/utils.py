def value_size(val):
    sz = 0
    if isinstance(val, dict):
        for v in val.values():
            sz += value_size(v)
    elif isinstance(val, list):
        for v in val:
            sz += value_size(v)
    else:
        sz = 1

    return sz

def get_object_def(obj, path):
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