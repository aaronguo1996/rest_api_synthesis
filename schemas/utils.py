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