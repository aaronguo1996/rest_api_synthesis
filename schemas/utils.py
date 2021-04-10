def value_size(val):
    if isinstance(val, dict):
        sz = 0
        for v in val.values():
            sz += value_size(v)

        return sz
    else:
        return 1