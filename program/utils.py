import collections

def find_expr(exprs, expr):
    for e, v in exprs:
        if e == expr:
            return v

    return None

def get_field_value(obj, field):
    if isinstance(obj, dict):
        return obj.get(field)
    elif isinstance(obj, list):
        return [get_field_value(x, field) for x in obj]
    else:
        return None

def flatten(l):
    for el in l:
        if isinstance(el, collections.Iterable) and not isinstance(el, (str, bytes)):
            yield from flatten(el)
        else:
            yield el