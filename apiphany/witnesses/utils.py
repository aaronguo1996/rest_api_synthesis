from apiphany.openapi import defs

def split_by(p, lst):
    good = [x for x in lst if p(x)]
    bad = [x for x in lst if not p(x)]
    return good, bad

def create_object(path, val):
    # print("creating object from path", path, "with value", val)
    obj = val
    for field in reversed(path):
        if field == defs.INDEX_ANY:
            obj = [obj]
        else:
            obj = {field: obj}

    return obj

def has_overlapping(obj1, obj2):
    for k in obj1:
        if k in obj2:
            return True

    return False

def insert_nest_object(in_obj, obj):
    if isinstance(obj, list) and isinstance(in_obj, list):
        if (len(in_obj) == 1 and isinstance(in_obj[0], dict) and
            len(obj) == 1 and isinstance(obj[0], dict) and
            not has_overlapping(in_obj[0], obj[0])):
            return [insert_nest_object(in_obj[0], obj[0])]
        else:
            return in_obj + obj
    elif isinstance(in_obj, dict) and isinstance(obj, dict):
        for field in obj:
            if field in in_obj:
                in_obj[field] = insert_nest_object(in_obj[field], obj[field])
            else:
                in_obj[field] = obj[field]

        return in_obj
    else:
        raise Exception(f"unmatched type for {obj} and {in_obj}")

def add_as_object(in_obj, path, val):
    obj = create_object(path, val)
    return insert_nest_object(in_obj, obj)

def filter_optional(params):
    req_params = []
    opt_params = []
    for param_obj in params:
        if param_obj.is_required:
            req_params.append(param_obj)
        else:
            opt_params.append(param_obj)
    return req_params, opt_params

def num_optional_params(entry):
    params = entry.parameters
    _, opt_params = filter_optional(params)
    return len(opt_params)