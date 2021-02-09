from collections import defaultdict

def group_types(types):
    type_dict = defaultdict(int)
    for t in types:
        type_dict[t] += 1

    return type_dict

def group_params(params):
    types = [str(p.type) for p in params]
    return group_types(types)

def make_entry_name(endpoint, method):
    return endpoint + ":" + method.upper()