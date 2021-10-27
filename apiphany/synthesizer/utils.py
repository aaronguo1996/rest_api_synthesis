from collections import defaultdict
import consts

def group_types(types):
    type_dict = defaultdict(int)
    for t in types:
        type_dict[t] += 1

    return type_dict

def group_params(params):
    types = [str(p.type.ignore_array()) for p in params]
    return group_types(types)

def make_entry_name(endpoint, method):
    return endpoint + "_" + method.upper()

def make_type_transition_name(from_type, to_type):
    return consts.PREFIX_CONVERT + from_type + "_" + to_type