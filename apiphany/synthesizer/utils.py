from collections import defaultdict
import consts
from openapi import defs

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

def make_partial_trans_name(object, field):
    return consts.PREFIX_PARTIAL + field + "_" + object

def is_syntactic(typ_name):
    return (
        typ_name == defs.TYPE_STRING or
        typ_name == defs.TYPE_NUM or
        typ_name == defs.TYPE_INT or
        typ_name == defs.TYPE_BOOL or
        typ_name == defs.TYPE_OBJECT
    )