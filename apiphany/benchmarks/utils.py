import os
import pickle
import re
import random
import math

import consts
from analyzer import parser
from synthesizer.utils import make_entry_name
from analyzer.utils import path_to_name
from analyzer.entry import ErrorResponse, TraceEntry
from analyzer.analyzer import LogAnalyzer

def prep_exp_dir(data_dir, exp_dir, config):
    api_name = config[consts.KEY_EXP_NAME]
    api_dir = os.path.join(data_dir, exp_dir, api_name)
    if not os.path.exists(api_dir):
        os.makedirs(api_dir)

    return api_dir

def update_type(skip_fields, entries, endpoints):
    for e in entries:
        entry_def = endpoints.get(e.endpoint).get(e.method.upper())
        if entry_def is None:
            raise Exception(f"{e.endpoint} {e.method.upper()} is not found")

        for param in e.parameters:
            if param.arg_name in skip_fields:
                continue

            for doc_param in entry_def.parameters:
                if doc_param.arg_name == param.arg_name:
                    match_param = doc_param
                    break

            param.type = match_param.type

def get_initial_witnesses(configuration, exp_dir, base_path, endpoints):
    trace_file = os.path.join(exp_dir, consts.FILE_TRACE)
    skip_fields = configuration.get(consts.KEY_SKIP_FIELDS)
    log_parser = parser.LogParser(
        configuration[consts.KEY_LOG_FILE], 
        configuration[consts.KEY_HOSTNAME],
        base_path, endpoints)
    entries = log_parser.parse_entries(
        configuration[consts.KEY_ANALYSIS][consts.KEY_UNINTERESTING],
        skip_fields,
    )

    return entries


def sanitize_traces(entries):
    sanitized_entries = []
    for entry in entries:
        if "projection" in entry.endpoint:
            continue

        sanitized_entries.append(entry) 

    return sanitized_entries

def parse_entries(configuration, exp_dir, base_path, endpoints):
    trace_file = os.path.join(exp_dir, consts.FILE_TRACE)
    skip_fields = configuration.get(consts.KEY_SKIP_FIELDS)
    initial_witness_only = configuration.get(consts.KEY_INITIAL_WITNESS_ONLY)
    if initial_witness_only or not os.path.exists(trace_file):
        print("Parsing OpenAPI document...")
        # entries = None
        log_parser = parser.LogParser(
            configuration[consts.KEY_LOG_FILE], 
            configuration[consts.KEY_HOSTNAME],
            base_path, endpoints)
        entries = log_parser.parse_entries(
            configuration[consts.KEY_ANALYSIS][consts.KEY_UNINTERESTING],
            skip_fields,
        )
        # if configuration[consts.KEY_DEBUG]:
        #     # write entries to log file
        #     logging.debug("========== Start Logging Parse Results ==========")
        #     for e in entries:
        #         logging.debug(e)

        if not initial_witness_only:
            with open(trace_file, 'wb') as f:
                pickle.dump(entries, f)
    else:
        with open(trace_file, 'rb') as f:
            entries = pickle.load(f)

        update_type(skip_fields, entries, endpoints)

    return entries

def get_solution_strs(solutions):
    return [r.pretty(0) for r in solutions]

def replace_variables(progstr):
    vnames = re.findall("x\d+", progstr)
    varnames = []
    for vname in vnames:
        if vname not in varnames:
            varnames.append(vname)

    for i, vname in enumerate(varnames):
        progstr = str.replace(progstr, vname, f"x{i}")

    progstr = re.sub("\s", "", progstr)
    progstr = re.sub("\n", "", progstr)
    return progstr

def compare_program_strings(progstr_a, progstr_b):
    return replace_variables(progstr_a) == replace_variables(progstr_b)

def avg(lst):
    if len(lst):
        return sum(lst) / len(lst)
    else:
        return None

def median(lst):
    lst = sorted(lst)
    if len(lst) % 2 == 0:
        return (lst[len(lst) // 2 - 1] + lst[len(lst) // 2]) / 2
    else:
        return lst[len(lst) // 2]

def get_obj_weight(obj):
    """
    weighs simply by calculating number of fields in object/list recursively
    """
    if isinstance(obj, list):
        total = 1
        for child in obj:
            total += get_obj_weight(child)
        return total
    elif isinstance(obj, dict):
        total = 1
        for _, child in obj.items():
            total += get_obj_weight(child)
        return total
    elif obj:
        return 1
    else:
        return 0

def index_entries(entries, skip_fields):
    index_result = {}
    for e in entries:
        if (isinstance(e.response, ErrorResponse) or
            not e.response.value):
            continue

        ep = e.endpoint
        md = e.method.upper()
        fun = make_entry_name(ep, md)

        if fun not in index_result:
            index_result[fun] = {}

        all_params = []
        for param in e.parameters:
            params = param.flatten_ad_hoc_by_value(skip_fields)
            all_params += params
        e.parameters = all_params

        param_values = {}
        for param in all_params:
            if param.arg_name not in skip_fields:
                name = path_to_name(param.path)
                param_values[name] = param.value

        param_names = tuple(sorted(list(param_values.keys())))

        if param_names not in index_result[fun]:
            index_result[fun][param_names] = []

        found = False
        for _, v, _ in index_result[fun][param_names]:
            if v == e.response.value:
                found = True

        if not found and e.response.value:
            weight = get_obj_weight(e.response.value)
            index_result[fun][param_names].append(
                (param_values, e.response.value, weight)
            )

        # if fun == "/v2/orders/batch-retrieve_POST":
        #     print(index_result[fun].keys())

    # for fun, fun_results in index_result.items():
    #     for param, param_results in fun_results.items():
    #         if len(param_results) > 10:
    #             index_result[fun][param] = param_results[-10:]
                
    return index_result

def pretty_none(v):
    if isinstance(v, float):
        if v < 0.05:
            return "$<$0.1"

        return round(v, 1)
        
    return v if v is not None else '-'

def get_petri_net_data(exp_dir):
    encoder_path = os.path.join(exp_dir, "encoder.txt")
    with open(encoder_path, "r") as f:
        numbers = []
        line = f.readline()
        while line:
            numbers.append(int(line) if "None" not in line else 0)
            line = f.readline()

    return numbers[0], numbers[1], numbers[2]
    
def within_expected_coverage(curr_coverage, target_coverage):
    return abs(curr_coverage - target_coverage) < 0.025

def to_syntactic_type(param):
    typ = param.type
    if typ is None:
        raise Exception("Parameter", param, "does not have type")

    param.type = typ.to_syntactic()
    return param

def create_entries(doc, config, ascription, infer_types=True):
    entries = {}

    endpoints = config.get(consts.KEY_ENDPOINTS)
    if not endpoints:
        endpoints = doc.keys()

    for endpoint, ep_def in doc.items():
        if endpoint not in endpoints:
            continue

        for _, method_def in ep_def.items():
            typed_entries = ascription.ascribe_type(method_def, infer_types)

            for entry in typed_entries:
                # store results
                entry_name = make_entry_name(entry.endpoint, entry.method)
                entries[entry_name] = entry

    return entries

def prune_by_coverage(paths, witnesses, coverage):
    methods = set()
    for ep, ep_def in paths.items():
        for md in ep_def.keys():
            methods.add((ep, md.upper()))

    covered = set()
    for w in witnesses:
        key = (w.endpoint, w.method.upper())
        if (key in methods and
            not isinstance(w.response, ErrorResponse) and
            w.response.value is not None):
            covered.add(key)

    print("Original coverage:", len(covered), "out of", len(methods), ", percentage:", len(covered) / len(methods))

    # coverage = len(covered) / len(methods) * coverage # relative coverage
    # if curr_coverage <= coverage or within_expected_coverage(curr_coverage, coverage):
    #     print("Warning: the provided coverage cannot be reached")
    #     return witnesses

    # drop a random subset of methods to reach the target coverage
    expected_covered_num = math.floor(coverage * len(covered)) # relative coverage
    sampled_covered = random.sample(list(covered), k=expected_covered_num)

    sampled_witnesses = []
    # counts = {}
    for w in witnesses:
        key = (w.endpoint, w.method.upper())
        if key in sampled_covered:
            sampled_witnesses.append(w)
    #         if key not in counts:
    #             counts[key] = []

    #         counts[key].append(w)

    # 
    # # control the witness size to reduce the memory usage
    # for k, ws in counts.items():
    #     if len(ws) > 10:
    #         sampled_witnesses += ws[-10:]
    #     else:
    #         sampled_witnesses += ws

    return sampled_witnesses
