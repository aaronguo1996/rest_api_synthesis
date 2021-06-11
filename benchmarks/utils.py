import os
import pickle
import re

import consts
from analyzer import parser
from synthesizer.utils import make_entry_name
from analyzer.utils import path_to_name
from analyzer.entry import ErrorResponse

def prep_exp_dir(config):
    exp_name = config[consts.KEY_EXP_NAME]
    exp_dir = os.path.join("experiment_data/", exp_name)
    if not os.path.exists(exp_dir):
        os.makedirs(exp_dir)

    return exp_dir

def parse_entries(configuration, exp_dir, base_path, endpoints):
    trace_file = os.path.join(exp_dir, consts.FILE_TRACE)
    print(trace_file)
    if not os.path.exists(trace_file):
        print("Parsing OpenAPI document...")
        # entries = None
        log_parser = parser.LogParser(
            configuration[consts.KEY_LOG_FILE], 
            configuration[consts.KEY_HOSTNAME],
            base_path, endpoints)
        entries = log_parser.parse_entries(
            configuration[consts.KEY_ANALYSIS][consts.KEY_UNINTERESTING],
            configuration.get(consts.KEY_SKIP_FIELDS),
        )
        # if configuration[consts.KEY_DEBUG]:
        #     # write entries to log file
        #     logging.debug("========== Start Logging Parse Results ==========")
        #     for e in entries:
        #         logging.debug(e)

        with open(trace_file, 'wb') as f:
            pickle.dump(entries, f)
    else:
        with open(trace_file, 'rb') as f:
            entries = pickle.load(f)

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
    return sum(lst) / len(lst)

def index_entries(entries, skip_fields):
    index_result = {}
    for e in entries:
        if (isinstance(e.response, ErrorResponse) or
            e.response.value is None):
            continue

        ep = e.endpoint
        md = e.method.upper()
        fun = make_entry_name(ep, md)

        if fun not in index_result:
            index_result[fun] = {}

        all_params = []
        for param in e.parameters:
            params = param.flatten_ad_hoc_by_value()
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
        
        index_result[fun][param_names].append(e)

    return index_result

def pretty_none(v):
    if isinstance(v, float):
        return round(v, 2)
        
    return v or '-'