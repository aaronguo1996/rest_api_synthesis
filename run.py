#!/usr/bin/python3.8

import argparse
import pickle
import os
import json
import logging
import random
from re import M
from synthesizer.constructor import Constructor
from graphviz import Digraph

# analyze traces
from analyzer import analyzer, dynamic, parser
from openapi import defs
from openapi.utils import read_doc, get_schema_forest
import consts
from synthesizer.synthesizer import Synthesizer
from synthesizer.filtering import run_filter
from synthesizer.parallel import spawn_encoders
from globs import init_synthesizer, get_solution_strs
from witnesses.engine import WitnessGenerator
from synthesizer.utils import make_entry_name
from analyzer.ascription import Ascription
from openapi.parser import OpenAPIParser

# test imports
from tests.run_test import run_test

# definitions of constants
DEFAULT_DEBUG_OUTPUT = 'debug.log' 

def build_cmd_parser():
    '''
        All arguments
    '''
    parser = argparse.ArgumentParser()
    parser.add_argument("config_file", nargs='?',
        help="Path to the configuration file")
    parser.add_argument("--test", action="store_true",
        help="Run unit tests")
    parser.add_argument("--dynamic", action="store_true",
        help="Run dynamic analysis")
    parser.add_argument("--filtering", action="store_true",
        help="Filter or rank results from previous run")
    parser.add_argument("--synthesis", action="store_true",
        help="Run synthesis algorithm in single process mode")
    parser.add_argument("--parallel", action="store_true",
        help="Run synthesis algorithm in parallel mode")
    parser.add_argument("--timeout", type=int,
        help="Timeout limit for synthesis to run")
    parser.add_argument("--witness", action="store_true",
        help="Generate witnesses by configuration")
    return parser

def prep_exp_dir(config):
    exp_name = config[consts.KEY_EXP_NAME]
    exp_dir = os.path.join("experiment_data/", exp_name)
    if not os.path.exists(exp_dir):
        os.makedirs(exp_dir)

    return exp_dir

def parse_entries(configuration, exp_dir, base_path, endpoints):
    trace_file = os.path.join(exp_dir, consts.FILE_TRACE)
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
        if configuration[consts.KEY_DEBUG]:
            # write entries to log file
            logging.debug("========== Start Logging Parse Results ==========")
            for e in entries:
                logging.debug(e)

        with open(trace_file, 'wb') as f:
            pickle.dump(entries, f)
    else:
        with open(trace_file, 'rb') as f:
            entries = pickle.load(f)

    return entries

def run_dynamic(configuration, entries, endpoint, limit=500):
    analysis = dynamic.DynamicAnalysis(
        entries,
        configuration.get(consts.KEY_SKIP_FIELDS)
    )
    seqs = analysis.get_sequences(endpoint=endpoint, limit=limit)
    print(seqs)

def create_entries(doc, config, ascription):
    entries = {}

    paths = doc.get(defs.DOC_PATHS)
    endpoints = config.get(consts.KEY_ENDPOINTS)
    if not endpoints:
        endpoints = paths.keys()

    for endpoint, ep_def in paths.items():
        if endpoint not in endpoints:
            continue

        for method, method_def in ep_def.items():
            typed_entries = ascription.ascribe_type(endpoint, method, method_def)

            for entry in typed_entries:
                # store results
                entry_name = make_entry_name(entry.endpoint, entry.method)
                if endpoint == "/users.lookupByEmail":
                    print("*******", [(p.arg_name, p.path, p.is_required, p.type) for p in entry.parameters])
                    p = entry.response
                    print("*******", (p.arg_name, p.path, p.is_required, p.type))
                entries[entry_name] = entry

    return entries

def generate_witnesses(configuration, doc, exp_dir, entries, endpoints):
    enable_debug = configuration.get(consts.KEY_DEBUG)

    print("Analyzing provided log...")
    log_analyzer = analyzer.LogAnalyzer()
    prefilter = configuration.get(consts.KEY_SYNTHESIS) \
                            .get(consts.KEY_SYN_PREFILTER)
    skip_fields = configuration.get(consts.KEY_SKIP_FIELDS)
    log_analyzer.analyze(
        doc.get(defs.DOC_PATHS),
        entries, 
        skip_fields,
        configuration.get(consts.KEY_BLACKLIST),
        prefilter=prefilter)

    groups = log_analyzer.analysis_result()
    if enable_debug:
        logging.debug("========== Start Logging Analyze Results ==========")
        for g in groups:
            logging.debug(g)

    ascription = Ascription(log_analyzer, skip_fields)
    entries = create_entries(doc, configuration, ascription)

    print("Getting more traces...")
    engine = WitnessGenerator(
        doc, entries, log_analyzer,
        configuration[consts.KEY_WITNESS][consts.KEY_TOKEN],
        configuration[consts.KEY_WITNESS][consts.KEY_VALUE_DICT],
        configuration[consts.KEY_WITNESS][consts.KEY_ANNOTATION],
        exp_dir,
        configuration[consts.KEY_WITNESS][consts.KEY_GEN_DEPTH],
        configuration[consts.KEY_PATH_TO_DEFS],
        configuration.get(consts.KEY_SKIP_FIELDS),
        configuration[consts.KEY_WITNESS][consts.KEY_PLOT_EVERY],
    )

    if configuration[consts.KEY_ANALYSIS][consts.KEY_PLOT_GRAPH]:
        engine.to_graph(endpoints, "dependencies_0")

    engine.saturate_all(
        endpoints, configuration[consts.KEY_WITNESS][consts.KEY_ITERATIONS],
        configuration[consts.KEY_WITNESS][consts.KEY_TIMEOUT])

    print("Writing typed entries to file...")
    constructor = Constructor(doc, log_analyzer)
    projs_and_filters = constructor.construct_graph()
    entries.update(projs_and_filters)
    with open(os.path.join(exp_dir, consts.FILE_ENTRIES), "wb") as f:
        pickle.dump(entries, f)

    print("Writing graph to file...")
    with open(os.path.join(exp_dir, consts.FILE_GRAPH), "wb") as f:
        pickle.dump(log_analyzer, f)

    if configuration[consts.KEY_ANALYSIS][consts.KEY_PLOT_GRAPH]:
        dot = Digraph(strict=True)
        log_analyzer.to_graph(dot, endpoints=endpoints)
        dot.render(os.path.join("output/", "dependencies"), view=False)

def main():
    cmd_parser = build_cmd_parser()
    args = cmd_parser.parse_args()

    configuration = {}
    with open(args.config_file, 'r') as config:
        configuration = json.loads(config.read())

    # clear the log file if exists
    output_file = configuration.get(consts.KEY_OUTPUT)
    enable_debug = configuration.get(consts.KEY_DEBUG)
    if enable_debug and os.path.exists(output_file):
        os.remove(output_file)

    logging.basicConfig(
        filename=output_file, level=logging.DEBUG)

    print("Reading OpenAPI document...")
    doc_file = configuration.get(consts.KEY_DOC_FILE)
    doc = read_doc(doc_file)
    openapi_parser = OpenAPIParser(doc)
    base_path, doc_entries = openapi_parser.parse()

    endpoints = configuration.get(consts.KEY_ENDPOINTS)
    if not endpoints:
        endpoints = doc.get(defs.DOC_PATHS).keys()

    exp_dir = prep_exp_dir(configuration)

    print("Loading witnesses...")
    if args.dynamic or args.witness or args.filtering:
        entries = parse_entries(configuration, exp_dir, base_path, doc_entries)

    if args.parallel or args.synthesis:
        with open(os.path.join(exp_dir, consts.FILE_ENTRIES), "rb") as f:
            entries = pickle.load(f)

    if args.dynamic:
        run_dynamic(configuration, entries, "/conversations.list", 500)
    
    elif args.witness:
        generate_witnesses(configuration, doc, exp_dir, entries, endpoints)
    
    else:
        with open(os.path.join(exp_dir, consts.FILE_GRAPH), "rb") as f:
            log_analyzer = pickle.load(f)
        
        if args.test:
            suites = configuration.get(consts.KEY_TEST_SUITES)
            if not suites:
                raise Exception("Test suites need to be specified in configuration file")

            run_test(suites, doc, configuration, log_analyzer)
        
        elif args.filtering:
            random.seed(1)

            dyn_analysis = dynamic.DynamicAnalysis(
                entries,
                configuration.get(consts.KEY_SKIP_FIELDS),
                abstraction_level=dynamic.CMP_ENDPOINT_AND_ARG_VALUE
            )

            with open("data/solutions.pkl", 'rb') as f:
                solutions = pickle.load(f)

            results = []
            for p in solutions:
                score = run_filter(
                    log_analyzer, dyn_analysis, 
                    {"channel_name": "objs_message.name"}, p, True
                )
                results.append((p, score))

            results = sorted(results, key=lambda x: x[-1], reverse=True)
            for i, (p, s) in enumerate(results):
                print("#", i+1)
                print("score:", s)
                print(p.pretty())

        elif args.parallel:
            init_synthesizer(doc, configuration, entries, exp_dir)
            inputs = {
                # "customer_id": SchemaType("customer.id", None),
                "product_name": SchemaType("product.name", None),
                "cur": SchemaType("fee.currency", None),
                "amt": SchemaType("unit_amount_/v1/prices_POST_unit_amount", None),
            }
            outputs = [SchemaType("plan.id", None)]
            # inputs = {
            #     "email": SchemaType("objs_user_profile.email", None),
            # }
            # outputs = [SchemaType("objs_message", None)]
            spawn_encoders(
                inputs, outputs,
                configuration[consts.KEY_SYNTHESIS][consts.KEY_SOLVER_NUM]
            )
        elif args.synthesis:
            synthesizer = Synthesizer(doc, configuration, entries, exp_dir)
            synthesizer.init()
            solutions = synthesizer.run_n(
                [],
                {
                    "customer_id": SchemaType("customer.id", None),
                    "product_id": SchemaType("product.id", None),
                },
                [
                    SchemaType("plan.id", None),
                ],
                1 # configuration["synthesis"]["solution_num"]
            )

            for prog in [r.pretty(synthesizer._entries, 0) for r in solutions]:
                print(prog)

        else:
            # output the results to json file
            with open(os.path.join("webapp/src/data/", "data.json"), 'w') as f:
                json_data = log_analyzer.to_json()
                json.dump(json_data, f)

            with open(os.path.join("webapp/src/data/", "schema.json"), 'w') as f:
                json_schema = get_schema_forest(doc)
                json.dump(json_schema, f)

if __name__ == "__main__":
    main()
