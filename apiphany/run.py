#!/usr/bin/env python3

import argparse
import pickle
import os
import json
import logging
import random
from graphviz import Digraph
import cProfile

# analyze traces
from analyzer import analyzer, dynamic
from analyzer.ascription import Ascription
from openapi import defs
from openapi.parser import OpenAPIParser
from openapi.utils import read_doc, get_schema_forest
from schemas import types
from synthesizer.constructor import Constructor
from synthesizer.filtering import retrospective_execute
from synthesizer.parallel import spawn_encoders
from synthesizer.synthesizer import Synthesizer
from synthesizer.utils import make_entry_name
from witnesses.engine import WitnessGenerator
from benchmarks.utils import prep_exp_dir, parse_entries
import consts

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
    parser.add_argument("--data-dir", required=True,
        help="Path to the directory containing the data")
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

def run_dynamic(configuration, entries, endpoint, limit=500):
    analysis = dynamic.DynamicAnalysis(
        entries,
        configuration.get(consts.KEY_SKIP_FIELDS)
    )
    seqs = analysis.get_sequences(endpoint=endpoint, limit=limit)
    print(seqs)

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
    hostname, base_path, doc_entries = openapi_parser.parse()

    endpoints = configuration.get(consts.KEY_ENDPOINTS)
    if not endpoints:
        endpoints = doc.get(defs.DOC_PATHS).keys()

    exp_dir = prep_exp_dir(args.data_dir, "default_exp", configuration)

    print("Loading witnesses...")
    if args.dynamic or args.witness or args.filtering:
        entries = parse_entries(configuration, exp_dir, base_path, doc_entries)

    if args.parallel or args.synthesis:
        with open(os.path.join(exp_dir, consts.FILE_ENTRIES), "rb") as f:
            entries = pickle.load(f)

    if args.dynamic:
        run_dynamic(configuration, entries, "/conversations.list", 500)
    
    elif args.witness:
        generate_witnesses(
            configuration, doc, doc_entries, hostname, base_path,
            exp_dir, entries, endpoints, args.uncovered
        )
    
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
                score = retrospective_execute(
                    log_analyzer, entries,
                    configuration.get(consts.KEY_SKIP_FIELDS),
                    dynamic.BiasType.SIMPLE, p
                )
                results.append((p, score))

            results = sorted(results, key=lambda x: x[-1], reverse=True)
            for i, (p, s) in enumerate(results):
                print("#", i+1)
                print("score:", s)
                print(p.pretty())

        elif args.parallel:
            synthesizer = Synthesizer(configuration, entries, exp_dir)
            synthesizer.init()
            inputs = {
                # "price": types.SchemaObject("price", None)
                "email": types.PrimString("objs_user_profile.email"),
                # "price_id": types.PrimString("plan.id")
                # "product_id": types.PrimString("product.id"),
            }
            outputs = [types.SchemaObject("objs_message")]
            spawn_encoders(
                synthesizer, inputs, outputs,
                configuration[consts.KEY_SYNTHESIS][consts.KEY_SOLVER_NUM]
            )
        elif args.synthesis:
            with cProfile.Profile() as pr:
                synthesizer = Synthesizer(configuration, entries, exp_dir)
                synthesizer.init()
                solutions = synthesizer.run_n(
                    [],
                    {
                        "channel": types.PrimString("defs_channel"),
                        "ts": types.PrimString("defs_ts"),
                    },
                    [types.SchemaObject("objs_message")],
                    5000
                    # configuration[consts.KEY_SYNTHESIS][consts.KEY_SOL_NUM]
                )

                pr.print_stats()

            # for prog in [r.pretty(0) for r in solutions]:
            #     print(prog)

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
