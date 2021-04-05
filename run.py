#!/usr/bin/python3.8

import argparse
import pickle
import os
import json
import logging
import random
from graphviz import Digraph

# analyze traces
from analyzer import analyzer, dynamic, parser
from schemas.schema_type import SchemaType
from openapi import defs
from openapi.utils import read_doc, get_schema_forest
import config_keys as keys
from synthesizer.filtering import run_filter
from synthesizer.parallel import spawn_encoders
from globs import init_synthesizer
from witnesses.engine import WitnessGenerator

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
    parser.add_argument("--parallel", action="store_true",
        help="Run synthesis algorithm in parallel mode")
    parser.add_argument("--witness", action="store_true",
        help="Generate witnesses by configuration")
    return parser

def main():
    cmd_parser = build_cmd_parser()
    args = cmd_parser.parse_args()

    configuration = {}
    with open(args.config_file, 'r') as config:
        configuration = json.loads(config.read())

    # clear the log file if exists
    output_file = configuration.get(keys.KEY_OUTPUT)
    enable_debug = configuration.get(keys.KEY_DEBUG)
    if enable_debug and os.path.exists(output_file):
        os.remove(output_file)

    logging.basicConfig(
        filename=output_file, level=logging.DEBUG)

    print("Reading OpenAPI document...")
    doc_file = configuration.get(keys.KEY_DOC_FILE)
    doc = read_doc(doc_file)
    SchemaType.doc_obj = doc

    print("Loading existing witnesses...")
    if args.witness:
        print("Parsing OpenAPI document...")
        # entries = None
        log_parser = parser.LogParser(
            configuration["log_file"], configuration["hostname"], doc)
        entries = log_parser.parse_entries(
            configuration["analysis"]["uninteresting_endpoints"],
            configuration.get(keys.KEY_SKIP_FIELDS),
        )
        if configuration["enable_debug"]:
            # write entries to log file
            logging.debug("========== Start Logging Parse Results ==========")
            for e in entries:
                logging.debug(e)
    else:
        with open(os.path.join("data/witnesses/", "traces_update_bk.pkl"), 'rb') as f:
            entries = pickle.load(f)

    print("Analyzing provided traces...")
    log_analyzer = analyzer.LogAnalyzer()
    log_analyzer.analyze(
        doc.get(defs.DOC_PATHS),
        entries, 
        configuration.get(keys.KEY_SKIP_FIELDS),
        configuration.get(keys.KEY_BLACKLIST),
        prefilter=configuration.get(keys.KEY_SYNTHESIS).get(keys.KEY_SYN_PREFILTER))
    groups = log_analyzer.analysis_result()
    if enable_debug:
        logging.debug("========== Start Logging Analyze Results ==========")
        for g in groups:
            logging.debug(g)

    endpoints = configuration.get(keys.KEY_ENDPOINTS)
    if not endpoints:
        endpoints = doc.get(defs.DOC_PATHS).keys()

    if configuration["analysis"]["plot_graph"]:
        dot = Digraph(strict=True)
        log_analyzer.to_graph(dot, endpoints=endpoints)
        dot.render(os.path.join("output/", "dependencies"), view=False)

    if args.test:
        suites = configuration.get(keys.KEY_TEST_SUITES)

        if not suites:
            raise Exception("Test suites need to be specified in configuration file")

        run_test(suites, doc, configuration, log_analyzer)
    elif args.dynamic:
        analysis = dynamic.DynamicAnalysis(
            entries,
            configuration.get(keys.KEY_SKIP_FIELDS)
        )
        seqs = analysis.get_sequences(endpoint="/conversations.list", limit=500)
        print(seqs)
    elif args.filtering:
        random.seed(1)

        dyn_analysis = dynamic.DynamicAnalysis(
            entries,
            configuration.get(keys.KEY_SKIP_FIELDS),
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
        init_synthesizer(doc, configuration, log_analyzer)
        inputs = {
            "channel_name": SchemaType("objs_conversation.name", None),
        }
        outputs = [
            SchemaType("objs_user.profile.email", None),
        ]
        spawn_encoders(
            inputs, outputs,
            configuration["synthesis"]["solver_number"]
        )
    elif args.witness:
        print("Running fuzzer to get more traces...")
        engine = WitnessGenerator(
            doc, log_analyzer,
            configuration["witness"]["value_dict"],
            configuration["witness"]["annotation_path"],
            configuration["witness"]["gen_depth"],
            configuration["path_to_definitions"],
            configuration.get(keys.KEY_SKIP_FIELDS),
            configuration["witness"]["plot_graph"],
        )

        if configuration["witness"]["plot_graph"]:
            engine.to_graph(endpoints, "dependencies_0")

        engine.saturate_all(
            endpoints, configuration["witness"]["iterations"],
            configuration["witness"]["timeout_per_request"])
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