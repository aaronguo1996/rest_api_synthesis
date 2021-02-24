#!/usr/bin/python3.8

import argparse
import pickle
import os
import json
import logging
from graphviz import Digraph

# analyze traces
from analyzer import analyzer, dynamic
from schemas.schema_type import SchemaType
from openapi import defs
from openapi.utils import read_doc, get_schema_forest
import config_keys as keys

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

    print("Reading traces...")
    entries = []
    with open(os.path.join("data/", "traces_update.pkl"), 'rb') as f:
        entries = pickle.load(f)

    # for e in entries:
    #     e.response.array_level = 0

    # with open(os.path.join("data/", "traces_update.pkl"), 'wb') as f:
    #     pickle.dump(entries, f)
    print("Analyzing provided traces...")
    log_analyzer = analyzer.LogAnalyzer()
    log_analyzer.analyze(
        doc.get(defs.DOC_PATHS),
        entries, 
        configuration.get(keys.KEY_SKIP_FIELDS))
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
        seqs = analysis.get_sequences(endpoint="/users.lookupByEmail", limit=500)
        print(seqs)
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