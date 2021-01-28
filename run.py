#!/usr/bin/python3.8

import argparse
import pickle
import os
import json
import logging
import matplotlib.pyplot as plt
from collections import defaultdict

from traces import parser, analyzer
from fuzzer import fuzzer
from tests import test_runner
from openapi.preprocess import PreProcessor
from prance import ResolvingParser, ValidationError

# definitions of all the subcommands
ANALYSIS_PARSER = 0
FUZZ_PARSER = 1
TEST_PARSER = 10

# definitions of constants
DEFAULT_DEBUG_OUTPUT = 'debug.log' 

def build_cmd_parser():
    '''
        All arguments
    '''
    parser = argparse.ArgumentParser()
    parser.add_argument("config_file", nargs='?',
                        help="Path to the configuration file")
    parser.add_argument("--test", action="store_true", help="Run unit tests")
    parser.add_argument("--plot", action="store_true", help="Plot graphs without fuzzing")
    parser.add_argument("--print-log", action="store_true", help="Print log from previous run")
    return parser

def read_doc(doc_path):
    try:
        parser = ResolvingParser(doc_path)
        # spec with all the references resolved
        return parser.specification
    except ValidationError: # allow other exceptions to be thrown
        path_segs = doc_path.split('/')
        old_filename = path_segs[-1]
        name_segs = old_filename.split('.')
        new_filename = '.'.join(name_segs[:-1]) + "_preprocess.json"
        preprocessor = PreProcessor(doc_path)
        new_path = '/'.join(path_segs[:-1] + [new_filename])
        preprocessor.preprocess(new_path)
        return read_doc(new_path)

def read_data():
    # {
    #         "Iteration": i,
    #         "Results": results,
    #         "Endpoints": self._covered_endpoints,
    #         "Error buckets": self._error_buckets,
    #     }
    results = []
    with open(fuzzer.RESULT_FILE, "rb") as f:
        try:
            x = pickle.load(f)
            while x:
                results.append(x)
                x = pickle.load(f)
        except:
            pass

    return results

def plot_errors(iter_results):
    errors = defaultdict(int)
    for i_result in iter_results:
        results = i_result["Results"]
        for r in results:
            if r.has_error:
                errors[(r.return_code, r.response_body.get("error"))] += 1

    lists = errors.items()
    labels, y = zip(*lists) # unpack a list of pairs into two tuples
    plt.figure(figsize=(20,20))
    plt.bar(range(len(y)), y)
    plt.xticks(range(len(y)), labels, rotation=90)
    plt.xlabel("Errors")
    plt.ylabel("Number of Occurrences")
    plt.savefig("errors.png")
    plt.close()

def plot_coverage(iter_results):
    coverage = {}
    for i_result in iter_results:
        coverage[i_result["Iteration"]] = len(i_result["Endpoints"])

    lists = coverage.items()
    x, y = zip(*lists)
    plt.plot(x, y)
    plt.xlabel("Iteration")
    plt.ylabel("Number of Endpoints")
    plt.savefig("coverage.png")
    plt.close()

def print_errors(iter_results):
    with open("errors.log", "w+") as f:
        for i_result in iter_results:
            for r in i_result["Results"]:
                if r.has_error:
                    f.write(r.endpoint)
                    f.write('\n')
                    f.write(json.dumps(r.request_params))
                    f.write('\n')
                    f.write(json.dumps(r.response_body))
                    f.write('\n')

def main():
    cmd_parser = build_cmd_parser()
    args = cmd_parser.parse_args()

    configuration = {}
    with open(args.config_file, 'r') as config:
        configuration = json.loads(config.read())

    # clear the log file if exists
    if (configuration["enable_debug"] and 
        not args.plot and not args.print_log and
        os.path.exists(configuration["debug_output"])):
        os.remove(configuration["debug_output"])

    logging.basicConfig(
        filename=configuration["debug_output"], level=logging.DEBUG)

    if args.test:
        suites = configuration.get("test_suites")

        if not suites:
            raise Exception("Test suites need to be specified in configuration file")

        test_runner.run_test(configuration["test_suites"])
    elif args.plot:
        results = read_data()
        plot_errors(results)
        plot_coverage(results)
    elif args.print_log:
        results = read_data()
        print_errors(results)
    else:
        print("Reading OpenAPI document...")
        doc = read_doc(configuration["doc_file"])

        # with open('debug.json', 'w+') as f:
        #     f.write(json.dumps(doc))

        print("Parsing OpenAPI document...")
        entries = None
        log_parser = parser.LogParser(
            configuration["log_file"], configuration["hostname"], doc)
        entries = log_parser.parse_entries(
            configuration["analysis"]["uninteresting_endpoints"],
            configuration["analysis"]["ignore_field_names"])
        if configuration["enable_debug"]:
            # write entries to log file
            logging.debug("========== Start Logging Parse Results ==========")
            for e in entries:
                logging.debug(e)

        print("Analyzing provided log file...")
        log_analyzer = analyzer.LogAnalyzer()
        log_analyzer.analyze(entries)
        groups = log_analyzer.analysis_result()
        # graph_flag = configuration["analysis"]["params"]["allow_only_input"]
        # log_analyzer.to_graph(graph_flag)
        if configuration["enable_debug"]:
            logging.debug("========== Start Logging Analyze Results ==========")
            for g in groups:
                logging.debug(g)
    
        print("Running fuzzer to get more traces...")
        engine = fuzzer.Fuzzer(
            doc, log_analyzer,
            configuration["fuzz"]["value_dict"], 
            configuration["fuzz"]["fuzz_depth"],
            configuration["path_to_definitions"],
            configuration["analysis"]["ignore_field_names"],
            configuration["fuzz"]["plot_graph"],
        )

        endpoints = configuration["fuzz"]["endpoints"]
        if not endpoints:
            endpoints = list(doc["paths"].keys())

        if configuration["fuzz"]["plot_graph"]:
            engine.to_graph(endpoints, "dependencies_0")

        engine.saturate_all(
            endpoints, configuration["fuzz"]["iterations"], 
            configuration["fuzz"]["timeout_per_request"])

if __name__ == "__main__":
    main()