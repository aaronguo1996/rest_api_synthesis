#!/usr/bin/python3.8

import argparse
import unittest
import os
import json
import logging

from traces import parser, analyzer
from tests import test_runner

# definitions of all the subcommands
ANALYSIS_PARSER = 0
FUZZ_PARSER = 1
TEST_PARSER = 10

# definitions of constants
DEFAULT_DEBUG_OUTPUT = 'debug.log' 

def build_analysis_parser(subparsers):
    '''
        Command ling arguments for analyze traces
    '''
    analysis_parser = subparsers.add_parser("analyze")
    analysis_parser.add_argument("config_file", nargs='?',
                                 help="Path to the configuration file")
    analysis_parser.set_defaults(subparser=ANALYSIS_PARSER)

def build_test_parser(subparsers):
    '''
        Command line arguments for unit testing
    '''
    test_parser = subparsers.add_parser("test")
    test_parser.add_argument("--suites", type=str, nargs="+",
                             help="Which test suites to run")
    test_parser.set_defaults(subparser=TEST_PARSER)

def build_cmd_parser():
    '''
        All arguments
    '''
    parser = argparse.ArgumentParser()
    subparsers = parser.add_subparsers(help="Sub-command help")
    build_analysis_parser(subparsers)
    build_test_parser(subparsers)
    return parser

def main():
    cmd_parser = build_cmd_parser()
    args = cmd_parser.parse_args()

    configuration = {}
    with open(args.config_file, 'r') as config:
        configuration = json.loads(config.read())

    # clear the log file if exists
    if (configuration["enable_debug"] and 
        os.path.exists(configuration["debug_output"])):
        os.remove(configuration["debug_output"])

    logging.basicConfig(
        filename=configuration["debug_output"],
        encoding='utf-8', level=logging.DEBUG)

    entries = None
    if args.subparser == ANALYSIS_PARSER or args.subparser == FUZZ_PARSER:
        log_parser = parser.LogParser(
            configuration["log_file"], 
            configuration["hostname"],
            configuration["doc_file"])
        entries = log_parser.parse_entries(
            configuration["uninteresting_endpoints"],
            configuration["ignore_field_names"])
        if configuration["enable_debug"]:
            # write entries to log file
            logging.debug("========== Start Logging Parse Results ==========")
            for e in entries:
                logging.debug(e)

        log_analyzer = analyzer.LogAnalyzer()
        log_analyzer.analyze(entries)
        groups = log_analyzer.analysis_result()
        graph_flag = configuration["analysis_params"]["allow_only_input"]
        log_analyzer.to_graph(graph_flag)
        if configuration["enable_debug"]:
            logging.debug("========== Start Logging Analyze Results ==========")
            for g in groups:
                logging.debug(g)

    if args.subparser == FUZZ_PARSER:
        pass

    if args.subparser == TEST_PARSER:
        test_runner.run_test(args.suites)
    
if __name__ == "__main__":
    main()