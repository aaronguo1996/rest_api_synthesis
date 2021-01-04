#!/usr/bin/python3.8

import argparse
import unittest
import os

from traces import parser, analyzer
from tests import test_runner

# definitions of all the subcommands
ANALYSIS_PARSER = 0
TEST_PARSER     = 10

# definitions of constants
DEFAULT_DEBUG_OUTPUT = 'debug.log' 

def build_analysis_parser(subparsers):
    '''
        Command ling arguments for analyze traces
    '''
    analysis_parser = subparsers.add_parser("analyze")
    analysis_parser.add_argument("--log-file", type=str, required=True,
                                 help="Path to the log file to be parsed")
    analysis_parser.add_argument("--hostname", type=str, required=True,
                                 help="Hostname of the APIs to be analyzed")
    analysis_parser.add_argument("--debug", action="store_true",
                                 help="Enable writing debug traces to logs")
    analysis_parser.add_argument("--debug-output", type=str, default=DEFAULT_DEBUG_OUTPUT,
                                 help="Path to the debug file")
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

    # clear the log file if exists
    if args.debug and os.path.exists(args.debug_output):
        os.remove(args.debug_output)

    entries = None
    if args.subparser == ANALYSIS_PARSER:
        log_parser = parser.LogParser(args.log_file, args.hostname)
        entries = log_parser.parse_entries()
        if args.debug:
            # write entries to log file
            with open(args.debug_output, 'a+') as f:
                f.write("==================== Start Logging Parse Results ====================\n")
                for e in entries:
                    f.write(str(e) + "\n")

        log_analyzer = analyzer.LogAnalyzer()
        log_analyzer.analyze(entries)
        groups = log_analyzer.analysis_result()
        if args.debug:
            with open(args.debug_output, 'a+') as f:
                f.write("==================== Start Logging Analyze Results ====================\n")
                for g in groups:
                    f.write(str(g) + "\n")

    if args.subparser == TEST_PARSER:
        test_runner.run_test(args.suites)
    
if __name__ == "__main__":
    main()