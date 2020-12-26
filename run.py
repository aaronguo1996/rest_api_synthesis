#!/usr/bin/python3.8

import argparse
import unittest

from traces import parser
from tests import test_runner

# definitions of all the subcommands
LOG_PARSER=0
TEST_PARSER=1

def build_log_parser(subparsers):
    '''
        Command line arguments for parsing traces
    '''
    log_parser = subparsers.add_parser("parser")
    log_parser.add_argument("--log-file", type=str, required=True,
                            help="Path to the log file to be parsed")
    log_parser.add_argument("--hostname", type=str, required=True,
                            help="Hostname of the APIs to be analyzed")
    log_parser.set_defaults(subparser=LOG_PARSER)

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
    build_log_parser(subparsers)
    build_test_parser(subparsers)
    return parser

def main():
    cmd_parser = build_cmd_parser()
    args = cmd_parser.parse_args()

    if args.subparser == LOG_PARSER:
        log_parser = parser.LogParser(args.log_file, args.hostname)
        log_parser.parse_entries()
    elif args.subparser == TEST_PARSER:
        test_runner.run_test(args.suites)
    else:
        raise NotImplementedError

if __name__ == "__main__":
    main()