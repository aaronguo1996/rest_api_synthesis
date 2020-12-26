import unittest

from tests import test_parser

PARSER_SUITE="parser suite"

def run_test(test_suites=""):
    runner = unittest.TextTestRunner(verbosity=2)
    if PARSER_SUITE in test_suites:
        runner.run(test_parser.suite())
    else:
        raise NotImplementedError