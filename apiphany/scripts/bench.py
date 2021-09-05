#!/usr/bin/env python3

#####
# BENCH RUNNER SCRIPT
#
# this script runs a set of tests defined as json files (one per API) in the
# rest_api_synthesis/benchmarks/ directory (any dir can be specified; this is
# the default). in the future this script will format the results as a latex
# table for inclusion in a latex file.
#
#####

import argparse

from apiphany.benchmarks.benchmark import BenchConfig, Bencher
from apiphany.analyzer import dynamic
from apiphany.benchmarks.suites import slack_suite, stripe_suite, square_suite

bias_type_args = {
    "none": dynamic.BiasType.NONE,
    "simple": dynamic.BiasType.SIMPLE,
    "look-ahead": dynamic.BiasType.LOOK_AHEAD
}

def build_cmd_parser():
    '''
        All arguments
    '''
    parser = argparse.ArgumentParser()
    parser.add_argument("output", nargs='?',
        help="Path to output latex table to")
    parser.add_argument("--repeat", type=int, nargs='?', default=5,
        help="Number of times to repeat filtering")
    parser.add_argument("--filter-num", type=int, nargs='?', default=3,
        help="Number of times to run filtering")
    parser.add_argument("--bias-type", default='simple',
        choices=list(bias_type_args.keys()) ,dest='bias_type',
        help="Bias type for retrospective execution")
    parser.add_argument("--bench", nargs='?',
        help="Path to benchmark file or directory (by default runs all in benchmarks)")
    parser.add_argument("--names", nargs="+",
        help="Benchmark name list")
    parser.add_argument("--cache", action='store_true', dest='cache',
        help="Whether to use cached results")
    parser.add_argument("--parallel", action='store_true', dest='parallel',
        help="Whether to run in parallel")
    parser.set_defaults(cache=False)
    parser.add_argument("--sol-only", action='store_true', dest='filter_sol_only',
        help="Whether to run retrospective execution on the solution only")
    parser.add_argument("--synthesis-only", action='store_true',
        help="Whether to run ranking")
    parser.set_defaults(filter_sol_only=False)
    return parser

def main():
    cmd_parser = build_cmd_parser()
    args = cmd_parser.parse_args()

    config = BenchConfig(
        args.cache,
        args.repeat,
        args.filter_num,
        args.filter_sol_only,
        args.synthesis_only,
        bias_type_args[args.bias_type],
        args.parallel)
    b = Bencher(
        [
            slack_suite,
            stripe_suite,
            square_suite,
        ],
        config)

    # with cProfile.Profile() as pr:
        
    b.run(
        args.names,
        output=args.output,
        print_api=True,
        print_results=True,
        print_appendix=True,
        plot_ranks=True,
        cached_results=True)

    # pr.print_stats()


if __name__ == '__main__':
    main()
