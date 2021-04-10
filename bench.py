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
from glob import glob
import os
from os.path import abspath, exists, join
import json
import logging
import random

from run import prep_exp_dir, parse_entries

from analyzer import analyzer, dynamic
import config_keys as keys
from graphviz import Digraph
from openapi import defs
from openapi.utils import read_doc
from synthesizer.synthesizer import *
from program.program_equality import compare_program_strings

BK_CONFIG = "config"
BK_SOLUTION = "solution"
BK_BENCHES = "benchmarks"

class SuppressPrint:
    def __init__(self, verbose):
        self.verbose = verbose
        
    def __enter__(self):
        if not self.verbose:
            self._original_stdout = sys.stdout
            sys.stdout = open(os.devnull, 'w')

    def __exit__(self, exc_type, exc_val, exc_tb):
        sys.stdout.close()
        sys.stdout = self._original_stdout

class Bencher:
    def __init__(self):
        self.benches = {}

    def run_benches(self, folder="benchmarks"):
        self.read_benches(folder)
        
        for bench_key in self.benches.keys():
            self.run_bench(bench_key)

            print()

    def read_benches(self, folder="benchmarks"):
        "Reads a list JSON bench files from a folder"

        files = [f for f in glob(f"{folder}/*.json")]

        print("reading benches")

        for inf in files:
            with open(inf) as f:
                js = json.load(f)
                config_path = js.get(BK_CONFIG)
                if not config_path:
                    print(f"✗ {inf}: no config")
                    continue

                with open(config_path) as cf:
                    js[BK_CONFIG] = json.load(cf)

                print(f"✓ {inf}: read")

            self.benches[inf] = js

        print()

    def run_bench(self, bench_key):
        # this assumes bench_key is in self.benches
        print(bench_key)
        print(f"• setup")
        
        configuration = self.benches[bench_key][BK_CONFIG]

        # clear the log file if exists
        output_file = configuration.get(keys.KEY_OUTPUT)
        enable_debug = configuration.get(keys.KEY_DEBUG)
        if enable_debug and exists(output_file):
            os.remove(output_file)

        logging.basicConfig(
            filename=output_file, level=logging.DEBUG)

        print("  • Reading OpenAPI document...")
        doc_file = configuration.get(keys.KEY_DOC_FILE)
        doc = read_doc(doc_file)
        SchemaType.doc_obj = doc

        endpoints = configuration.get(keys.KEY_ENDPOINTS)
        if not endpoints:
            endpoints = doc.get(defs.DOC_PATHS).keys()

        exp_dir = prep_exp_dir(configuration)

        print("  • Loading witnesses...")
        entries = parse_entries(doc, configuration, exp_dir)

        log_analyzer = None
        with open(os.path.join(exp_dir, "graph.pkl"), "rb") as f:
            log_analyzer = pickle.load(f)

        # log_analyzer = analyzer.LogAnalyzer()
        # log_analyzer.analyze(
        #     doc.get(defs.DOC_PATHS),
        #     entries, 
        #     configuration.get(keys.KEY_SKIP_FIELDS),
        #     configuration.get(keys.KEY_BLACKLIST),
        #     prefilter=configuration.get(keys.KEY_SYNTHESIS).get(keys.KEY_SYN_PREFILTER))

        blen = len(self.benches[bench_key][BK_BENCHES])

        print(f"• run {blen} benches")

        for i, bench in enumerate(self.benches[bench_key][BK_BENCHES]):
            print(f"  • [{i + 1}/{blen}]")
            synthesizer = Synthesizer(
                doc,
                configuration,
                log_analyzer,
                exp_dir
            )
            synthesizer.init()

            solutions = synthesizer.run_n(
                bench["landmarks"],
                {k: SchemaType(v, None) for k, v in bench["input_args"].items()},
                [SchemaType(bench["output"], None)],
                bench["max_length"]
            )

            # the solution is contained as a list of lines in the solution key.
            if BK_SOLUTION in bench:
                tgt_sol = "\n".join(bench[BK_SOLUTION])

                # We need to rank our solutions by running filtering first.
                random.seed(1)

                dyn_analysis = dynamic.DynamicAnalysis(
                    entries,
                    configuration.get(keys.KEY_SKIP_FIELDS),
                    abstraction_level=dynamic.CMP_ENDPOINT_AND_ARG_VALUE
                )

                results = []
                for p in solutions:
                    score = run_filter(
                        log_analyzer, dyn_analysis, 
                        {"channel_name": "objs_message.name"}, p, True
                    )
                    results.append((p, score))

                res = sorted(results, key=lambda x: x[-1], reverse=True)

                res_sols = [str(synthesizer._program_generator.generate_program(r, {k: SchemaType(v, None) for k, v in bench["input_args"].items()}, SchemaType(bench["output"], None))[0]) for r in res]

                found = False
                for rank, res_sol in enumerate(res_sols):
                    if compare_program_strings(tgt_sol, res_sol):
                        print(f"  • [{i + 1}/{blen}] PASS, Rank {rank}")
                        found = True
                        break
                if not found:
                    print(f"  • [{i + 1}/{blen}] FAIL")
            else:
                print(f"  • [{i + 1}/{blen}] NO SOL")

    def filter_bench(self, bench_key):
        pass

def build_cmd_parser():
    '''
        All arguments
    '''
    parser = argparse.ArgumentParser()
    parser.add_argument("output", nargs='?',
        help="Path to output latex table to")
    return parser

def main():
    cmd_parser = build_cmd_parser()
    args = cmd_parser.parse_args()

    b = Bencher()
    b.run_benches()

if __name__ == '__main__':
    main()
