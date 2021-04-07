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

from glob import glob
import os
from os.path import abspath, exists, join
import json
import logging

from analyzer import analyzer
import config_keys as keys
from graphviz import Digraph
from openapi import defs
from openapi.utils import read_doc
from synthesizer.synthesizer import *
from program.program_equality import compare_program_strings

BK_ANALYZER = "analyzer"
BK_CONFIG = "config"
BK_DOC = "doc"
BK_SOLUTION = "solution"

class Bencher:
    def __init__(self):
        self.benches = {}

    def run_benches(self, folder="benchmarks"):
        self.read_benches(folder)
        
        for bench_key in self.benches.keys():
            self.setup_bench(bench_key)
            self.exec_bench(bench_key)

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

    def setup_bench(self, bench_key):
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

        print("  • Reading traces...")
        entries = []
        with open(join("data/", "traces_update_bk.pkl"), 'rb') as f:
            entries = pickle.load(f)

        # for e in entries:
        #     e.response.array_level = 0

        # with open(join("data/", "traces_update.pkl"), 'wb') as f:
        #     pickle.dump(entries, f)
        print("  • Analyzing provided traces...")
        log_analyzer = analyzer.LogAnalyzer()
        log_analyzer.analyze(
            doc.get(defs.DOC_PATHS),
            entries, 
            configuration.get(keys.KEY_SKIP_FIELDS),
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
            dot.render(join("output/", "dependencies"), view=False)

        self.benches[bench_key][BK_ANALYZER] = log_analyzer
        self.benches[bench_key][BK_DOC] = doc
        
    def exec_bench(self, bench_key):
        blen = len(self.benches[bench_key]['benchmarks'])

        print(f"• run {blen} benches")

        for i, bench in enumerate(self.benches[bench_key]['benchmarks']):
            print(f"  • [{i + 1}/{blen}]")
            synthesizer = Synthesizer(
                self.benches[bench_key][BK_DOC],
                self.benches[bench_key][BK_CONFIG],
                self.benches[bench_key][BK_ANALYZER],
            )
            synthesizer.init()

            res = synthesizer.run_n(
                bench["landmarks"],
                {k: SchemaType(v, None) for k, v in bench["input_args"].items()},
                [SchemaType(bench["output"], None)],
                bench["max_length"]
            )

            # the solution is contained as a list of lines in the solution key.
            if BK_SOLUTION in bench:
                tgt_sol = "\n".join(bench[BK_SOLUTION])
                # print(repr(tgt_sol))

                # for r in res:
                #     print(repr(str(synthesizer._program_generator.generate_program(r, {k: SchemaType(v, None) for k, v in bench["input_args"].items()}, SchemaType(bench["output"], None))[0])))

                res_sols = [str(synthesizer._program_generator.generate_program(r, {k: SchemaType(v, None) for k, v in bench["input_args"].items()}, SchemaType(bench["output"], None))[0]) for r in res]

                #TODO: actually run filterer so that res_sols is actually in order of rank
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

if __name__ == '__main__':
    b = Bencher()
    b.run_benches()
