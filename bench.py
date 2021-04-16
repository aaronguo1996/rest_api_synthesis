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
from collections import namedtuple
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
from synthesizer.filtering import run_filter
from program.program import ProjectionExpr, AppExpr
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

# Entry1 = namedtuple('Entry1', 'endpoints, avg_num_args, obj_size, endpoints_covered, annotations, places, transitions')
# Entry2 = namedtuple('Entry2', 'id, name, desc, ast_size, endpoint_calls, projects, rank, rank_no_re')

def avg(lst):
    return sum(lst) / len(lst)

class Bencher:
    def __init__(self, repeat):
        self.benches = {}

        # map from api to entry
        self.table1 = {}
        # map from api to list of benches for each api
        self.table2 = {}

        self.repeat = repeat

    def tkey(self, bench_key):
        return self.benches[bench_key][BK_CONFIG]["exp_name"].split("_")[0]

    def run_benches(self, bench=None, folder="benchmarks"):
        self.read_benches(folder)
        
        for bench_key in self.benches.keys():
            if (bench is not None and bench == bench_key) or bench is None:
                self.run_bench(bench_key)

            print()

    def read_benches(self, folder="benchmarks"):
        "Reads a list JSON bench files from a folder, populating table1"

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

            # set self.benches
            self.benches[inf] = js

            # populate table 1, part 1
            # for the name, we use the first part of the experiment name when split by _s.
            key = self.tkey(inf)
            self.table1[key] = {}

            # to get number of annotations, open the annotations file
            with open(js[BK_CONFIG]["witness"]["annotation_path"]) as af:
                a = json.load(af)
                self.table1[key]["annotations"] = len(a)

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

        # initialize table 1, part 2
        key = self.tkey(bench_key)
        self.table1[key]["avg_num_args"] = avg([len(x.parameters) for x in entries])
        self.table1[key]["obj_size"] = avg([len(d.get(defs.DOC_PROPERTIES)) if defs.DOC_PROPERTIES in d else 0 for n, d in doc.get(defs.DOC_COMPONENTS).get(defs.DOC_SCHEMAS).items() if d.get(defs.DOC_TYPE) == "object"])
        self.table1[key]["endpoints"] = len(endpoints)
        self.table1[key]["endpoints_covered"] = len({x.endpoint for x in entries})

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

        # initialize table 2, part 0
        self.table2[key] = []

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

            inputs = {k: SchemaType(v, None) for k, v in bench["input_args"].items()}

            solutions = synthesizer.run_n(
                bench["landmarks"],
                {k: SchemaType(v, None) for k, v in bench["input_args"].items()},
                [SchemaType(bench["output"], None)],
                bench["max_length"]
            )

            for prog in solutions:
                print(prog.pretty())

            # initialize table 1, part 3
            # here, we report statistics on the petri net if they haven't been yet.
            if "places" not in self.table1[key]:
                self.table1[key]["places"] = len(synthesizer._encoder._net.place())
                self.table1[key]["transitions"] = len(synthesizer._encoder._net.transition())

            # initialize table 2, part 1
            arr = {
                "name": bench["name"],
                "desc": bench["desc"],
                "ast_size": "N/A",
                "endpoint_calls": "N/A",
                "projects": "N/A",
                "rank": "N/A",
                "rank_no_re": "N/A",
            }
                
            # the solution is contained as a list of lines in the solution key.
            if BK_SOLUTION in bench:
                tgt_sol = "\n".join(bench[BK_SOLUTION])

                res_no_re = [r.pretty() for r in solutions]

                found = False
                for rank, res_sol in enumerate(res_no_re):
                    if compare_program_strings(tgt_sol, res_sol):
                        found = True
                        arr["rank_no_re"] = rank + 1

                        break

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
                        bench["input_args"], p, True,
                        repeat=self.repeat if self.repeat else 5
                    )
                    results.append((p, score))

                res = sorted(results, key=lambda x: x[-1], reverse=True)

                res_sols = [r.pretty() for r, _ in res]

                found = False
                for rank, res_sol in enumerate(res_sols):
                    if compare_program_strings(tgt_sol, res_sol):
                        print(f"  • [{i + 1}/{blen}] PASS, Rank {rank}")
                        found = True
                        arr["rank"] = rank + 1

                        ns = res[rank][0].collect_exprs()
                        arr["ast_size"] = len(ns)
                        arr["projects"] = len(list(filter(lambda x: isinstance(x, ProjectionExpr), ns)))
                        arr["endpoint_calls"] = len(list(filter(lambda x: isinstance(x, AppExpr), ns)))

                        break
                if not found:
                    print(f"  • [{i + 1}/{blen}] FAIL")
            else:
                print(f"  • [{i + 1}/{blen}] NO SOL")

            self.table2[key].append(arr)

    def print_table1(self, output=None):
        res = r"""% auto-generated: ./bench.py, table 1
\resizebox{\textwidth}{!}{\begin{tabular}{lrrrrrrr}
  \toprule
  & \multicolumn{3}{c}{API size} & \multicolumn{2}{c}{Sub-API size} & \multicolumn{2}{c}{TNN size} \\
  \cmidrule(lr){2-4} \cmidrule(lr){5-6} \cmidrule(lr){7-8}
  API & \# endpoints & Avg. endpoint args & Avg. object size & \# endpoints covered & \# annotations & \# places & \# transitions \\
  \midrule
"""
        print(self.table1)
        for api, rest in self.table1.items():
            if 'avg_num_args' in rest:
                avg_num_args = round(rest['avg_num_args'], 2)
                obj_size = round(rest['obj_size'], 2)
                res += f"  {api.capitalize()} & {rest['endpoints']} & {avg_num_args} & {obj_size} & {rest['endpoints_covered']} & {rest['annotations']} & {rest['places']} & {rest['transitions']}"
                res += r" \\"
                res += "\n"

        res += r"""  \bottomrule
\end{tabular}}
"""

        print(res)

        if output:
            with open(join(output, "table1.tex"), "w") as of:
                of.write(res)
                print(f"written to {join(output, 'table1.tex')}")

    def print_table2(self, output=None):
        res = r"""% auto-generated: ./bench.py, table 2
\resizebox{\textwidth}{!}{
  \begin{tabular}{llp{5cm}rrrrr}
    \toprule
    & \multicolumn{2}{c}{Benchmark info} & \multicolumn{3}{c}{Solution stats} & \multicolumn{2}{c}{Solution rank} \\
    \cmidrule(lr){2-3} \cmidrule(lr){4-6} \cmidrule(lr){7-8}
    API & Name & Description & AST Size & \# endpoint calls & \# projections & Without RE & With RE \\
    \midrule
"""
        for api, bench_results in self.table2.items():
            res += api.capitalize() + " "
            for r in bench_results:
                res += f"& {r['name']} & {r['desc']} & {r['ast_size']} & {r['endpoint_calls']} & {r['projects']} & {r['rank_no_re']} & {r['rank']} "
                res += r" \\"
                res += "\n"

        res += r"""    \bottomrule
  \end{tabular}
}
"""

        print(res)

        if output:
            with open(join(output, "table2.tex"), "w") as of:
                of.write(res)
                print(f"written to {join(output, 'table2.tex')}")

def build_cmd_parser():
    '''
        All arguments
    '''
    parser = argparse.ArgumentParser()
    parser.add_argument("bench", nargs='?',
                        help="Bench file to run")
    parser.add_argument("--output", nargs='?',
        help="Path to output latex table to")
    parser.add_argument("--repeat", type=int, nargs='?',
        help="Number of times to repeat filtering")
    return parser

def main():
    cmd_parser = build_cmd_parser()
    args = cmd_parser.parse_args()

    print(args.bench)

    b = Bencher(args.repeat)
    b.run_benches(bench=args.bench)
    b.print_table1(args.output)
    b.print_table2(args.output)

if __name__ == '__main__':
    main()
