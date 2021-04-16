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
import shutil
import sys
import pickle

from analyzer import dynamic
from globs import get_solution_strs, init_synthesizer, get_petri_net_data
from openapi import defs
from openapi.utils import read_doc
from program.program import ProjectionExpr, AppExpr
from program.program_equality import compare_program_strings
from run import prep_exp_dir, parse_entries
from schemas.schema_type import SchemaType
from synthesizer.filtering import run_filter
from synthesizer.parallel import spawn_encoders
from synthesizer.utils import DEFAULT_LENGTH_LIMIT
import config_keys as keys

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

def avg(lst):
    return sum(lst) / len(lst)

class Bencher:
    def __init__(self, repeat, bench):
        self.benches = {}

        # map from api to entry
        self.table1 = {}
        # map from api to list of benches for each api
        self.table2 = {}

        self.repeat = repeat
        self.bench = bench

    def tkey(self, bench_key):
        return self.benches[bench_key][BK_CONFIG]["exp_name"].split("_")[0]

    def run_benches(self, folder="benchmarks", names=None):
        self.read_benches(folder)

        for bench_key in self.benches.keys():
            self.run_bench(bench_key, names)

            print()

    def read_benches(self, folder="benchmarks"):
        "Reads a list JSON bench files from a folder, populating table1"

        if self.bench is None:
            self.bench = "benchmarks"

        if os.path.isdir(self.bench):
            files = [f for f in glob(f"{folder}/*.json")]
        else:
            files = [self.bench]

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

    def run_bench(self, bench_key, names):
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

        obj_sizes = []
        schemas = doc.get(defs.DOC_COMPONENTS).get(defs.DOC_SCHEMAS)
        for _, sch in schemas.items():
            typ = sch.get(defs.DOC_TYPE)
            if typ == "object":
                if defs.DOC_PROPERTIES in sch:
                    properties = sch.get(defs.DOC_PROPERTIES)
                    obj_sizes.append(len(properties))
                    continue

            obj_sizes.append(1)

        self.table1[key]["obj_size"] = avg(obj_sizes)
        self.table1[key]["endpoints"] = len(endpoints)
        self.table1[key]["endpoints_covered"] = len({x.endpoint for x in entries})

        log_analyzer = None
        with open(os.path.join(exp_dir, "graph.pkl"), "rb") as f:
            log_analyzer = pickle.load(f)

        # initialize table 2, part 0
        self.table2[key] = []

        blen = len(self.benches[bench_key][BK_BENCHES])

        print(f"• run {blen} benches")

        for i, bench in enumerate(self.benches[bench_key][BK_BENCHES]):
            print(f"  • [{i + 1}/{blen}]")

            if names is not None and bench["name"] not in names:
                continue

            # create a directory for the current benchmark
            bm_dir = os.path.join(exp_dir, bench["name"])
            if os.path.exists(bm_dir):
                shutil.rmtree(bm_dir)

            os.makedirs(bm_dir, exist_ok=True)

            init_synthesizer(doc, configuration, log_analyzer, bm_dir)
            inputs = {k: SchemaType(v, None) for k, v in bench["input_args"].items()}
            output = [SchemaType(out, None) for out in bench["output"]]
            spawn_encoders(
                inputs, output,
                configuration["synthesis"]["solver_number"]
            )

            # process solutions
            solutions = set()
            for i in range(DEFAULT_LENGTH_LIMIT + 1):
                sol_file = os.path.join(bm_dir, f"solutions_{i}.pkl")
                if os.path.exists(sol_file):
                    with open(sol_file, 'rb') as f:
                        programs = pickle.load(f)

                    solutions = solutions.union(programs)

            # initialize table 1, part 3
            # here, we report statistics on the petri net if they haven't been yet.
            if "places" not in self.table1[key]:
                num_place, num_trans = get_petri_net_data()
                self.table1[key]["places"] = num_place
                self.table1[key]["transitions"] = num_trans

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
                res_no_re = get_solution_strs(solutions)

                found = False
                for rank, res_sol in enumerate(res_no_re):
                    if compare_program_strings(tgt_sol, res_sol):
                        found = True
                        arr["rank_no_re"] = rank

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
                    cost = run_filter(
                        log_analyzer, dyn_analysis,
                        inputs, p, bench["output_list"],
                        repeat=self.repeat
                    )
                    results.append((p, cost))

                res = sorted(results, key=lambda x: x[-1])
                for r in res:
                    print(r[1], r[0])

                res_sols = [str(r) for r, _ in res]

                found = False
                for rank, res_sol in enumerate(res_sols):
                    if compare_program_strings(tgt_sol, res_sol):
                        print(f"  • [{i + 1}/{blen}] PASS, Rank {rank}")
                        found = True
                        arr["rank"] = rank

                        #TODO: FIX THIS PLS
                        try:
                            ns = res[rank].collect_exprs()
                            arr["ast_size"] = len(ns)
                            arr["projects"] = len(filter(lambda x: isinstance(x, ProjectionExpr), ns))
                            arr["endpoint_calls"] = len(filter(lambda x: isinstance(x, AppExpr), ns))
                        except:
                            pass

                        break
                if not found:
                    print(f"  • [{i + 1}/{blen}] FAIL")
            else:
                print(f"  • [{i + 1}/{blen}] NO SOL")

            self.table2[key].append(arr)

    def print_table1(self, output=None):
        res = ("% auto-generated: ./bench.py, table 1"
            "\\resizebox{\textwidth}{!}{\\begin{tabular}{lrrrrrrr}"
            "\\toprule"
            "& \\multicolumn{3}{c}{API size} & \\multicolumn{2}{c}{Sub-API size} & \\multicolumn{2}{c}{TNN size} \\\\"
            "\\cmidrule(lr){2-4} \\cmidrule(lr){5-6} \\cmidrule(lr){7-8}"
            "API & \\# endpoints & Avg. endpoint args & Avg. object size & \\# endpoints covered & \\# annotations & \\# places & \\# transitions \\\\"
            "\\midrule")

        for api, rest in self.table1.items():
            avg_num_args = round(rest['avg_num_args'], 2)
            obj_size = round(rest['obj_size'], 2)
            res += f"  {api.capitalize()} & {rest['endpoints']} & {avg_num_args} & {obj_size} & {rest['endpoints_covered']} & {rest['annotations']} & {rest['places']} & {rest['transitions']}"
            res += r" \\"
            res += "\n"

        res += ("\\bottomrule"
                "\\end{tabular}}")

        # print(res)

        if output:
            with open(join(output, "table1.tex"), "w") as of:
                of.write(res)
                print(f"written to {join(output, 'table1.tex')}")

    def print_table2(self, output=None):
        res = ("% auto-generated: ./bench.py, table 2"
               "\\resizebox{\\textwidth}{!}{"
               "\\begin{tabular}{llp{5cm}rrrrr}"
               "\\toprule"
               "& \\multicolumn{2}{c}{Benchmark info} & \\multicolumn{3}{c}{Solution stats} & \\multicolumn{2}{c}{Solution rank} \\\\"
               "\\cmidrule(lr){2-3} \\cmidrule(lr){4-6} \\cmidrule(lr){7-8}"
               "API & Name & Description & AST Size & \\# endpoint calls & \\# projections & Without RE & With RE \\\\"
               "\\midrule")

        for api, bench_results in self.table2.items():
            res += api.capitalize() + " "
            for r in bench_results:
                res += f"& {r['name']} & {r['desc']} & {r['ast_size']} & {r['endpoint_calls']} & {r['projects']} & {r['rank_no_re']} & {r['rank']} "
                res += r" \\"
                res += "\n"

        res += ("\\bottomrule"
                "\\end{tabular}}")

        # print(res)

        if output:
            with open(join(output, "table2.tex"), "w") as of:
                of.write(res)
                print(f"written to {join(output, 'table2.tex')}")

def build_cmd_parser():
    '''
        All arguments
    '''
    parser = argparse.ArgumentParser()
    parser.add_argument("output", nargs='?',
        help="Path to output latex table to")
    parser.add_argument("--repeat", type=int, nargs='?', default=5,
        help="Number of times to repeat filtering")
    parser.add_argument("--bench", nargs='?',
        help="Path to benchmark file or directory (by default runs all in benchmarks)")
    parser.add_argument("--names", nargs="+",
        help="Benchmark name list")
    return parser

def main():
    cmd_parser = build_cmd_parser()
    args = cmd_parser.parse_args()

    b = Bencher(args.repeat, args.bench)
    b.run_benches(names=args.names)
    b.print_table1(args.output)
    b.print_table2(args.output)

if __name__ == '__main__':
    main()
