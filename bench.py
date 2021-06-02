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
import re

from analyzer import dynamic
from globs import get_solution_strs, init_synthesizer, get_petri_net_data
from openapi import defs
from openapi.utils import read_doc
from openapi.parser import OpenAPIParser
from program.program import ProjectionExpr, AppExpr
from program.program_equality import compare_program_strings
from run import prep_exp_dir, parse_entries
from schemas import types
from synthesizer.filtering import run_filter
from synthesizer.parallel import spawn_encoders
import consts
from benchmarks.benchmarks import benchmarks

BK_CONFIG = "config"
BK_SOLUTION = "solutions"
BK_BENCHES = "benchmarks"

bias_type_args = {
    "none": dynamic.BiasType.NONE,
    "simple": dynamic.BiasType.SIMPLE,
    "look-ahead": dynamic.BiasType.LOOK_AHEAD
}

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
    def __init__(self, repeat, bench, cache, filter_num, filter_sol_only, re_bias_type):
        self.benches = {}

        # map from api to entry
        self.table1 = {}
        # map from api to list of benches for each api
        self.table2 = {}

        self.repeat = repeat
        self.bench = bench
        self.cache = cache
        self.filter_num = filter_num
        self.filter_sol_only = filter_sol_only
        self.re_bias_type = re_bias_type
        self.config = dict()

    def run_benches(self, names=None):
        self.init_tables()

        for bench in benchmarks:
            self.run_bench(bench, names)

            print()

    def init_tables(self):
        "Reads a list JSON bench files from a folder, populating table1"

        for bench in benchmarks:
            with open(bench.config, 'r') as config_file:
                self.config[bench.name] = json.load(config_file)

            # populate table 1, part 1
            # for the name, we use the first part of the experiment name when split by _s.
            self.table1[bench.name] = {}

            # to get number of annotations, open the annotations file
            with open(self.config[bench.name]["witness"]["annotation_path"]) as af:
                a = json.load(af)
                self.table1[bench.name]["annotations"] = len(a)

    def run_bench(self, bench, names):
        # this assumes bench_key is in self.benches
        print(bench.name)
        print(f"• setup")

        configuration = self.config[bench.name]

        # clear the log file if exists
        output_file = configuration.get(consts.KEY_OUTPUT)
        enable_debug = configuration.get(consts.KEY_DEBUG)
        if enable_debug and exists(output_file):
            os.remove(output_file)

        logging.basicConfig(
            filename=output_file, level=logging.DEBUG)

        print("  • Reading OpenAPI document...")
        doc_file = configuration.get(consts.KEY_DOC_FILE)
        doc = read_doc(doc_file)
        openapi_parser = OpenAPIParser(doc)
        hostname, base_path, doc_entries = openapi_parser.parse()
        types.BaseType.doc_obj = doc

        endpoints = configuration.get(consts.KEY_ENDPOINTS)
        if not endpoints:
            endpoints = doc.get(defs.DOC_PATHS).keys()

        exp_dir = prep_exp_dir(configuration)

        print("  • Loading witnesses...")
        filter_entries = parse_entries(configuration, exp_dir, base_path, doc_entries)

        with open(os.path.join(exp_dir, consts.FILE_ENTRIES), "rb") as f:
            synth_entries = pickle.load(f)

        # initialize table 1, part 2
        self.table1[bench.name]["avg_num_args"] = avg([len(x.parameters) for x in filter_entries])

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

        self.table1[bench.name]["obj_size"] = avg(obj_sizes)
        self.table1[bench.name]["endpoints"] = len(endpoints)
        covered = {x.endpoint for x in filter_entries if str(x.endpoint) in endpoints}
        self.table1[bench.name]["endpoints_covered"] = len(covered)

        log_analyzer = None
        with open(os.path.join(exp_dir, "graph.pkl"), "rb") as f:
            log_analyzer = pickle.load(f)

        # initialize table 2, part 0
        self.table2[bench.name] = []

        blen = len(bench.benches)

        print(f"• run {blen} benches")

        for i, case in enumerate(bench.benches):
            print(f"  • [{i + 1}/{blen}]")

            if names is not None and case.name not in names:
                continue

            list_output = isinstance(case.output, types.ArrayType)

            bm_dir = os.path.join(exp_dir, case.name)
            # create a directory for the current benchmark
            cached = os.path.exists(bm_dir) and len(os.listdir(bm_dir)) != 0
            if cached and not self.cache:
                shutil.rmtree(bm_dir)

            os.makedirs(bm_dir, exist_ok=True)

            init_synthesizer(doc, configuration, synth_entries, bm_dir)

            if not cached or not self.cache:
                spawn_encoders(
                    case.input, case.output,
                    configuration["synthesis"]["solver_number"]
                )

            # process solutions
            solutions = set()
            for j in range(consts.DEFAULT_LENGTH_LIMIT + 1):
                sol_file = os.path.join(bm_dir, f"solutions_{j}.pkl")
                if os.path.exists(sol_file):
                    with open(sol_file, 'rb') as f:
                        programs = pickle.load(f)

                    solutions = solutions.union(programs)

            # initialize table 1, part 3
            # here, we report statistics on the petri net if they haven't been yet.
            if "places" not in self.table1[bench.name]:
                num_place, num_trans = get_petri_net_data()
                self.table1[bench.name]["places"] = num_place
                self.table1[bench.name]["transitions"] = num_trans

            # initialize table 2, part 1
            arr = {
                "name": case.name,
                "desc": case.description,
                "ast_size": "-",
                "endpoint_calls": "-",
                "projects": "-",
                "rank": "-",
                "rank_no_re": "-",
                "median_rank": "-",
                "mean_rank": "-",
            }

            # the solution is contained as a list of lines in the solution key.
            tgt_sols = ["\n".join(sol) for sol in case.solutions]
            res_no_re = get_solution_strs(solutions)

            found = False
            for rank, res_sol in enumerate(res_no_re):
                for tgt_sol in tgt_sols:
                    if compare_program_strings(tgt_sol, res_sol):
                        found = True
                        arr["rank_no_re"] = rank

                        break
                if found:
                    break

            sol_prog = None
            # We need to rank our solutions by running filtering first.
            def get_solution_rank():
                dyn_analysis = dynamic.DynamicAnalysis(
                    filter_entries,
                    configuration.get(consts.KEY_SKIP_FIELDS),
                    abstraction_level=dynamic.CMP_ENDPOINT_AND_ARG_VALUE,
                    bias_type=self.re_bias_type
                )

                results = []
                for p in solutions:
                    is_target_sol = False
                    for tgt_sol in tgt_sols:
                        is_target_sol = is_target_sol or compare_program_strings(tgt_sol, str(p))

                    if is_target_sol or not self.filter_sol_only:
                        cost = run_filter(
                            log_analyzer, dyn_analysis,
                            case.input, p, list_output,
                            repeat=self.repeat
                        )
                        results.append((p, cost))

                res = sorted(results, key=lambda x: x[-1])
                for r in res:
                    print(r[1], get_solution_strs([r[0]])[0])

                for rank, res_sol in enumerate(res):
                    for tgt_sol in tgt_sols:
                        if compare_program_strings(tgt_sol, str(res_sol[0])):
                            return rank + 1, res_sol[0]
                return None, None

            ranks = [get_solution_rank() for _ in range(self.filter_num)]
            sol_prog = ranks[0][1]
            ranks = [rank for rank, _ in ranks]
            print(ranks)
            if ranks[0] is not None:
                print(f"  • [{i + 1}/{blen}] PASS, Rank {rank}")
                arr["mean_rank"] = sum(ranks) / len(ranks)
                arr["rank"] = arr["mean_rank"]
                arr["median_rank"] = sorted(ranks)[len(ranks)//2]
            else:
                print(f"  • [{i + 1}/{blen}] FAIL")

            print(arr["rank_no_re"], arr["rank"])
            if sol_prog is not None:
                ns = sol_prog.collect_exprs()
                arr["ast_size"] = len(ns)
                arr["projects"] = len(list(filter(lambda x: isinstance(x, ProjectionExpr), ns)))
                arr["endpoint_calls"] = len(list(filter(lambda x: isinstance(x, AppExpr), ns)))
            self.table2[bench.name].append(arr)

    def print_table1(self, output=None):
        res = ("% auto-generated: ./bench.py, table 1\n"
            "\\resizebox{\\textwidth}{!}{\\begin{tabular}{lrrrrrrr}"
            "\\toprule"
            "& \\multicolumn{3}{c}{API size} & \\multicolumn{2}{c}{Sub-API size} & \\multicolumn{2}{c}{TNN size} \\\\"
            "\\cmidrule(lr){2-4} \\cmidrule(lr){5-6} \\cmidrule(lr){7-8}"
            "API & \\# endpoints & Avg. endpoint args & Avg. object size & \\# endpoints covered & \\# annotations & \\# places & \\# transitions \\\\"
            "\\midrule")
        res += "\n"

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
        res = ("% auto-generated: ./bench.py, table 2\n"
               "\\resizebox{\\textwidth}{!}{"
               "\\begin{tabular}{llp{5cm}rrrrr}"
               "\\toprule"
               "& \\multicolumn{2}{c}{Benchmark info} & \\multicolumn{3}{c}{Solution stats} & \\multicolumn{2}{c}{Solution rank} \\\\"
               "\\cmidrule(lr){2-3} \\cmidrule(lr){4-6} \\cmidrule(lr){7-8}"
               "API & Name & Description & AST Size & \\# endpoint calls & \\# projections & Without RE & With RE \\\\"
               "\\midrule")
        res += "\n"

        for i, (api, bench_results) in enumerate(self.table2.items()):
            res += api.capitalize() + " "
            for r in bench_results:
                res += f"& {r['name']} & {r['desc']} & {r['ast_size']} & {r['endpoint_calls']} & {r['projects']} & {r['rank_no_re']} & {r['rank']} "
                res += r" \\"
                res += "\n"
            if i < len(self.table2.items()) - 1:
                res += "\\hline\n"

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
    parser.add_argument("--filternum", type=int, nargs='?', default=3,
        help="Number of times to run filtering")
    parser.add_argument("--bench", nargs='?',
        help="Name of benchmark to run (by default runs all in benchmarks)")
    parser.add_argument("--names", nargs="+",
        help="Benchmark name list")
    parser.add_argument("--bias-type", default='simple', choices=list(bias_type_args.keys()) ,dest='bias_type',
        help="Bias type for retrospective execution")
    parser.add_argument("--cache", action='store_true', dest='cache',
        help="Whether to use cached results")
    parser.set_defaults(cache=False)
    parser.add_argument("--sol-only", action='store_true', dest='filter_sol_only',
        help="Whether to run retrospective execution on the solution only")
    parser.set_defaults(filter_sol_only=False)
    return parser

def main():
    cmd_parser = build_cmd_parser()
    args = cmd_parser.parse_args()

    b = Bencher(args.repeat, args.bench, args.cache, args.filternum, args.filter_sol_only, bias_type_args[args.bias_type])
    b.run_benches(names=args.names)
    b.print_table1(args.output)
    b.print_table2(args.output)

if __name__ == '__main__':
    main()
