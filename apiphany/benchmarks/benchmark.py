from globs import get_petri_net_data
import json
import pickle
import os
import shutil
import pebble
import time

import consts
from openapi import defs
from openapi.utils import read_doc
from openapi.parser import OpenAPIParser
from synthesizer.synthesizer import Synthesizer
import benchmarks.utils as utils
from schemas import types
from analyzer import dynamic
from synthesizer.filtering import retrospective_execute, check_results
from program.program import ProjectionExpr, AppExpr, FilterExpr
from synthesizer import parallel

class BenchConfig:
    def __init__(
        self, cache=False, repeat=5, filter_num=3,
        filter_sol_only=False, synthesis_only=False,
        bias_type=dynamic.BiasType.SIMPLE, use_parallel=True):
        self.cache = cache
        self.repeat = repeat
        self.filter_num = filter_num
        self.filter_sol_only = filter_sol_only
        self.synthesis_only = synthesis_only
        self.re_bias_type = bias_type
        self.use_parallel = use_parallel

class BenchmarkResult:
    def __init__(self, name, desc):
        self.name = name
        self.desc = desc
        self.rank_no_re = None
        self.mean_rank = None
        self.median_rank = None
        self.ast_size = None
        self.projects = None
        self.filters = None
        self.endpoint_calls = None

class APIInfo:
    def __init__(self, api, num_args, obj_size, ep_num, ep_covered, annotations):
        self.api_name = api
        self.avg_num_args = num_args
        self.obj_size = obj_size
        self.ep_num = ep_num
        self.ep_covered = ep_covered
        self.annotations = annotations

class Benchmark:
    def __init__(self, name, desc, inputs, output, solutions):
        self.name = name
        self.description = desc
        self.inputs = inputs
        self.output = output
        self.solutions = solutions
        self.latex_entry = BenchmarkResult(name, desc)

    def run(self, exp_dir, entries, configuration, runtime_config):
        bm_dir = os.path.join(exp_dir, self.name)
        # create a directory for the current benchmark
        cached = os.path.exists(bm_dir) and len(os.listdir(bm_dir)) != 0
        if cached and not runtime_config.cache:
            shutil.rmtree(bm_dir)

        os.makedirs(bm_dir, exist_ok=True)

        if not cached or not runtime_config.cache:
            synthesizer = Synthesizer(configuration, entries, bm_dir)
            synthesizer.init()
            parallel.spawn_encoders(
                synthesizer,
                self.inputs, [self.output],
                configuration[consts.KEY_SYNTHESIS][consts.KEY_SOLVER_NUM]
            )
            
        solutions = {}
        for j in range(consts.DEFAULT_LENGTH_LIMIT + 1):
            sol_file = os.path.join(bm_dir, f"solutions_{j}.pkl")
            if os.path.exists(sol_file):
                try:
                    with open(sol_file, 'rb') as f:
                        programs = pickle.load(f)
                except Exception as e:
                    print(j)
                    raise Exception(e)

                solutions.update({p:p for p in programs})

        num_place, num_trans = get_petri_net_data(bm_dir)

        return num_place, num_trans, list(solutions.keys())

    def _run_re(
        self, entries, configuration, runtime_config, 
        log_analyzer, solutions):
        all_results = []
        
        with pebble.ProcessPool() as pool:
            for i, p in enumerate(solutions):
                print(f"{i}/{len(solutions)}", flush=True)
                print(p, flush=True)

                is_target_sol = False
                for tgt_sol in self.solutions:
                    eq_target = tgt_sol == p
                    is_target_sol = is_target_sol or eq_target

                start = time.time()
                if is_target_sol or not runtime_config.filter_sol_only:
                    reps = []
                    for j in range(runtime_config.filter_num):
                        group_results = []
                        for k in range(runtime_config.repeat):
                            if runtime_config.use_parallel:
                                future = pool.schedule(
                                    retrospective_execute,
                                    args=(
                                        log_analyzer,
                                        entries,
                                        configuration.get(consts.KEY_SKIP_FIELDS),
                                        runtime_config.re_bias_type,
                                        p)
                                )
                            else:
                                future = retrospective_execute(
                                    log_analyzer,
                                    entries,
                                    configuration.get(consts.KEY_SKIP_FIELDS),
                                    runtime_config.re_bias_type,
                                    p)

                            group_results.append(future)

                        reps.append(group_results)

                    end = time.time()
                    print("Time for running a program for all reptitions:", end - start, flush=True)

                    all_results.append(reps)

        return all_results

    def get_rank(
        self, entries, configuration, runtime_config, 
        log_analyzer, solutions):
        found = False
        print("Total solutions:", len(solutions), flush=True)
        for rank, res_sol in enumerate(solutions):
            for tgt_sol in self.solutions:
                if tgt_sol == res_sol:
                    found = True
                    self.latex_entry.rank_no_re = rank
                    break

            if found:
                break

        all_results = self._run_re(
            entries, configuration, runtime_config,
            log_analyzer, solutions)

        program_ranks = [[] for _ in range(runtime_config.repeat)]
        for i, reps in enumerate(all_results):
            for j, rep in enumerate(reps):
                if runtime_config.use_parallel:
                    results = [x.result() for x in rep]
                else:
                    results = [x for x in rep]

                score = check_results(
                    results,
                    isinstance(self.output, types.ArrayType))
                if runtime_config.filter_sol_only:
                    p = self.solutions[0]
                else:
                    p = solutions[i]

                program_ranks[j].append((i, p, score))

        ranks = []
        for res in program_ranks:
            res = sorted(res, key=lambda x: x[-1])
            for rank, (_, res_sol, score) in enumerate(res):
                if (res_sol in self.solutions and
                    abs(score - consts.MAX_COST) > 1e-2):
                    ranks.append((rank + 1, res_sol, score))

                    for i, r in enumerate(res):
                        print(i, r[0], r[2], r[1])

                    break

        sol_prog = ranks[0][1] if len(ranks) > 0 else None
        ranks = [r[0] for r in ranks]
        return ranks, sol_prog

    def to_latex_entry(self, ranks, sol_prog):
        if len(ranks) > 0 and ranks[0] is not None:
            print(f"PASS, Ranks {ranks}")
            self.latex_entry.mean_rank = sum(ranks) / len(ranks)
            self.latex_entry.median_rank = sorted(ranks)[len(ranks)//2]
        else:
            print(f"FAIL")
        
        if sol_prog is not None:
            ns = sol_prog.collect_exprs()
            self.latex_entry.ast_size = len(ns)
            self.latex_entry.projects = len(
                list(filter(lambda x: isinstance(x, ProjectionExpr), ns)))
            self.latex_entry.filters = len(
                list(filter(lambda x: isinstance(x, FilterExpr), ns)))
            self.latex_entry.endpoint_calls = len(
                list(filter(lambda x: isinstance(x, AppExpr), ns)))

        return self.latex_entry

class BenchmarkSuite:
    def __init__(self, config_file, api, benchmarks):
        self._prep(config_file)
        self.api = api
        self.benchmarks = benchmarks

    def _prep(self, config_file):
        with open(config_file, 'r') as config:
            self._configuration = json.loads(config.read())
        doc_file = self._configuration.get(consts.KEY_DOC_FILE)
        self._doc = read_doc(doc_file)
        openapi_parser = OpenAPIParser(self._doc)
        _, base_path, doc_entries = openapi_parser.parse()

        endpoints = self._configuration.get(consts.KEY_ENDPOINTS)
        if not endpoints:
            endpoints = self._doc.get(defs.DOC_PATHS).keys()

        self._exp_dir = utils.prep_exp_dir(self._configuration)
        self._entries = utils.parse_entries(
            self._configuration, 
            self._exp_dir, 
            base_path, 
            doc_entries)

        with open(os.path.join(self._exp_dir, consts.FILE_ENTRIES), "rb") as f:
            self._typed_entries = pickle.load(f)

        with open(os.path.join(self._exp_dir, consts.FILE_GRAPH), "rb") as f:
            self._log_analyzer = pickle.load(f)

    def get_info(self):
        # to get number of annotations, open the annotations file
        ann_file = self._configuration[consts.KEY_WITNESS][consts.KEY_ANNOTATION]
        with open(ann_file, 'r') as af:
            a = json.load(af)
            annotations = len(a)

        # average number of endpoint arguments
        avg_num_args = utils.avg([len(x.parameters) for x in self._entries])

        # average number of object size
        # FIXME: this is wrong, we need to count numbers of nodes in objects
        # the problem is that we might have mutual recursive definitions
        obj_sizes = []
        schemas = self._doc.get(defs.DOC_COMPONENTS).get(defs.DOC_SCHEMAS)
        for _, sch in schemas.items():
            typ = sch.get(defs.DOC_TYPE)
            if typ == defs.TYPE_OBJECT:
                if defs.DOC_PROPERTIES in sch:
                    properties = sch.get(defs.DOC_PROPERTIES)
                    obj_sizes.append(len(properties))
                    continue

            obj_sizes.append(1)

        obj_size = utils.avg(obj_sizes)

        # number of endpoints
        endpoints = self._doc.get(defs.DOC_PATHS)
        ep_num = len(endpoints)

        # covered endpoints
        covered = {
            x.endpoint for x in self._entries if x.endpoint in endpoints
        }
        ep_covered = len(covered)

        return APIInfo(
            self.api, avg_num_args, obj_size, 
            ep_num, ep_covered, annotations)

    def run(self, runtime_config, names, cached_results=False):
        latex_entries = []
        places = None
        transitions = None
        entries = utils.index_entries(
            self._entries,
            self._configuration.get(consts.KEY_SKIP_FIELDS)
        )

        cache_path = os.path.join(self._exp_dir, "bench_results.pkl")
        if cached_results:
            with open(cache_path, "rb") as f:
                d = pickle.load(f)

            places = d["places"]
            transitions = d["transitions"]
            latex_entries = d["results"]
        else:
            for benchmark in self.benchmarks:
                if names is not None and benchmark.name not in names:
                    continue

                print("Running benchmark", benchmark.name)
                places, transitions, solutions = benchmark.run(
                    self._exp_dir, 
                    self._typed_entries, 
                    self._configuration,
                    runtime_config
                )

                if not runtime_config.synthesis_only:
                    print("RE")
                    ranks, sol_prog = benchmark.get_rank(
                        entries,
                        self._configuration,
                        runtime_config,
                        self._log_analyzer,
                        solutions,
                    )

                    latex_entry = benchmark.to_latex_entry(ranks, sol_prog)
                    latex_entries.append(latex_entry)


            print("dumping")
            with open(cache_path, "wb") as f:
                pickle.dump({
                    "places": places,
                    "transitions": transitions,
                    "results": latex_entries,
                }, f)

        return latex_entries, places, transitions

class Bencher:
    def __init__(self, suites, config):
        self._suites = suites
        self._config = config

    def run(self, names, cached_results=False, print_api=False, print_results=False, output=None):
        place_counts = []
        trans_counts = []
        benchmark_results = []
        
        for suite in self._suites:
            benchmark_entries, places, transitions = suite.run(
                self._config, names, cached_results)
            place_counts.append(places)
            trans_counts.append(transitions)
            benchmark_results.append(benchmark_entries)

        if print_api:
            self.print_api_info(place_counts, trans_counts, output)

        if print_results:
            self.print_benchmark_results(benchmark_results, output)

    def print_api_info(self, places, transitions, output=None):
        res = ("% auto-generated: ./bench.py, table 1\n"
            "\\resizebox{\\textwidth}{!}{\\begin{tabular}{lrrrrrrr}"
            "\\toprule"
            "& \\multicolumn{3}{c}{API size} & \\multicolumn{2}{c}{Sub-API size} & \\multicolumn{2}{c}{TTN size} \\\\"
            "\\cmidrule(lr){2-4} \\cmidrule(lr){5-6} \\cmidrule(lr){7-8}"
            "API & \\# endpoints & Avg. endpoint args & Avg. object size & \\# endpoints covered & \\# annotations & \\# places & \\# transitions \\\\"
            "\\midrule")
        res += "\n"

        for i, suite in enumerate(self._suites):
            if places[i] is not None:
                api_info = suite.get_info()
                avg_num_args = round(api_info.avg_num_args, 2)
                obj_size = round(api_info.obj_size, 2)
                res += (f"  {api_info.api_name.capitalize()} "
                    f"& {api_info.ep_num} "
                    f"& {avg_num_args} "
                    f"& {obj_size} "
                    f"& {api_info.ep_covered} "
                    f"& {api_info.annotations} "
                    f"& {places[i]} "
                    f"& {transitions[i]}")
                res += r" \\"
                res += "\n"

        res += ("\\bottomrule"
                "\\end{tabular}}")

        # print(res)

        if output:
            with open(os.path.join(output, "table1.tex"), "w") as of:
                of.write(res)
                print(f"written to {os.path.join(output, 'table1.tex')}")

    def print_benchmark_results(self, results, output=None):
        res = ("% auto-generated: ./bench.py, table 2\n"
               "\\resizebox{\\textwidth}{!}{"
               "\\begin{tabular}{l|lp{7.5cm}|rrrr|rr}"
               "\\toprule"
               "& \\multicolumn{2}{c|}{Benchmark info} & \\multicolumn{4}{c|}{Solution stats} & \\multicolumn{2}{c}{Solution rank} \\\\"
               "\\cmidrule(lr){2-3} \\cmidrule(lr){4-7} \\cmidrule(lr){8-9}"
               "API & Name & Description & Size & $n_{ep}$ & $n_{proj}$ & $n_{filter} $ & w/o RE & w/ RE \\\\"
               "\\midrule")
        res += "\n"

        for i, suite in enumerate(self._suites):
            bench_results = results[i]
            res += f"\\multirow{{{len(suite.benchmarks)}}}{{*}}{{{suite.api.capitalize()}}} "
            for r in bench_results:
                if r is None:
                    continue

                res += (
                    f"& {r.name} "
                    f"& {r.desc} "
                    f"& {utils.pretty_none(r.ast_size)} "
                    f"& {utils.pretty_none(r.endpoint_calls)} "
                    f"& {utils.pretty_none(r.projects)} "
                    f"& {utils.pretty_none(r.filters)} "
                    f"& {utils.pretty_none(r.rank_no_re)} "
                    f"& {utils.pretty_none(r.mean_rank)} ")
                res += r" \\"
                res += "\n"
            if i < len(self._suites) - 1:
                res += "\\hline\n"

        res += ("\\bottomrule"
                "\\end{tabular}}")

        # print(res)

        if output:
            with open(os.path.join(output, "table2.tex"), "w") as of:
                of.write(res)
                print(f"written to {os.path.join(output, 'table2.tex')}")
