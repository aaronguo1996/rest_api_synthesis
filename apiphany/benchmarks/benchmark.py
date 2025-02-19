import cProfile
import json
import pickle
import os
import shutil
from graphviz import Digraph

from analyzer import dynamic, analyzer
from analyzer.ascription import Ascription
from analyzer.entry import ErrorResponse
from openapi import defs
from openapi.parser import OpenAPIParser
from openapi.utils import read_doc
from program.program import EquiExpr, ProjectionExpr, AppExpr
from synthesizer import parallel
from synthesizer.constructor import Constructor
from synthesizer.synthesizer import Synthesizer
from witnesses.engine import WitnessGenerator
import benchmarks.utils as utils
import consts
from schemas import types


class BenchConfig:
    def __init__(
        self, cache=False, repeat_exp=3, repeat_re=15,
        filter_sol_only=False, synthesis_only=False, witness_only=False,
        bias_type=dynamic.BiasType.SIMPLE, use_parallel=True,
        get_place_stats=False, generate_witness=False, method_coverage=1,
        uncovered_opt=consts.UncoveredOption.DEFAULT_TO_SYNTACTIC,
        conversion_fair=False, prim_as_return=False, with_partials=False, 
        syntactic_only=False, no_merge=False):
        self.cache = cache
        self.repeat_exp = repeat_exp
        self.repeat_re = repeat_re
        self.filter_sol_only = filter_sol_only
        self.synthesis_only = synthesis_only
        self.witness_only = witness_only
        self.re_bias_type = bias_type
        self.use_parallel = use_parallel
        self.get_place_stats = get_place_stats
        self.generate_witness = generate_witness
        self.method_coverage = method_coverage
        self.uncovered_opt = uncovered_opt
        self.conversion_fair = conversion_fair
        self.prim_as_return = prim_as_return
        self.syntactic_only = syntactic_only
        self.with_partials = with_partials
        self.no_merge = no_merge

class BenchmarkResult:
    def __init__(self, name, desc):
        self.name = name
        self.desc = desc
        self.rank_no_re = None
        self.rank_no_re_before_sol = None
        self.rank_no_re_rng = None
        self.rank_before_sol = None
        self.ranks = None
        self.ast_size = None
        self.projects = None
        self.filters = None
        self.endpoint_calls = None
        self.syn_time = None
        self.re_time = None
        self.candidates = None
        self.paths = None

class APIInfo:
    def __init__(self, api, num_args, obj_sizes, obj_num, ep_num, 
        init_w, init_covered, gen_w, ep_covered, annotations):
        self.api_name = api
        self.num_args = num_args
        self.obj_sizes = obj_sizes
        self.obj_num = obj_num
        self.ep_num = ep_num
        self.init_w = init_w
        self.init_covered = init_covered
        self.gen_w = gen_w
        self.ep_covered = ep_covered
        self.annotations = annotations

class Benchmark:
    def __init__(self, name, desc, source, inputs, output, solutions, is_effectful):
        self.name = name
        self.description = desc
        self.source = source
        self.inputs = inputs
        self.output = output
        self.solutions = solutions
        self.is_effectful = is_effectful
        self.latex_entry = BenchmarkResult(name, desc)

    def run(self, exp_dir, entries, indexed_entries, configuration, analyzer, runtime_config):
        print(f"Running {self.name}")

        bm_dir = os.path.join(exp_dir, self.name)
        # create a directory for the current benchmark
        cached = os.path.exists(bm_dir) and len(os.listdir(bm_dir)) != 0
        if cached and not runtime_config.cache:
            shutil.rmtree(bm_dir)

        os.makedirs(bm_dir, exist_ok=True)

        if not cached or not runtime_config.cache:
            synthesizer = Synthesizer(configuration, entries, bm_dir)
            synthesizer.init()
            # convert the types before passing into the synthesizer
            rep_inputs = {}
            for ip, tip in self.inputs.items():
                tip = analyzer.find_representative_for_type(
                    tip, 
                    not runtime_config.syntactic_only)
                rep_inputs[ip] = tip
            #     if runtime_config.syntactic_only:
            #         tip.to_syntactic()

            # if runtime_config.syntactic_only:
            #     self.output.to_syntactic()
            is_array_output = isinstance(self.output, types.ArrayType)
            rep_output = self.output.ignore_array()
            rep_output = analyzer.find_representative_for_type(
                rep_output, 
                not runtime_config.syntactic_only)

            print("inputs", rep_inputs)
            print("output", rep_output)
            # with cProfile.Profile() as p:
            parallel.spawn_encoders(
                synthesizer,
                analyzer,
                indexed_entries,
                rep_inputs, [rep_output], is_array_output,
                configuration[consts.KEY_SYNTHESIS][consts.KEY_SOLVER_NUM],
                self.solutions[0],
                runtime_config,
            )
                # p.sort_stats("cumulative").print_stats(999999)
            
        solutions = []
        prev_solutions = {}
        for j in range(consts.DEFAULT_LENGTH_LIMIT + 1):
            sol_file = os.path.join(bm_dir, f"solutions_{j}.pkl")
            if os.path.exists(sol_file):
                try:
                    with open(sol_file, 'rb') as f:
                        programs = pickle.load(f)
                except Exception as e:
                    print(j)
                    raise Exception(e)

                solution_at_len = []
                for p in programs:
                    if p not in prev_solutions:
                        solution_at_len.append(p)

                prev_solutions.update({p:p for p in programs})
                solutions.append(solution_at_len)

        num_place, num_trans, path_cnt = utils.get_petri_net_data(bm_dir)

        return num_place, num_trans, path_cnt, solutions

    def to_latex_entry(self, paths, candidates):
        # sort candidates by cost
        sorted_candidates = sorted(candidates, key=lambda x: x[-1])
        
        # find the position of the desired solution
        syn_time = None
        re_time = None
        solution_found = False
        rank = None
        candidates_lower = []
        for rank, (syn_time, sol_prog, re_time, cost) in enumerate(sorted_candidates):            
            # print(rank, cost, sol_prog.has_conversion())
            # print(rank, sol_prog)
            candidates_lower.append((syn_time, sol_prog, re_time, cost))

            if sol_prog in self.solutions:
                print("Solution found")
                print(sol_prog, "has cost", cost)
                solution_found = True
                break

        if rank is not None:
            rank += 1

        if solution_found:
            candidates_no_re = len(candidates)
            candidates_before_sol = [c for c in sorted_candidates if c[0] <= syn_time]
            self.latex_entry.ranks = [rank]
            rank_before_sol = len([c for c in candidates_lower if c[0] <= syn_time])
            self.latex_entry.rank_before_sol = rank_before_sol
            print(f"PASS, Ranks {rank} vs {candidates_no_re}")
            self.latex_entry.mean_rank = rank
            self.latex_entry.median_rank = rank
            self.latex_entry.syn_time = syn_time
            self.latex_entry.re_time = re_time
            self.latex_entry.rank_no_re = candidates_no_re
            self.latex_entry.rank_no_re_before_sol = len(candidates_before_sol)
            self.latex_entry.candidates = len(candidates)
            self.latex_entry.paths = paths
        else:
            print(f"FAIL")

        # collect stats about the solution
        ns = self.solutions[0].collect_exprs()
        self.latex_entry.ast_size = len(ns)
        self.latex_entry.projects = len(
            list(filter(lambda x: isinstance(x, ProjectionExpr), ns)))
        self.latex_entry.filters = len(
            list(filter(lambda x: isinstance(x, EquiExpr), ns)))
        self.latex_entry.endpoint_calls = len(
            list(filter(lambda x: isinstance(x, AppExpr), ns)))

        return self.latex_entry

class BenchmarkSuite:
    def __init__(self, config_file, api, benchmarks):
        self.config_file = config_file
        self.api = api
        self.benchmarks = benchmarks

    def prep(self, data_dir, exp_dir, runtime_config):
        with open(self.config_file, 'r') as config:
            self._configuration = json.loads(config.read())
        doc_file = self._configuration.get(consts.KEY_DOC_FILE)
        self._doc = read_doc(doc_file)
        openapi_parser = OpenAPIParser(self._doc)
        hostname, base_path, doc_entries = openapi_parser.parse()

        endpoints = self._configuration.get(consts.KEY_ENDPOINTS)
        if not endpoints:
            endpoints = self._doc.get(defs.DOC_PATHS).keys()

        self._suite_dir = utils.prep_exp_dir(data_dir, exp_dir, self._configuration)
        # create subdirs for different runs
        if not runtime_config.witness_only:
            oldest_dir = None
            oldest_ts = None
            for i in range(runtime_config.repeat_exp):
                self._iter_dir = os.path.join(self._suite_dir, f"iter_{i}")
                if not os.path.exists(self._iter_dir):
                    os.makedirs(self._iter_dir)
                    oldest_dir = None
                    break
                else:
                    mtime = os.path.getmtime(self._iter_dir)
                    if oldest_ts is None or mtime < oldest_ts:
                        oldest_dir = self._iter_dir
                        oldest_ts = mtime

            if oldest_dir is not None:
                self._iter_dir = oldest_dir

        self._witnesses = utils.parse_entries(
            self._configuration, 
            self._suite_dir, 
            base_path, 
            doc_entries)
        self._initial_witnesses = utils.get_initial_witnesses(
            self._configuration, 
            self._suite_dir, 
            base_path, 
            doc_entries)

        paths = self._doc.get(defs.DOC_PATHS)
        self._witnesses = utils.prune_by_coverage(
            paths, self._witnesses,
            runtime_config.method_coverage)

        if runtime_config.generate_witness:
            self.generate_witnesses(
                doc_entries, hostname, base_path,
                self._witnesses, endpoints, 
                runtime_config,
            )

        with open(os.path.join(self._suite_dir, consts.FILE_ENTRIES), "rb") as f:
            self._typed_entries = pickle.load(f)
        
        with open(os.path.join(self._suite_dir, consts.FILE_GRAPH), "rb") as f:
            self._log_analyzer = pickle.load(f)

    def generate_witnesses(self, doc_entries, hostname, base_path, 
        witnesses, endpoints, runtime_config):
        print("---------------------------------------------------------------")
        print("Analyzing provided witnesses for", self.api)
        log_analyzer = analyzer.LogAnalyzer(runtime_config.uncovered_opt)
        prefilter = self._configuration.get(consts.KEY_SYNTHESIS).get(consts.KEY_SYN_PREFILTER)
        skip_fields = self._configuration.get(consts.KEY_SKIP_FIELDS)
        
        if not runtime_config.no_merge:
            log_analyzer.analyze(
                doc_entries,
                witnesses,
                skip_fields,
                self._configuration.get(consts.KEY_BLACKLIST),
                prefilter=prefilter)

        ascription = Ascription(log_analyzer, skip_fields)
        entries = utils.create_entries(
            doc_entries, self._configuration, ascription, 
            not runtime_config.syntactic_only)

        print("Getting more traces...")
        engine = WitnessGenerator(
            doc_entries, hostname, base_path, entries, log_analyzer,
            self._configuration[consts.KEY_WITNESS][consts.KEY_TOKEN],
            self._configuration[consts.KEY_WITNESS][consts.KEY_VALUE_DICT],
            self._configuration[consts.KEY_WITNESS][consts.KEY_ANNOTATION],
            self._suite_dir,
            self._configuration[consts.KEY_PATH_TO_DEFS],
            self._configuration.get(consts.KEY_SKIP_FIELDS),
            self._configuration[consts.KEY_WITNESS][consts.KEY_PLOT_EVERY],
        )

        if self._configuration[consts.KEY_ANALYSIS][consts.KEY_PLOT_GRAPH]:
            engine.to_graph(endpoints, "dependencies_0")

        engine.saturate_all(
            endpoints, 
            self._configuration[consts.KEY_WITNESS][consts.KEY_ITERATIONS],
            self._configuration[consts.KEY_WITNESS][consts.KEY_TIMEOUT],
            self._configuration[consts.KEY_WITNESS][consts.KEY_MAX_OPT])

        # ascribe types with the new analysis results
        entries = utils.create_entries(
            doc_entries, self._configuration, ascription,
            not runtime_config.syntactic_only)

        print("Writing typed entries to file...")
        constructor = Constructor(self._doc, log_analyzer,
            not runtime_config.syntactic_only)
        with_syntactic = (
            runtime_config.uncovered_opt==consts.UncoveredOption.DEFAULT_TO_SYNTACTIC or
            runtime_config.syntactic_only) # generate semantic to syntactic conversion when syntactic types exist
        projs_and_filters = constructor.construct_graph(
            with_syntactic=with_syntactic,
            with_partials=runtime_config.with_partials,)
        entries.update(projs_and_filters)
        with open(os.path.join(self._suite_dir, consts.FILE_ENTRIES), "wb") as f:
            pickle.dump(entries, f)

        log_analyzer.index_values_by_type()
        print("Writing graph to file...")
        with open(os.path.join(self._suite_dir, consts.FILE_GRAPH), "wb") as f:
            pickle.dump(log_analyzer, f)

        if self._configuration[consts.KEY_ANALYSIS][consts.KEY_PLOT_GRAPH]:
            dot = Digraph(strict=True)
            log_analyzer.to_graph(dot, endpoints=endpoints)
            dot.render(os.path.join("output/", "dependencies"), view=False)

        print("---------------------------------------------------------------")

    def get_info(self):
        # to get number of annotations, open the annotations file
        ann_file = self._configuration[consts.KEY_WITNESS][consts.KEY_ANNOTATION]
        with open(ann_file, 'r') as af:
            a = json.load(af)
            annotations = len(a)

        # number of endpoint arguments
        num_args = [len(x.parameters) for x in self._typed_entries.values()]

        # number of object size
        obj_sizes = []
        schemas = self._doc.get(defs.DOC_COMPONENTS).get(defs.DOC_SCHEMAS)
        obj_num = len(schemas)
        for _, sch in schemas.items():
            typ = sch.get(defs.DOC_TYPE)
            if typ == defs.TYPE_OBJECT:
                if defs.DOC_PROPERTIES in sch:
                    properties = sch.get(defs.DOC_PROPERTIES)
                    if not properties:
                        continue

                    obj_sizes.append(len(properties))
                    continue

            obj_sizes.append(1)

        # number of endpoints
        endpoints = self._doc.get(defs.DOC_PATHS)
        ep_num = 0
        for ep in endpoints.values():
            ep_num += len(ep)

        # initial witnesses and coverage
        initial_witness_cnt = len(self._initial_witnesses)
        initial_covered = {
            (x.endpoint, x.method.upper()) for x in self._initial_witnesses if x.endpoint in endpoints
        }
        # print(initial_covered)
        initial_covered_num = len(initial_covered)

        not_covered_benches = 0
        for benchmark in self.benchmarks:
            ns = benchmark.solutions[0].collect_exprs()
            ep_calls = list(filter(lambda x: isinstance(x, AppExpr), ns))
            eps = [tuple(e._fun.split('_')) for e in ep_calls]
            eps = [('_'.join(e[:-1]), e[-1]) for e in eps]
            for ep in eps:
                if ep not in initial_covered:
                    print(ep, "is not covered")
                    not_covered_benches += 1
                    break

        print(self.api, "has", not_covered_benches, "benchmarks with not covered endpoints")

        # covered endpoints
        covered = set()
        
        for x in self._witnesses:
            if (x.endpoint in endpoints and 
                not isinstance(x.response, ErrorResponse) and 
                x.response.value):
                covered.add((x.endpoint, x.method.upper()))

        ep_covered = len(covered)

        # witnesses stats
        all_witnesses = [e for e in self._witnesses if not isinstance(e.response, ErrorResponse)]
        all_witness_cnt = len(all_witnesses)

        return APIInfo(
            self.api, num_args, obj_sizes, obj_num, ep_num, 
            initial_witness_cnt, initial_covered_num,
            all_witness_cnt - initial_witness_cnt,
            ep_covered, annotations)

    def get_popular_types(self):
        synthesizer = Synthesizer(self._configuration, self._typed_entries, None)
        synthesizer.init()
        parallel.run_encoder(synthesizer, {}, {}, 0, None)

    def run(self, runtime_config, names, cached_results=False):
        if runtime_config.witness_only:
            return None, None, None

        latex_entries = []
        places = None
        transitions = None
        
        indexed_entries = utils.index_entries(
            self._witnesses,
            self._configuration.get(consts.KEY_SKIP_FIELDS)
        )

        cache_path = os.path.join(self._iter_dir, "bench_results.pkl")
        if cached_results:
            with open(cache_path, "rb") as f:
                d = pickle.load(f)

            places = d["places"]
            transitions = d["transitions"]
            latex_entries = d["results"]

            print("places", places)
            print("transitions", transitions)
            # update the solution sizes
            # for i, e in enumerate(latex_entries):
            #     e.ast_size = len(self.benchmarks[i].solutions[0].collect_exprs())
            #     # print(self.benchmarks[i].solutions[0])
            #     # print(e.ast_size)

            # with open(cache_path, "wb") as f:
            #     pickle.dump({
            #         "places": places,
            #         "transitions": transitions,
            #         "results": latex_entries,
            #     }, f)
        else:
            places = None
            transitions = None
            for benchmark in self.benchmarks:
                if names is not None and benchmark.name not in names:
                    continue

                bench_places, bench_transitions, path_cnt, solutions = benchmark.run(
                    self._iter_dir, 
                    self._typed_entries,
                    indexed_entries, 
                    self._configuration,
                    self._log_analyzer,
                    runtime_config
                )

                if bench_places is not None and places is None:
                    places = bench_places

                if bench_transitions is not None and transitions is None:
                    transitions = bench_transitions

                if not runtime_config.synthesis_only:
                    flat_solutions = []
                    for sol in solutions:
                        flat_solutions += sol

                    flat_solutions = list({s[1]:s for s in flat_solutions}.values())
                    latex_entry = benchmark.to_latex_entry(path_cnt, flat_solutions)
                    latex_entries.append(latex_entry)


            with open(cache_path, "wb") as f:
                pickle.dump({
                    "places": places,
                    "transitions": transitions,
                    "results": latex_entries,
                }, f)

        return latex_entries, places, transitions

class Bencher:
    def __init__(self, exp_name, suites, config):
        self._exp_name = exp_name
        self._suites = suites
        self._config = config

    def run(self, data_dir, suites, names,
        cached_results=False, 
        print_api=False, 
        print_results=False, 
        print_appendix=False, 
        print_small=False,
        plot_ranks=False, 
        output=None):
        place_counts = []
        trans_counts = []
        benchmark_results = []

        if print_appendix:
            self.print_appendix(output)
        
        exp_dir = os.path.join(data_dir, self._exp_name)
        # copy trace files before actual runs
        if not os.path.exists(exp_dir):
            os.makedirs(exp_dir)
        
        for api in consts.APIS:
            src_file = os.path.join(
                "../", 
                consts.DATA_DEFAULT, 
                consts.EXP_DEFAULT,
                api,
                consts.FILE_TRACE)
            dst_dir = os.path.join(exp_dir, api)
            if not os.path.exists(dst_dir):
                os.makedirs(dst_dir)
                dst_file = os.path.join(dst_dir, consts.FILE_TRACE)
                shutil.copy(src_file, dst_file)

        for suite in self._suites:
            if suites is not None and suites != [] and suite.api not in suites:
                continue

            suite.prep(data_dir, self._exp_name, self._config)
            if self._config.get_place_stats:
                suite.get_popular_types()
            else:
                benchmark_entries, places, transitions = suite.run(
                    self._config, names, cached_results)
                place_counts.append(places)
                trans_counts.append(transitions)
                benchmark_results.append(benchmark_entries)

        # set to False to disable this step for further runnings
        self._config.generate_witness = abs(self._config.method_coverage - 1.0) > 1e-6

        if print_api:
            self.print_api_info(place_counts, trans_counts, print_small, output)

        if print_results:
            self.print_benchmark_results(benchmark_results, output)

        if plot_ranks:
            self.plot_ranks(benchmark_results, output)

    def print_api_info(self, places, transitions, small=False, output=None):
        if small:
            res = (
            "\\small\\begin{tabular}{l|rrrr|rr}\n"
            "\\toprule\n"
            "& \\multicolumn{4}{c|}{API size} & \\multicolumn{2}{c}{API Analysis} \\\\\n"
            "\\cmidrule(lr){2-5} \\cmidrule(lr){6-7} \n"
            "API & $|\\Lambda.f|$ & $n_{args}$ & $|\\Lambda.o|$ & $s_{objs}$ & $|\\witnesses|$ & $n_{cov}$ \\\\\n"
            "\\midrule\n")
        else:
            res = (
                "\\small\\begin{tabular}{l|rrrr|rr|rr}\n"
                "\\toprule\n"
                "& \\multicolumn{4}{c|}{API size} & \\multicolumn{2}{c|}{API Analysis} & \\multicolumn{2}{c}{TTN size} \\\\\n"
                "\\cmidrule(lr){2-5} \\cmidrule(lr){6-7} \\cmidrule(lr){8-9}\n"
                "API & $|\\Lambda.f|$ & $n_{args}$ & $|\\Lambda.o|$ & $s_{objs}$ & $|\\witnesses|$ & $n_{cov}$ & $|P|$ & $|T|$ \\\\\n"
                "\\midrule\n")
        res += "\n"

        for i, suite in enumerate(self._suites):
            if places[i] is not None:
                api_info = suite.get_info()
                # avg_num_args = round(api_info.avg_num_args, 2)
                # obj_size = round(api_info.obj_size, 2)
                res += (f"  \\{api_info.api_name} "
                    f"& {api_info.ep_num} "
                    f"& {min(api_info.num_args)} - {max(api_info.num_args)} "
                    f"& {api_info.obj_num} "
                    f"& {min(api_info.obj_sizes)} - {max(api_info.obj_sizes)} "
                    f"& {api_info.gen_w} "
                    f"& {api_info.ep_covered} ")
                
                if not small:
                    res += (
                        f"& {places[i]} "
                        f"& {transitions[i]}")
                
                res += r" \\"
                res += "\n"

        res += ("\\bottomrule"
                "\\end{tabular}")

        # print(res)

        if output:
            with open(os.path.join(output, "api_info.tex"), "w") as of:
                of.write(res)
                print(f"written to {os.path.join(output, 'api_info.tex')}")

    def print_appendix(self, output=None):
        res = ("% auto-generated: ./bench.py, type queries and solutions\n"
               "\\section{Type Queries and Solutions}\\label{appendix:solutions}\n\n"
               "This section includes type queries and ``gold standard'' solutions for "
               "all the tested benchmarks. Additionally, the type queries used here "
               "correspond directly to the OpenAPI spec of the corresponding API; "
               "in the paper, these queries are simplified for readability.\n\n"
               # TODO: hmm
               "\\setlength{\parindent}{0pt}\n\n")

        for suite in self._suites:
            res += f"\\subsection{{\\{suite.api}}}\n"

            for bench in suite.benchmarks:
                res += f"\\textbf{{{bench.name}. {bench.description}}}\n\n"

                # Input to output
                input_vals = ',\n  '.join([f"{k}: {v}" for k, v in bench.inputs.items()])
                output_val = bench.output
                newline = '\n'
                res += ("Type query: "
                        "\\begin{lstlisting}[style=dsl,basicstyle=\\ttfamily\\footnotesize,xleftmargin=5pt,breaklines=true,postbreak=\\mbox{\\textcolor{red}{$\\hookrightarrow$}\\space}]\n"
                        f"{{ {input_vals} {newline if ',' in input_vals else ''}}} -> {output_val}"
                        "\n\n\\end{lstlisting}\n\n")
                
                # Target solution
                res += ("Solution:\n"
                        "\\begin{lstlisting}[style=dsl,basicstyle=\\ttfamily\\footnotesize,xleftmargin=5pt,breaklines=true,postbreak=\\mbox{\\textcolor{red}{$\\hookrightarrow$}\\space}]\n"
                        f"{bench.solutions[0]}\n"
                        "\\end{lstlisting}\n\n")

                # Source
                if bench.source:
                    res += ("\\vspace{-0.25em}{\\footnotesize Source: \\url{"
                            f"{bench.source}"
                            "}\n\n")
                    
                res += "\\vspace{1em}\n\n"

        if output:
            with open(os.path.join(output, "solutions.tex"), "w") as of:
                of.write(res)
                print(f"written to {os.path.join(output, 'solutions.tex')}")
