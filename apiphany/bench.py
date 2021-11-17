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
import enum
import matplotlib.pyplot as plt
import os
import pickle
import math
import cProfile
from matplotlib.ticker import (AutoMinorLocator)
import scipy.stats as st

from analyzer import dynamic
from benchmarks.benchmark import BenchConfig, Bencher, BenchmarkResult
from benchmarks.suites import slack_suite, stripe_suite, square_suite
from benchmarks import utils
import consts

bias_type_args = {
    "none": dynamic.BiasType.NONE,
    "simple": dynamic.BiasType.SIMPLE,
    "look-ahead": dynamic.BiasType.LOOK_AHEAD
}

class Ablation(enum.Enum):
    APIPHANY = "apiphany"
    NOSEMANTIC = "apiphany-no-semantic"
    NORE = "apiphany-no-re"

def build_cmd_parser():
    '''
        All arguments
    '''
    parser = argparse.ArgumentParser()
    
    # general commands
    parser.add_argument("output", nargs='?',
        help="Path to output latex table to")
    parser.add_argument("--data-dir", required=True,
        help="Path to data directory")
    parser.add_argument("--exp-name",
        help="Experiment name")
    parser.add_argument("--suites", nargs="+",
        choices=["slack", "stripe", "squareapi"],
        help="Benchmark suite to run. If used together with `--benchmark`, only benchmarks in selected suites will be run")
    parser.add_argument("--benchmarks", nargs="+",
        help="Benchmark name list")
    parser.add_argument("--repeat-exp", default=3, type=int,
        help="Number of times to repeat each experiment")

    # witness generation
    parser.add_argument("--generate-witness-only", action="store_true",
        help="Only generate witness files")
    parser.add_argument("--generate-witness", action="store_true",
        help="Whether to generate witness")
    parser.add_argument("--syntactic-only", action="store_true",
        help="Whether to not infer any semantic types.")
    parser.add_argument("--method-coverage", type=float,
        help="Prune methods and witnesses to get the target coverage")
    parser.add_argument("--with-partials", action='store_true',
        help="Whether to include partial object constructions")
    parser.add_argument("--no-merge", action='store_true',
        help="Whether to merge locations")
    parser.add_argument("--uncovered", type=consts.UncoveredOption,
        choices=list(consts.UncoveredOption),
        default=consts.UncoveredOption.EXCLUDE,
        help="Different options to deal with uncovered methods")

    # synthesis options
    parser.add_argument("--synthesis-only", action='store_true',
        help="Whether to run ranking")
    parser.add_argument("--conversion-fair", action='store_true',
        help="Whether to treat conversion transitions fair")
    parser.add_argument("--primitive-as-return", action='store_true',
        help="Whether to allow programs return primitive types when semantic types not found")
    
    # retrospective execution options
    parser.add_argument("--repeat-re", type=int, nargs='?',
        help="Number of times to repeat retrospective execution")
    parser.add_argument("--bias-type", default='simple',
        choices=list(bias_type_args.keys()) ,dest='bias_type',
        help="Bias type for retrospective execution")
    parser.add_argument("--cache", action='store_true', dest='cache',
        help="Whether to use cached results")
    parser.add_argument("--parallel", action='store_true', dest='parallel',
        help="Whether to run in parallel")
    parser.add_argument("--sol-only", action='store_true', dest='filter_sol_only',
        help="Whether to run retrospective execution on the solution only")
    parser.add_argument("--get-place-stats", action='store_true',
        help="Whether to get place stats")
    
    # plotting options
    parser.add_argument("--print-results",
        help="Whether to print results.tex for the given exp name")
    parser.add_argument("--print-api-info", action="store_true",
        help="Whether to print api info")
    parser.add_argument("--print-small", action="store_true",
        help="Whether to print small tables")
    parser.add_argument("--print-appendix", action="store_true",
        help="Whether to print appendix")
    parser.add_argument("--plot-all", nargs='+',
        help="Whether to plot all available charts for given experiments")
    parser.add_argument("--plot-solved", nargs='*',
        help="Whether to plot how many benchmarks are solved vs time for given experiments")
    parser.add_argument("--plot-ranks", nargs='*',
        help="Whether to plot rank vs time for given experiments")

    # default values
    parser.set_defaults(
        repeat_re=15,
        filter_sol_only=False,
        syntactic_only=False,
        generate_witness_only=False,
        generate_witness=False,
        method_coverage=1.0,
        conversion_fair=False,
        primitive_as_return=False,
        print_api_info=False,
        print_appendix=False,
        cache=False)
    return parser



def load_exp_results(data_dir, exp_name, repeat_exp=3):
    all_entries = {}
    
    for api in consts.APIS:
        api_dir = os.path.join(data_dir, exp_name, api, "iter_0")
        if not os.path.exists(api_dir):
            continue

        latex_entries = None
        for i in range(repeat_exp):
            cache_path = os.path.join(
                data_dir, exp_name, api, f"iter_{i}", consts.FILE_RESULTS)
            if os.path.exists(cache_path):
                print("Loading", cache_path)
                with open(cache_path, "rb") as f:
                    d = pickle.load(f)

                if latex_entries is None:
                    latex_entries = [[] for _ in range(len(d["results"]))]

                for j, res in enumerate(d["results"]):
                    latex_entries[j].append(res)

        entries = []
        for reps in latex_entries:
            entry = reps[0]
            entry.syn_time = [rep.syn_time for rep in reps if rep.syn_time is not None]
            entry.re_time = [rep.re_time for rep in reps if rep.re_time is not None]
            ranks = [rep.ranks[0] for rep in reps if rep.ranks is not None]
            entry.ranks = ranks if ranks else None
            entry.rank_no_re = [rep.rank_no_re for rep in reps if rep.rank_no_re is not None]
            rank_before_sol = [rep.rank_before_sol for rep in reps if rep.rank_before_sol is not None]
            entry.rank_before_sol = rank_before_sol if rank_before_sol else None
            rank_no_re_before_sol = [rep.rank_no_re_before_sol for rep in reps if rep.rank_no_re_before_sol is not None]
            entry.rank_no_re_before_sol = rank_no_re_before_sol if rank_no_re_before_sol else None
            entries.append(entry)

        all_entries[api] = entries

    # print(all_entries)
    return all_entries

def compute_confidence_interval(xs, alpha, f):
    # confidence=0.99
    # compute confidence interval for a list of numbers
    # https://stackoverflow.com/questions/15033511/compute-a-confidence-interval-from-sample-data
    # print(xs)
    n = len(xs)
    mean = sum(xs) / n
    std = math.sqrt(sum((x - mean)**2 for x in xs) / n)
    z_score = st.t.ppf(alpha, n - 1)
    h = z_score * std / math.sqrt(n)
    return f(xs), max(0, mean - h), mean + h

def plot_with_intervals(ax, xs, ys, **kwargs):
    means = [x[0] for x in xs]
    errors = [[min(x[0], x[1]) for x in xs], [x[1] for x in xs]]
    lefts = [max(0, x[0] - x[1]) for x in xs]
    rights = [x[0] + x[1] for x in xs]
    ax.plot(means, ys, **kwargs)
    
    ax.fill_betweenx(ys, sorted(lefts), sorted(rights), alpha=.25)


def plot_ranks(experiments, data_dir, repeat_exp=1, output=None):
    # load results for all experiments
    for exp in experiments:
        api_results = load_exp_results(data_dir, exp, repeat_exp)
        results = []
        for r in api_results.values():
            results += r

        ranks_re = []
        ranks_no_re = []
        ranks_re_before_sol = []
        ranks_no_re_before_sol = []
        for result in results:
            if result is None or result.ranks is None:
                continue

            ranks_re.append(compute_confidence_interval(result.ranks, 0.975, utils.median))
            ranks_no_re.append(compute_confidence_interval(result.rank_no_re, 0.975, utils.median))
            ranks_re_before_sol.append(compute_confidence_interval(result.rank_before_sol, 0.975, utils.median))
            ranks_no_re_before_sol.append(compute_confidence_interval(result.rank_no_re_before_sol, 0.975, utils.median))
    
        cnt_ranks_re = [sum([1 for x in ranks_re if x[0] <= i]) for i in range(0,50000)]
        cnt_ranks_re_high = [sum([1 for x in ranks_re if max(x[1], 0) <= i]) for i in range(0,50000)]
        cnt_ranks_re_low = [sum([1 for x in ranks_re if x[2] <= i]) for i in range(0,50000)]
        cnt_ranks_no_re = [sum([1 for x in ranks_no_re if x[0] <= i]) for i in range(0,50000)]
        cnt_ranks_no_re_high = [sum([1 for x in ranks_no_re if max(x[1], 0) <= i]) for i in range(0,50000)]
        cnt_ranks_no_re_low = [sum([1 for x in ranks_no_re if x[2] <= i]) for i in range(0,50000)]
        cnt_ranks_re_before_sol = [sum([1 for x in ranks_re_before_sol if x[0] <= i]) for i in range(0,50000)]
        cnt_ranks_re_before_sol_high = [sum([1 for x in ranks_re_before_sol if max(x[1], 0) <= i]) for i in range(0,50000)]
        cnt_ranks_re_before_sol_low = [sum([1 for x in ranks_re_before_sol if x[2] <= i]) for i in range(0,50000)]
        cnt_ranks_no_re_before_sol = [sum([1 for x in ranks_no_re_before_sol if x[0] <= i]) for i in range(0,50000)]
        cnt_ranks_no_re_before_sol_high = [sum([1 for x in ranks_no_re_before_sol if max(x[1], 0) <= i]) for i in range(0,50000)]
        cnt_ranks_no_re_before_sol_low = [sum([1 for x in ranks_no_re_before_sol if x[2] <= i]) for i in range(0,50000)]
        # print(ranks_no_re)

        # plot core data
        fig, (ax1, ax2) = plt.subplots(1, 2, sharey=True, figsize=(4,2.5))
        

        ymax = math.ceil(consts.TOTAL_BENCHMARKS / 2.) * 2 + 1
        # ys = list(range(0, len(ranks_re) + 1)) + [len(ranks_re)]
        # re_xs = [0] + sorted([x[0] for x in ranks_re]) + [50001]
        # re_high = [0] + sorted([x[1] for x in ranks_re])+ [50001]
        # re_low = [0] + sorted([x[2] for x in ranks_re])+ [50001]
        # no_re_xs = [0] + sorted([x[0] for x in ranks_no_re]) + [50001]
        # no_re_high = [0] + sorted([x[1] for x in ranks_no_re])+ [50001]
        # no_re_low = [0] + sorted([x[2] for x in ranks_no_re])+ [50001]
        ax1.set_xlim(0, 15)
        ax2.set_xscale('log')
        ax2.set_xlim(15, 50000)
        ax1.set_ylim(0, ymax)
        ax1.set_xlabel("Rank", loc="right")
        ax1.set_ylabel("# benchmarks")
        # ax1.yaxis.set_minor_locator(AutoMinorLocator())
        # ax1.xaxis.set_minor_locator(AutoMinorLocator())
        # ax2.yaxis.set_minor_locator(AutoMinorLocator())
        # ax2.xaxis.set_minor_locator(AutoMinorLocator())
        ax1.yaxis.set_ticks(list(range(0,ymax+1,5)) + [consts.TOTAL_BENCHMARKS])
        ax1.xaxis.set_ticks([0,5,10,15])
        # ax1.plot(re_xs, ys, label="w/ RE")
        # ax1.fill_betweenx(ys, re_low, re_high, alpha=.25)
        # ax1.plot(no_re_xs, ys, label="w/o RE")
        # ax1.fill_betweenx(ys, no_re_low, no_re_high, alpha=.25)
        # ax2.plot(re_xs, ys, label="w/ RE")
        # ax2.fill_betweenx(ys, re_low, re_high, alpha=.25)
        # ax2.plot(no_re_xs, ys, label="w/o RE")
        # ax2.fill_betweenx(ys, no_re_low, no_re_high, alpha=.25)

        # ax1.plot(cnt_ranks_re, label="w/ RE", color="#1f77b4")
        ax1.fill_between(range(0,50000), cnt_ranks_re_before_sol_high, cnt_ranks_re_low, alpha=.25)
        # ax1.plot(cnt_ranks_re_before_sol, label="w/ RE before solution", color="#1f77b4")
        ax1.fill_between(range(0,50000), cnt_ranks_re, cnt_ranks_re_before_sol, alpha=1, color="#1f77b4")
        # dummy plots to get the next color
        ax1.plot([0])
        ax1.plot([0])
        ax1.fill_between([0],[0],[0])
        ax1.plot([0])
        ax1.fill_between([0],[0],[0])
        #
        # ax1.plot(cnt_ranks_no_re, label="w/o RE")
        # ax1.fill_between(range(0,50000), cnt_ranks_no_re, cnt_ranks_no_re_before_sol, alpha=1, color="#d62728")
        ax1.plot(cnt_ranks_no_re_before_sol, label="w/o RE")
        ax1.fill_between(range(0,50000), cnt_ranks_no_re_before_sol_high, cnt_ranks_no_re_before_sol_low, alpha=.25)

        ax2.plot(cnt_ranks_re, label="w/ RE", color="#1f77b4")
        ax2.fill_between(range(0,50000), cnt_ranks_re_before_sol_low, cnt_ranks_re_high, alpha=.25)
        # ax2.plot(cnt_ranks_re_before_sol, label="w/ RE before solution", color="#1f77b4")
        ax2.fill_between(range(0,50000), cnt_ranks_re, cnt_ranks_re_before_sol, alpha=1, color="#1f77b4")
        # dummy plots to get the next color
        ax2.plot([0])
        ax2.plot([0])
        ax2.fill_between([0],[0],[0])
        ax2.plot([0])
        ax2.fill_between([0],[0],[0])
        #
        ax2.plot(cnt_ranks_no_re_before_sol, label="w/o RE")
        # ax2.fill_between(range(0,50000), cnt_ranks_no_re, cnt_ranks_no_re_before_sol, alpha=1, color="#d62728")
        ax2.fill_between(range(0,50000), cnt_ranks_no_re_before_sol_low, cnt_ranks_no_re_before_sol_high, alpha=.25)

        ax1.hlines(consts.TOTAL_BENCHMARKS, 0, 20, linestyles='dashed', label="max #benchmarks", colors="0.8")
        ax2.hlines(consts.TOTAL_BENCHMARKS, 20, 50000, linestyles='dashed', label="max #benchmarks", colors="0.8")
        ax2.legend(loc="best")

        # set border lines
        ax1.spines.right.set_visible(False)
        ax2.spines.left.set_visible(False)
        ax1.yaxis.tick_left()
        ax2.yaxis.tick_right()
        ax2.tick_params(labelright=False)

        # plot break lines
        d = .5  # proportion of vertical to horizontal extent of the slanted line
        kwargs = dict(marker=[(-d, -1), (d, 1)], markersize=5,
                    linestyle="none", color='k', mec='k', mew=1, clip_on=False)
        ax2.plot([0, 0], [0, 1], transform=ax2.transAxes, **kwargs)
        ax1.plot([1, 1], [0, 1], transform=ax1.transAxes, **kwargs)


        # plt.show()
        if output:
            output_path = os.path.join(output, f"{exp}_ranks.png")
        else:
            output_path = "ranks.png"

        plt.tight_layout()
        fig.subplots_adjust(wspace=0.05)  # adjust space between axes

        plt.savefig(output_path)

def plot_solved(experiments, data_dir, repeat_exp=1, output=None):
    # load results for all experiments
    times_dict = {}
    for exp in experiments:
        api_results = load_exp_results(data_dir, exp, repeat_exp)
        times = []
        for results in api_results.values():
            for result in results:
                if result is None or result.ranks is None:
                    continue

                m, l, h = compute_confidence_interval(result.syn_time, 0.975, utils.avg)
                times.append((m, l, h))

        times_dict[exp] = sorted(times, key=lambda x: x[0])

    # plot core data
    fig, ax = plt.subplots(1, 1, figsize=(4, 2.5))
    # ax.grid()
    ymax = math.ceil(consts.TOTAL_BENCHMARKS / 2.) * 2 + 1
    ax.set_ylim(0, ymax)
    ax.set_xlim(-4, consts.TIMEOUT)
    ax.yaxis.set_ticks(list(range(0, ymax, 5)) + [consts.TOTAL_BENCHMARKS])
    ax.yaxis.set_minor_locator(AutoMinorLocator())
    ax.xaxis.set_minor_locator(AutoMinorLocator())
    ax.set_xlabel("Time (s)")
    ax.set_ylabel("# solved benchmarks")

    markers = ["x", "o", "v", "+", "*"]
    # colors = ["#fc8d62", "#8da0cb"]
    label_mapping = {
        "apiphany": "APIphany",
        "apiphany_repeat": "APIphany",
        "apiphany_full_timeout": "APIphany",
        "apiphany_no_semantic": "APIphany-NoSemantic",
        "apiphany_no_merge": "APIphany-NoMerge",
    }
    for i, (exp, xs) in enumerate(times_dict.items()):
        ys = list(range(1, len(xs)+1))
        label = label_mapping.get(exp, exp)
        means = [x[0] for x in xs] + [consts.TIMEOUT + 10]
        lefts = [x[1] for x in xs] + [consts.TIMEOUT + 10]
        rights = [x[2] for x in xs] + [consts.TIMEOUT + 10]
        ys += ys[-1:]
        ax.plot(means, ys, label=label, marker=markers[i], markersize=5)
        ax.fill_betweenx(ys, sorted(lefts), sorted(rights), alpha=.25)

    ax.axhline(y=consts.TOTAL_BENCHMARKS, linestyle='dashed', label="max #benchmarks", color="0.8")
    ax.legend(loc="best")
    plt.tight_layout()
    plt.savefig(os.path.join(output, "solved.png"))

def print_benchmark_results(suites, results, output=None, small=False):
    if small:
        res = ("% auto-generated: ./bench.py, table 2\n"
            "\\begin{tabular}{c|l|rrrr|r|rrr}\n"
            "\\toprule\n"
            "\\multirow{2}{*}{API} & \\multirow{2}{*}{ID} & \\multicolumn{4}{c|}{Solution Size} & \\multicolumn{1}{c|}{Time} & \\multicolumn{3}{c}{Rank} \\\\\n"
            "\\cmidrule(lr){3-6} \\cmidrule(lr){8-10} \n"
            " &  & AST & $n_{f}$ & $n_{p}$ & $n_{g}$ & (sec) & $r_{orig}$ & $r_{RE}$ & $r_{RE}^{TO}$ \\\\\n"
            "\\midrule")
        res += "\n"
    else:
        res = ("% auto-generated: ./bench.py, table 2\n"
                "\\begin{tabular}{l|lp{6.5cm}|rrrr|rr|rrrr}\n"
                "\\toprule\n"
                "\\multirow{2}{*}{API} & \\multicolumn{2}{c|}{Benchmark} & \\multicolumn{4}{c|}{Solution Size} & \\multicolumn{2}{c|}{Timing} & \\multicolumn{4}{c}{Rank} \\\\\n"
                "\\cmidrule(lr){2-3} \\cmidrule(lr){4-7} \\cmidrule(lr){8-9} \\cmidrule(lr){10-13} \n"
                " & ID & Description & AST & $n_{f}$ & $n_{p}$ & $n_{g}$ & $t_{Total}$ & $t_{RE}$ & $r_{orig}$ & $r_{RE}$ & $\\#$ cands & $r_{RE}^{TO}$ \\\\\n"
                "\\midrule")
        res += "\n"

    for i, (api, bench_results) in enumerate(results.items()):
        res += f"\\multirow{{{len(bench_results)}}}{{*}}{{\\rotatebox{{90}}{{\\{consts.APIS_LATEX[i]}}}}} "
        suite = suites[i]
        for j, r in enumerate(bench_results):
            bench = suite.benchmarks[j]

            if r is None:
                continue

            # print(r.name, r.ranks)
            ranks = r.ranks
            if ranks is None:
                median_rank = None
            else:
                median_rank = utils.median(ranks)
            
            if not r.rank_no_re:
                rank_no_re = None
            else:
                rank_no_re = utils.median(r.rank_no_re)
            # if r.rank_no_re_rng is None:
            #     rank_no_re = None
            # else:
            #     rank_no_re = f"{r.rank_no_re_rng[0]}-{r.rank_no_re_rng[1]}"
            
            if median_rank is not None:
                if not small and median_rank <= rank_no_re:
                    median_rank_str = f"{median_rank}"
                else:
                    median_rank_str = str(median_rank)

                if not small and rank_no_re <= median_rank:
                    rank_no_re_str = f"{rank_no_re}"
                else:
                    rank_no_re_str = str(rank_no_re)
            else:
                median_rank_str = utils.pretty_none(median_rank)
                rank_no_re_str = utils.pretty_none(rank_no_re)

            if r.rank_no_re_before_sol:
                rank_no_re_before_sol_str = utils.median(r.rank_no_re_before_sol)
                rank_before_sol_str = utils.median(r.rank_before_sol)
            else:
                rank_no_re_before_sol_str = utils.pretty_none(r.rank_no_re_before_sol)
                rank_before_sol_str = utils.pretty_none(r.rank_before_sol)
            
            # print(r.name, r.rank_before_sol, r.ranks)

            dagger = '$^{\\dagger}$'
            if small:
                res += (
                    f"& {r.name}{dagger if bench.is_effectful else ''} "
                    f"& {utils.pretty_none(r.ast_size)} "
                    f"& {utils.pretty_none(r.endpoint_calls)} "
                    f"& {utils.pretty_none(r.projects)} "
                    f"& {utils.pretty_none(r.filters)} "
                    f"& {utils.pretty_none(utils.avg(r.syn_time))} "
                    f"& {rank_no_re_before_sol_str} "
                    f"& {rank_before_sol_str} "
                    f"& {median_rank_str} "
                    )
            else:
                res += (
                    f"& {r.name}{dagger if bench.is_effectful else ''} "
                    f"& {bench.description} "
                    f"& {utils.pretty_none(r.ast_size)} "
                    f"& {utils.pretty_none(r.endpoint_calls)} "
                    f"& {utils.pretty_none(r.projects)} "
                    f"& {utils.pretty_none(r.filters)} "
                    f"& {utils.pretty_none(utils.avg(r.syn_time))} "
                    f"& {utils.pretty_none(utils.avg(r.re_time))} "
                    f"& {rank_no_re_before_sol_str}"
                    f"& {rank_before_sol_str}"
                    f"& {rank_no_re_str} "
                    f"& {median_rank_str} ")

            res += r" \\"
            res += "\n"
        if i < len(results) - 1:
            res += "\\hline\n"

    res += ("\\bottomrule"
            "\\end{tabular}")

    # print(res)

    if output:
        filename = "results_short.tex" if small else "results.tex"
        with open(os.path.join(output, filename), "w") as of:
            of.write(res)
            print(f"written to {filename}")

def main():
    cmd_parser = build_cmd_parser()
    args = cmd_parser.parse_args()

    plt.rcParams.update({'font.size': 8})

    suites = [
        slack_suite,
        stripe_suite,
        square_suite,
    ]

    if args.print_results:
        results = load_exp_results(args.data_dir, args.print_results, args.repeat_exp)
        print_benchmark_results(suites, results, args.output, small=args.print_small)
        return

    if args.plot_all or args.plot_solved:
        experiments = args.plot_all
        if experiments is None:
            experiments = args.plot_solved

        plot_solved(experiments, args.data_dir, args.repeat_exp, args.output)

    if args.plot_all or args.plot_ranks:
        experiments = args.plot_all
        if experiments is None:
            experiments = args.plot_ranks

        plot_ranks(experiments, args.data_dir, args.repeat_exp, args.output)

    if (not args.plot_all and
        not args.plot_solved and
        not args.plot_ranks):
        if args.exp_name is None:
            raise Exception("You have to provide a valid experiment name first.")
            
        config = BenchConfig(
            cache=args.cache,
            repeat_exp=args.repeat_exp,
            repeat_re=args.repeat_re,
            filter_sol_only=args.filter_sol_only,
            synthesis_only=args.synthesis_only,
            witness_only=args.generate_witness_only,
            bias_type=bias_type_args[args.bias_type],
            use_parallel=args.parallel,
            get_place_stats=args.get_place_stats,
            generate_witness=args.generate_witness,
            method_coverage=args.method_coverage,
            uncovered_opt=args.uncovered,
            conversion_fair=args.conversion_fair,
            prim_as_return=args.primitive_as_return,
            syntactic_only=args.syntactic_only,
            with_partials=args.with_partials,
            no_merge=args.no_merge,
        )
        b = Bencher(args.exp_name, suites, config)

        if args.generate_witness_only:
            rep = 1
        else:
            rep = args.repeat_exp

        # with cProfile.Profile() as p:
        print("***********************************************************")
        print(f"Running experiment...")

        b.run(
            args.data_dir,
            args.suites,
            args.benchmarks,
            output=args.output,
            print_api=args.print_api_info,
            print_results=args.print_results,
            print_appendix=args.print_appendix,
            print_small=args.print_small,
            plot_ranks=False,
            cached_results=args.cache)

        # p.print_stats()
        print(f"Experiment completed")
        print("***********************************************************")

if __name__ == '__main__':
    main()
