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
from matplotlib.ticker import (MultipleLocator, AutoMinorLocator)

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
    parser.add_argument("--print-results", action="store_true",
        help="Whether to print results.tex")
    parser.add_argument("--print-api-info", action="store_true",
        help="Whether to print api info")
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
        print_results=False,
        print_api_info=False,
        cache=False)
    return parser



def load_exp_results(data_dir, exp_name, repeat_exp=3):
    all_entries = []
    
    for api in consts.APIS:
        api_dir = os.path.join(data_dir, exp_name, api, "iter_0")
        if not os.path.exists(api_dir):
            continue

        latex_entries = None
        for i in range(repeat_exp):
            cache_path = os.path.join(
                data_dir, exp_name, api, f"iter_{i}", consts.FILE_RESULTS)
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
            entry.syn_time = utils.avg([rep.syn_time for rep in reps if rep.syn_time is not None])
            entry.re_time = utils.avg([rep.re_time for rep in reps if rep.re_time is not None])
            ranks = [rep.ranks[0] for rep in reps if rep.ranks is not None]
            entry.ranks = ranks if ranks else None
            entries.append(entry)

        all_entries += entries

    # print(all_entries)
    return all_entries
    

def plot_ranks(experiments, data_dir, output=None):
    # load results for all experiments
    for exp in experiments:
        results = load_exp_results(data_dir, exp, 1)
        ranks_re = []
        ranks_no_re = []
        for result in results:
            if result is None or result.ranks is None:
                continue

            ranks_re.append(utils.median(result.ranks))
            ranks_no_re.append(result.rank_no_re)
    
        cnt_ranks_re = [sum([1 for x in ranks_re if x <= i]) for i in range(0,50000)]
        cnt_ranks_no_re = [sum([1 for x in ranks_no_re if x <= i]) for i in range(0,50000)]

        # plot core data
        fig, (ax1, ax2) = plt.subplots(1, 2, sharey=True)
        fig.subplots_adjust(wspace=0.05)  # adjust space between axes

        ymax = math.ceil(consts.TOTAL_BENCHMARKS / 2.) * 2 + 1
        ax1.set_xlim(0, 15)
        ax2.set_xscale('log')
        ax2.set_xlim(15, 50000)
        ax1.set_ylim(0, ymax)
        ax1.set_xlabel("Rank", loc="right")
        ax1.set_ylabel("# benchmarks")
        ax1.yaxis.set_ticks(range(0,ymax+1,2))
        ax1.xaxis.set_ticks([0,3,6,9,10,12,15])
        # ax1.plot(cnt_ranks_re, label="w/ RE", color="#fc8d62", marker="^", markevery=ranks_re)
        # ax1.plot(cnt_ranks_no_re, label="w/o RE", color="#8da0cb", marker="d", markevery=ranks_no_re)
        # ax2.plot(cnt_ranks_re, label="w/ RE", color="#fc8d62", marker="^", markevery=ranks_re)
        # ax2.plot(cnt_ranks_no_re, label="w/o RE", color="#8da0cb", marker="d", markevery=ranks_no_re)
        ax1.plot(cnt_ranks_re, label="w/ RE", color="#fc8d62")
        ax1.plot(cnt_ranks_no_re, label="w/o RE", color="#8da0cb")
        ax2.plot(cnt_ranks_re, label="w/ RE", color="#fc8d62")
        ax2.plot(cnt_ranks_no_re, label="w/o RE", color="#8da0cb")
        ax1.hlines(consts.TOTAL_BENCHMARKS, 0, 15, linestyles='dashed', label="max solved benchmarks", colors="0.8")
        ax2.hlines(consts.TOTAL_BENCHMARKS, 15, 50000, linestyles='dashed', label="max solved benchmarks", colors="0.8")
        ax2.legend(loc="best")

        # set border lines
        ax1.spines.right.set_visible(False)
        ax2.spines.left.set_visible(False)
        ax1.yaxis.tick_left()
        ax2.yaxis.tick_right()
        ax2.tick_params(labelright=False)

        # plot break lines
        d = .5  # proportion of vertical to horizontal extent of the slanted line
        kwargs = dict(marker=[(-d, -1), (d, 1)], markersize=12,
                    linestyle="none", color='k', mec='k', mew=1, clip_on=False)
        ax2.plot([0, 0], [0, 1], transform=ax2.transAxes, **kwargs)
        ax1.plot([1, 1], [0, 1], transform=ax1.transAxes, **kwargs)


        # plt.show()
        if output:
            output_path = os.path.join(output, f"{exp}_ranks.png")
        else:
            output_path = "ranks.png"

        plt.savefig(output_path)

def plot_solved(experiments, data_dir, output=None):
    # load results for all experiments
    times_dict = {}
    for exp in experiments:
        results = load_exp_results(data_dir, exp, 1)
        times = []
        for result in results:
            if result is None or result.ranks is None:
                continue

            times.append(result.syn_time)

        times_dict[exp] = sorted(times)

    # plot core data
    fig, ax = plt.subplots(1, 1)
    ymax = math.ceil(consts.TOTAL_BENCHMARKS / 2.) * 2 + 1
    ax.set_ylim(0, ymax)
    ax.set_xlim(0, consts.TIMEOUT)
    # ax.set_xscale('log')
    ax.yaxis.set_ticks(range(0,ymax+1,5))
    ax.yaxis.set_minor_locator(AutoMinorLocator())
    ax.xaxis.set_minor_locator(AutoMinorLocator())
    ax.set_xlabel("Time (s)")
    ax.set_ylabel("# solved benchmarks")

    markers = ["^", "d", "o", "s", "*"]
    colors = ["#fc8d62", "#8da0cb"]
    for i, (exp, xs) in enumerate(times_dict.items()):
        ys = list(range(len(xs)+1))
        ax.plot([0]+xs+[300], ys+[len(xs)], label=exp, marker=markers[i], color=colors[i])

    ax.hlines(consts.TOTAL_BENCHMARKS, 0, 120, linestyles='dashed', label="max solved benchmarks", colors="0.8")
    ax.legend(loc="center right")
    # plt.tight_layout()
    plt.savefig(os.path.join(output, "solved.png"))

def main():
    cmd_parser = build_cmd_parser()
    args = cmd_parser.parse_args()

    if args.plot_all or args.plot_solved:
        experiments = args.plot_all
        if experiments is None:
            experiments = args.plot_solved

        plot_solved(experiments, args.data_dir, args.output)

    if args.plot_all or args.plot_ranks:
        experiments = args.plot_all
        if experiments is None:
            experiments = args.plot_ranks

        plot_ranks(experiments, args.data_dir, args.output)

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
        )
        b = Bencher(
            args.exp_name,
            [
                slack_suite,
                stripe_suite,
                square_suite,
            ],
            config)

        if args.generate_witness_only:
            rep = 1
        else:
            rep = args.repeat_exp

        # with cProfile.Profile() as p:
        for i in range(rep):
            print("***********************************************************")
            print(f"Running iteration #{i}")

            b.run(
                args.data_dir,
                args.suites,
                args.benchmarks,
                output=args.output,
                print_api=args.print_api_info,
                print_results=args.print_results,
                print_appendix=False,
                plot_ranks=False,
                cached_results=args.cache)

            # p.print_stats()
            print(f"Iteration #{i} completed")
            print("***********************************************************")

if __name__ == '__main__':
    main()
