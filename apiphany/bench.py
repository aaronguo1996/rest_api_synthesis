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
import cProfile
from graphviz import Digraph

from analyzer import dynamic
from analyzer.ascription import Ascription
from benchmarks.benchmark import BenchConfig, Bencher
from benchmarks.suites import slack_suite, stripe_suite, square_suite
from synthesizer.constructor import Constructor
from synthesizer.utils import make_entry_name
from witnesses.engine import WitnessGenerator
import analyzer
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
    parser.add_argument("--exp-name", default="default_apiphany",
        help="Experiment name")
    parser.add_argument("--bench", nargs='?',
        help="Path to benchmark file or directory (by default runs all in benchmarks)")
    parser.add_argument("--names", nargs="+",
        help="Benchmark name list")

    # witness generation
    parser.add_argument("--generate-witness", action="store_true",
        help="Whether to generate witness")
    parser.add_argument("--method-coverage", type=float,
        help="Prune methods and witnesses to get the target coverage")
    parser.add_argument("--uncovered", type=consts.UncoveredOption,
        choices=list(consts.UncoveredOption),
        default=consts.UncoveredOption.EXCLUDE,
        help="Different options to deal with uncovered methods")

    # synthesis options
    parser.add_argument("--synthesis-only", action='store_true',
        help="Whether to run ranking")
    parser.add_argument("--conversion-fair", action='store_true',
        help="Whether to treat conversion transitions fair")
    
    # retrospective execution options
    parser.add_argument("--run-re", action='store_true',
        help="Whether to run retrospective execution")
    parser.add_argument("--repeat", type=int, nargs='?', default=5,
        help="Number of times to repeat filtering")
    parser.add_argument("--filter-num", type=int, nargs='?', default=3,
        help="Number of times to run filtering")
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
        filter_sol_only=False,
        generate_witness=False,
        method_coverage=1.0,
        conversion_fair=False,
        print_results=False,
        print_api_info=False,
        cache=False)
    return parser



def load_exp_results(data_dir, exp_name):
    all_entries = []
    apis = ["slack_api_test", "stripe_api_test", "square_api_test"]
    for api in apis:
        cache_path = os.path.join(data_dir, exp_name, api, "bench_results.pkl")
        with open(cache_path, "rb") as f:
            d = pickle.load(f)

        latex_entries = d["results"]
        all_entries += latex_entries

    # print(all_entries)
    return all_entries
    

def plot_ranks(experiments, data_dir, output=None):
    # load results for all experiments
    for exp in experiments:
        results = load_exp_results(data_dir, exp)
        ranks_re = []
        ranks_no_re = []
        for result in results:
            if result is None or result.ranks is None:
                continue

            ranks_re.append(result.ranks[0])
            ranks_no_re.append(result.rank_no_re)
    
        cnt_ranks_re = [sum([1 for x in ranks_re if x <= i]) for i in range(0,5000)]
        cnt_ranks_no_re = [sum([1 for x in ranks_no_re if x <= i]) for i in range(0,5000)]

        # plot core data
        fig, (ax1, ax2) = plt.subplots(1, 2, sharey=True)
        fig.subplots_adjust(wspace=0.05)  # adjust space between axes

        ax1.set_xlim(0, 15)
        ax2.set_xscale('log')
        ax2.set_xlim(15, 5000)
        ax1.set_ylim(0, 28)
        ax1.set_xlabel("Rank", loc="right")
        ax1.set_ylabel("# benchmarks")
        ax1.yaxis.set_ticks(range(0,28,2))
        ax1.xaxis.set_ticks([0,3,6,9,10,12,15])
        ax1.plot(cnt_ranks_re, label="w/ RE", color="#fc8d62")
        ax1.plot(cnt_ranks_no_re, label="w/o RE", color="#8da0cb")
        ax2.plot(cnt_ranks_re, label="w/ RE", color="#fc8d62")
        ax2.plot(cnt_ranks_no_re, label="w/o RE", color="#8da0cb")
        ax1.hlines(26, 0, 15, linestyles='dashed', label="max solved benchmarks", colors="0.8")
        ax2.hlines(26, 15, 3000, linestyles='dashed', label="max solved benchmarks", colors="0.8")
        ax2.legend(loc="lower right")

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
        results = load_exp_results(data_dir, exp)
        times = []
        for result in results:
            if result is None or result.ranks is None:
                continue

            times.append(result.syn_time)

        times_dict[exp] = sorted(times)

    # plot core data
    fig, ax = plt.subplots(1, 1)
    ax.set_ylim(0, 28)
    ax.set_xlim(0, 60)
    ax.yaxis.set_ticks(range(0,28,2))
    ax.set_xlabel("Time (s)")
    ax.set_ylabel("# solved benchmarks")

    for exp, xs in times_dict.items():
        ys = list(range(len(xs)+1))
        ax.plot([0]+xs+[60], ys+[len(xs)], label=exp)

    ax.hlines(26, 0, 60, linestyles='dashed', label="max solved benchmarks", colors="0.8")
    ax.legend(loc="lower right")
    plt.savefig(os.path.join(output, "solved.png"))

def main():
    cmd_parser = build_cmd_parser()
    args = cmd_parser.parse_args()

    if args.plot_all or args.plot_solved:
        plot_solved(args.plot_solved, args.data_dir, args.output)

    if args.plot_all or args.plot_ranks:
        plot_ranks(args.plot_ranks, args.data_dir, args.output)

    if (not args.plot_all and
        not args.plot_solved and
        not args.plot_ranks):
        config = BenchConfig(
            cache=args.cache,
            repeat=args.repeat,
            filter_num=args.filter_num,
            filter_sol_only=args.filter_sol_only,
            synthesis_only=args.synthesis_only,
            bias_type=bias_type_args[args.bias_type],
            use_parallel=args.parallel,
            get_place_stats=args.get_place_stats,
            generate_witness=args.generate_witness,
            method_coverage=args.method_coverage,
            uncovered_opt=args.uncovered,
            run_re=args.run_re,
            conversion_fair=args.conversion_fair,
        )
        b = Bencher(
            args.exp_name,
            [
                slack_suite,
                # stripe_suite,
                # square_suite,
            ],
            config)

        # with cProfile.Profile() as p:
        b.run(
            args.data_dir,
            args.names,
            output=args.output,
            print_api=args.print_api_info,
            print_results=args.print_results,
            print_appendix=False,
            plot_ranks=False,
            cached_results=False)

            # p.print_stats()

if __name__ == '__main__':
    main()
