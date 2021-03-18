#!/usr/bin/python3.8

import argparse
import pickle
import os
import json
import logging
import random
import matplotlib.pyplot as plt
from collections import defaultdict
from graphviz import Digraph

from traces import parser, analyzer, typeChecker
from fuzzer import fuzzer
from tests import test_runner
from openapi.preprocess import PreProcessor
from prance import ResolvingParser, ValidationError

# definitions of all the subcommands
ANALYSIS_PARSER = 0
FUZZ_PARSER = 1
TEST_PARSER = 10

# definitions of constants
DEFAULT_DEBUG_OUTPUT = 'debug.log'


def build_cmd_parser():
    '''
        All arguments
    '''
    parser = argparse.ArgumentParser()
    parser.add_argument("config_file", nargs='?',
                        help="Path to the configuration file")
    parser.add_argument("--test", action="store_true", help="Run unit tests")
    parser.add_argument("--plot", action="store_true",
                        help="Plot graphs without fuzzing")
    parser.add_argument("--print-log", action="store_true",
                        help="Print log from previous run")
    parser.add_argument("--store-traces", action="store_true",
                        help="Store generated traces into a binary file")
    return parser


def read_doc(doc_path):
    try:
        parser = ResolvingParser(doc_path)
        # spec with all the references resolved
        return parser.specification
    except ValidationError:  # allow other exceptions to be thrown
        path_segs = doc_path.split('/')
        old_filename = path_segs[-1]
        name_segs = old_filename.split('.')
        new_filename = '.'.join(name_segs[:-1]) + "_preprocess.json"
        preprocessor = PreProcessor(doc_path)
        new_path = '/'.join(path_segs[:-1] + [new_filename])
        preprocessor.preprocess(new_path)
        return read_doc(new_path)


def read_data():
    # {
    #         "Iteration": i,
    #         "Results": results,
    #         "Endpoints": self._covered_endpoints,
    #         "Error buckets": self._error_buckets,
    #     }
    results = []
    with open(fuzzer.RESULT_FILE, "rb") as f:
        try:
            x = pickle.load(f)
            while x:
                results.append(x)
                x = pickle.load(f)
        except:
            pass

    return results


def plot_errors(iter_results):
    errors = defaultdict(int)
    for i_result in iter_results:
        results = i_result["Results"]
        for r in results:
            if r.has_error:
                errors[(r.return_code, r.response_body.get("error"))] += 1

    lists = errors.items()
    labels, y = zip(*lists)  # unpack a list of pairs into two tuples
    plt.figure(figsize=(20, 20))
    plt.bar(range(len(y)), y)
    plt.xticks(range(len(y)), labels, rotation=90)
    plt.xlabel("Errors")
    plt.ylabel("Number of Occurrences")
    plt.savefig("errors.png")
    plt.close()


def plot_coverage(iter_results):
    coverage = {}
    for i_result in iter_results:
        coverage[i_result["Iteration"]] = len(i_result["Endpoints"])

    lists = coverage.items()
    x, y = zip(*lists)
    plt.plot(x, y)
    plt.xlabel("Iteration")
    plt.ylabel("Number of Endpoints")
    plt.savefig("coverage.png")
    plt.close()


def print_errors(iter_results):
    with open("errors.log", "w+") as f:
        for i_result in iter_results:
            for r in i_result["Results"]:
                if r.has_error:
                    f.write(r.endpoint)
                    f.write('\n')
                    f.write(json.dumps(r.request_params))
                    f.write('\n')
                    f.write(json.dumps(r.response_body))
                    f.write('\n')


def main():
    random.seed(1)

    cmd_parser = build_cmd_parser()
    args = cmd_parser.parse_args()

    configuration = {}
    with open(args.config_file, 'r') as config:
        configuration = json.loads(config.read())

    # clear the log file if exists
    if (configuration["enable_debug"] and
        not args.plot and not args.print_log and
            os.path.exists(configuration["debug_output"])):
        os.remove(configuration["debug_output"])

    logging.basicConfig(
        filename=configuration["debug_output"], level=logging.DEBUG)

    if args.test:
        suites = configuration.get("test_suites")

        if not suites:
            raise Exception(
                "Test suites need to be specified in configuration file")

        test_runner.run_test(configuration["test_suites"])
    elif args.plot:
        results = read_data()
        plot_errors(results)
        plot_coverage(results)
    elif args.print_log:
        results = read_data()
        print_errors(results)
    else:
        print("Reading OpenAPI document...")
        doc = read_doc(configuration["doc_file"])

        # with open('debug.json', 'w+') as f:
        #     f.write(json.dumps(doc))

        print("Parsing OpenAPI document...")
        # entries = None
        log_parser = parser.LogParser(
            configuration["log_file"], configuration["hostname"], doc)
        entries = log_parser.parse_entries(
            configuration["analysis"]["uninteresting_endpoints"],
            configuration["analysis"]["ignore_field_names"])
        if configuration["enable_debug"]:
            # write entries to log file
            logging.debug("========== Start Logging Parse Results ==========")
            for e in entries:
                logging.debug(e)

        # write traces to the binary file
        # with open('traces.pkl', 'wb') as f:
        #     pickle.dump(entries, f)
        with open('traces.pkl', 'rb') as f:
            entries = pickle.load(f)

        # print("Analyzing provided log file...")
        log_analyzer = analyzer.LogAnalyzer()
        log_analyzer.analyze(
            entries, configuration["analysis"]["ignore_field_names"])
        groups = log_analyzer.analysis_result()
        # graph_flag = configuration["analysis"]["params"]["allow_only_input"]
        # log_analyzer.to_graph(graph_flag)
        if configuration["enable_debug"]:
            logging.debug(
                "========== Start Logging Analyze Results ==========")
            for g in groups:
                logging.debug(g)

        print("Running fuzzer to get more traces...")
        engine = fuzzer.Fuzzer(
            doc, log_analyzer,
            configuration["fuzz"]["value_dict"],
            configuration["fuzz"]["annotation_path"],
            configuration["fuzz"]["fuzz_depth"],
            configuration["path_to_definitions"],
            configuration["analysis"]["ignore_field_names"],
            configuration["fuzz"]["plot_graph"],
        )

        endpoints = configuration["fuzz"]["endpoints"]
        if not endpoints:
            endpoints = list(doc["paths"].keys())

        if configuration["fuzz"]["plot_graph"]:
            engine.to_graph(endpoints, "dependencies_0")

        engine.saturate_all(
            endpoints, configuration["fuzz"]["iterations"],
            configuration["fuzz"]["timeout_per_request"])

        # obj_defs = typeChecker.Type.get_object_def("#/components/schemas")
        # # print(obj_defs["objs_user"])

        # user = {
        #     'id': 'U01HHAZ22LD',
        #     'team_id': 'T01D0TUHGNB',
        #     'name': 'gz19960828',
        #     'deleted': False,
        #     'color': '5b89d5',
        #     'real_name': 'zhg069',
        #     'tz': 'America/Los_Angeles',
        #     'tz_label': 'Pacific Standard Time',
        #     'tz_offset': -28800,
        #     'profile': {
        #         'title': '',
        #         'phone': '',
        #         'skype': '',
        #         'real_name': 'zhg069',
        #         'real_name_normalized': 'zhg069',
        #         'display_name': 'Zheng Guo',
        #         'display_name_normalized': 'Zheng Guo',
        #         'fields': None,
        #         'status_text': '',
        #         'status_emoji': '',
        #         'status_expiration': 0,
        #         'avatar_hash': 'ga0116aac821',
        #         'email': 'gz19960828@gmail.com',
        #         'first_name': 'zhg069',
        #         'last_name': '',
        #         'image_24': 'https://secure.gravatar.com/avatar/a0116aac821e0c780b87e9f7476d5eb1.jpg?s=24&d=https%3A%2F%2Fa.slack-edge.com%2Fdf10d%2Fimg%2Favatars%2Fava_0007-24.png', 
        #         'image_32': 'https://secure.gravatar.com/avatar/a0116aac821e0c780b87e9f7476d5eb1.jpg?s=32&d=https%3A%2F%2Fa.slack-edge.com%2Fdf10d%2Fimg%2Favatars%2Fava_0007-32.png',
        #         'image_48': 'https://secure.gravatar.com/avatar/a0116aac821e0c780b87e9f7476d5eb1.jpg?s=48&d=https%3A%2F%2Fa.slack-edge.com%2Fdf10d%2Fimg%2Favatars%2Fava_0007-48.png', 
        #         'image_72': 'https://secure.gravatar.com/avatar/a0116aac821e0c780b87e9f7476d5eb1.jpg?s=72&d=https%3A%2F%2Fa.slack-edge.com%2Fdf10d%2Fimg%2Favatars%2Fava_0007-72.png', 
        #         'image_192': 'https://secure.gravatar.com/avatar/a0116aac821e0c780b87e9f7476d5eb1.jpg?s=192&d=https%3A%2F%2Fa.slack-edge.com%2Fdf10d%2Fimg%2Favatars%2Fava_0007-192.png', 
        #         'image_512': 'https://secure.gravatar.com/avatar/a0116aac821e0c780b87e9f7476d5eb1.jpg?s=512&d=https%3A%2F%2Fa.slack-edge.com%2Fdf10d%2Fimg%2Favatars%2Fava_0007-512.png', 
        #         'status_text_canonical': '', 
        #         'team': 'T01D0TUHGNB'
        #     }, 
        #     'is_admin': False, 
        #     'is_owner': False, 
        #     'is_primary_owner': False, 
        #     'is_restricted': False, 
        #     'is_ultra_restricted': False, 
        #     'is_bot': False, 
        #     'is_app_user': False, 
        #     'updated': 1611535634, 
        #     'has_2fa': False, 
        #     'is_invited_user': True
        # }
        # typ = typeChecker.Type(
        #     "objs_user", obj_defs["objs_user"]).is_type_of(user)
        # print(typ)

        # conversation = {'id': 'D01E1G5JY5D', 'created': 1605061151, 'is_frozen': False, 'is_archived': False, 'is_im': True, 'is_org_shared': False, 'user': 'U01EUT203SM', 'last_read': '1609829301.000300', 'latest': {'client_msg_id': 'd2179f02-208b-4498-a13e-4b78b6eadfef', 'type': 'message', 'text': 'this is a direct message', 'user': 'U01DMQYRMC4', 'ts': '1609829301.000300', 'team': 'T01D0TUHGNB', 'blocks': [{'type': 'rich_text', 'block_id': 'ZuhTv', 'elements': [{'type': 'rich_text_section', 'elements': [{'type': 'text', 'text': 'this is a direct message'}]}]}]}, 'unread_count': 0, 'unread_count_display': 0, 'is_open': True, 'priority': 0}
        # conversation = {'id': 'D01DU9FTXLH', 'created': 1603833026, 'is_frozen': False, 'is_archived': False, 'is_im': True, 'is_org_shared': False, 'user': 'U01DFLC5JCS', 'is_user_deleted': False, 'latest': '1605058952.000400', 'priority': 0}
        # conversation = {'id': 'D01DFS9PVH9', 'created': 1603832891, 'is_archived': False, 'is_im': True, 'is_org_shared': False, 'user': 'U01DMQYRMC4', 'last_read': '1612396055.000100', 'latest': {'type': 'message', 'subtype': 'bot_message', 'text': 'yWQPRYe4GvBvMq5as', 'ts': '1612425759.000200', 'username': 'User token test app', 'bot_id': 'B01J5RHEG4S'}, 'unread_count': 2, 'unread_count_display': 2, 'is_open': True, 'priority': 0}
        # conversation = {'id': 'D01DU9FTXLH', 'created': 1603833026, 'is_archived': False, 'is_im': True, 'is_org_shared': False, 'user': 'U01DFLC5JCS', 'last_read': '1612413454.000100', 'latest': {'type': 'message', 'subtype': 'bot_message', 'text': 'z7ubHcx2RJ', 'ts': '1612413454.000100', 'username': 'User token test app', 'bot_id': 'B01J5RHEG4S'}, 'unread_count': 0, 'unread_count_display': 0, 'is_open': True, 'priority': 0}
        # typ = typeChecker.Type(
        #     "objs_conversation", obj_defs["objs_conversation"]).is_type_of(conversation)
        # print(typ)

        # with open('traces.pkl', 'rb') as f:
        #     entries = pickle.load(f)
        #     log_analyzer = analyzer.LogAnalyzer()
        #     log_analyzer.analyze(
        #         entries, configuration["analysis"]["ignore_field_names"])
        #     groups = log_analyzer.analysis_result()
        #     dot = Digraph(strict=True)
        #     log_analyzer.to_graph(dot, endpoints=configuration["fuzz"]["endpoints"])
        #     dot.render("output/dependencies", view=False)

if __name__ == "__main__":
    main()
