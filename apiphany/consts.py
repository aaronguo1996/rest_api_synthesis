from enum import Enum

OBJ_MATCH_THRESHOLD = 0.6
REF_PREFIX = "#/components/schemas/"
CUSTOM_PREFIX = "x-"
DEFAULT_LENGTH_LIMIT = 9
JSON_TYPE = "application/json"
HOSTNAME_PREFIX = "https://"
HOSTNAME_PREFIX_LEN = len(HOSTNAME_PREFIX)

KEY_ANALYSIS = "analysis"
KEY_ANNOTATION = "annotation_path"
KEY_BLACKLIST = "blacklist"
KEY_DEBUG = "enable_debug"
KEY_DOC_FILE = "doc_file"
KEY_ENDPOINTS = "endpoints"
KEY_EXP_NAME = "exp_name"
KEY_GEN_DEPTH = "gen_depth"
KEY_HOSTNAME = "hostname"
KEY_ITERATIONS = "iterations"
KEY_LOG_FILE = "log_file"
KEY_OUTPUT = "debug_output"
KEY_PATH_TO_DEFS = "path_to_definitions"
KEY_PLOT_EVERY = "plot_every"
KEY_PLOT_GRAPH = "plot_graph"
KEY_SKIP_FIELDS = "ignore_field_names"
KEY_SOLVER_NUM = "solver_number"
KEY_SOLVER_TYPE = "solver_type"
KEY_SYN_PREFILTER = "enable_prefilter"
KEY_SYNTHESIS = "synthesis"
KEY_TEST_SUITES = "test_suites"
KEY_TIMEOUT = "timeout_per_request"
KEY_TOKEN = "token"
KEY_UNINTERESTING = "uninteresting_endpoints"
KEY_VALUE_DICT = "value_dict"
KEY_WITNESS = "witness"
KEY_MAX_OPT = "max_opt_params"
KEY_SOL_NUM = "solution_number"
KEY_EXPAND_GROUP = "expand_group"
KEY_BLOCK_PERM = "block_perms"
KEY_EXECUTION = "execution"
KEY_BIAS = "bias_type"
KEY_INITIAL_WITNESS_ONLY = "initial_witness_only"

SOLVER_PN_SMT = "petri net SMT"
SOLVER_HYPER = "hypergraph"
SOLVER_PN_ILP = "petri net ILP"

FILE_TRACE = "traces.pkl"
FILE_ENTRIES = "entries.pkl"
FILE_GRAPH = "graph.pkl"
FILE_RESULTS = "bench_results.pkl"

PREFIX_CLONE = "clone_"
PREFIX_CONVERT = "convert_"

SPACE = '    '
MAX_COST = 99999.9

EXP_DEFAULT = "default_apiphany"
DATA_DEFAULT = "experiment_data_20210707_2056"

APIS = ["slack_api_test", "stripe_api_test", "square_api_test"]

class UncoveredOption(Enum):
    EXCLUDE = "exclude"
    DEFAULT_TO_SYNTACTIC = "default-to-syntactic"

    def __str__(self):
        return self.value

class SearchStatus(Enum):
    FOUND_EXPECTED = "found-expected"
    NOT_FOUND = "not-found"
    TIMEOUT = "timeout"