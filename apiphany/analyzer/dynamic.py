import random
from enum import IntEnum
import time
import xeger

from apiphany.analyzer.entry import ErrorResponse
from apiphany.analyzer.multiplicity import MUL_ZERO_MORE
from apiphany.analyzer.utils import path_to_name
from apiphany.schemas import types

CMP_ENDPOINT_NAME = 0
CMP_ENDPOINT_AND_ARG_NAME = 1
CMP_ENDPOINT_AND_ARG_VALUE = 2

class BiasType(IntEnum):
    NONE = 0
    SIMPLE = 1
    LOOK_AHEAD = 2

class Goal:
    def __init__(self, multiplicity, values, fields=[]):
        self.multiplicity = multiplicity
        self.values = values
        self.fields = fields

    def __str__(self):
        return (
            "values:" + str(self.values) +
            " fields:" + str(self.fields)
        )

    def __repr__(self):
        return self.__str__()

class DynamicAnalysis:
    """search for trace either by a parameter value or the endpoint name
    """

    def __init__(self, entries, skip_fields, log_analyzer,
        abstraction_level=0, bias_type=BiasType.NONE):
        self._entries = entries
        self._skip_fields = skip_fields
        self._environment = {}
        self._log_analyzer = log_analyzer
        self._abstraction_level = abstraction_level
        self._bias_type = bias_type

    def reset_env(self):
        self._environment = {}

    def get_traces_by_param(self, param):
        results = []
        for entry in self._entries:
            params = entry.parameters
            param_values = [p.value for p in params
                if (p.value and
                not isinstance(p.value, int) and
                not isinstance(p.value, bool))
            ]

            if param.value in param_values:
                results.append(entry.endpoint)

        results = {r: r for r in results}
        return results

    def get_traces_by_endpoint(self, endpoint):
        """look at the responses of the endpoint and find the next that consumes some part of its responses
        """
        entries = [e for e in self._entries if e.endpoint == endpoint]
        results = []

        for entry in entries:
            resps = entry.response.flatten(
                "#/components/schemas", 
                self._skip_fields
            )

            for r in resps:
                results += self.get_traces_by_param(r)

        # if endpoint == "/conversations.list":
        #     print("get_traces_by_endpoint", results)

        results = {r: r for r in results}
        return list(results.keys())

    def get_nullary_endpoints(self):
        endpoints = []
        for entry in self._entries:
            params = [p for p in entry.parameters
                if p.arg_name not in self._skip_fields]

            if len(params) == 0:
                endpoints.append(entry.endpoint)

        endpoints = {e: e for e in endpoints}
        return list(endpoints.keys())

    def get_sequences(self, endpoint=None, limit=100):
        # start from the given endpoint, what kind of sequences we can get
        starts = self.get_nullary_endpoints() if endpoint is None else [endpoint]
        # bfs
        sequences = []
        queue = [[x] for x in starts]
        # print(queue)
        while len(queue) > 0 and len(sequences) < limit:
            seq = queue.pop(0)
            traces = self.get_traces_by_endpoint(seq[-1])
            if len(traces) == 0:
                sequences.append(seq)
            else:
                non_loop = []
                for tr in traces:
                    sequences.append(seq + [tr])
                    if tr not in seq:
                        # print("adding", seq+[tr])
                        non_loop.append(seq + [tr])
                
                queue += non_loop

        return sequences

    def push_var(self, x, v):
        self._environment[x] = v

    def pop_var(self, x):
        self._environment.pop(x, None)

    def lookup_var(self, x):
        return self._environment.get(x)

    def sample_value_by_type(self, typ):
        return self._log_analyzer.sample_value_by_type(typ)

    def _sample_entry(self, entries, backup=[]):
        if entries:
            entry_vals, weights = zip(*entries)
        elif backup:
            entry_vals, weights = zip(*backup)
        else:
            entry_vals, weights = [], []

        # print("entries:", entry_vals, weights)
        if entry_vals:
            return random.choices(entry_vals, weights=weights, k=1)[0]
        else:
            # print("no successful entry found")
            return None

    def get_trace(self, fun, args):
        # abstraction level matters here
        # get all entries with the same endpoint call
        start = time.time()
        same_endpoint_calls = self._entries.get(fun, {})

        if self._abstraction_level == CMP_ENDPOINT_NAME:
            calls = []
            for _, v, w in same_endpoint_calls.values():
                calls.append((v, w))
            return self._sample_entry(calls)

        # get all entries with the same arg names
        arg_names = sorted([x for x, _ in args])
        same_args_calls = same_endpoint_calls.get(tuple(arg_names), [])
        same_args_values = [(v, w) for _, v, w in same_args_calls]

        if self._abstraction_level == CMP_ENDPOINT_AND_ARG_NAME:
            # return self._sample_entry(same_args_calls, same_endpoint_calls)
            return self._sample_entry(same_args_values)

        # get all entries with the same arg values
        same_arg_val_calls = []
        for params, v, w in same_args_calls:
            has_all_values = True
            for x, arg_v in args:
                if params[x] != arg_v:
                    has_all_values = False
                    break

            if has_all_values:
                same_arg_val_calls.append((v, w))

        if self._abstraction_level == CMP_ENDPOINT_AND_ARG_VALUE:
            # print("sampling entries for", fun)
            # return self._sample_entry(same_arg_val_calls, same_args_calls)
            return self._sample_entry(
                same_arg_val_calls,
                backup=same_args_values)
        else:
            raise Exception("Unknown abstraction level")

    def get_trace_by_goal(self, fun, arg_names, goal):
        # get all entries with the same endpoint call
        same_endpoint_calls = []
        for entry in self._entries:
            if entry.endpoint == fun:
                # check arg names
                param_names = [param.arg_name for param in entry.parameters]
                has_all_args = True
                for x in arg_names:
                    if x not in param_names:
                        has_all_args = False
                        break

                for param in entry.parameters:
                    if param.arg_name in self._skip_fields:
                        continue

                    if param.arg_name not in arg_names:
                        has_all_args = False
                        break
                
                if not has_all_args:
                    continue

                # check response fields
                if isinstance(entry.response, ErrorResponse):
                    continue
                
                response_matches = True
                obj = entry.response.value
                for p in goal.fields:
                    if obj is None:
                        response_matches = False
                        break
                    else:
                        obj = obj.get(p)
                        while isinstance(obj, list):
                            idx = random.randint(0, len(obj)-1)
                            obj = obj[idx]
 
                if not response_matches:
                    continue
                
                # check response values
                for v in goal.values:
                    if (isinstance(obj, list) and v not in obj) or v != obj:
                        response_matches = False

                if not response_matches:
                    continue

                same_endpoint_calls.append(entry)

        is_return_array = False
        if same_endpoint_calls:
            an_endpoint = same_endpoint_calls[0]
            is_return_array = an_endpoint.response.array_level > 0
            
        if goal.multiplicity == MUL_ZERO_MORE and not is_return_array:
            count = 2
        else:
            count = 1

        if same_endpoint_calls:
            return random.choices(same_endpoint_calls, k=count)
        else:
            return None
