import random

from analyzer.entry import ErrorResponse
from analyzer.multiplicity import MUL_ZERO_MORE
from synthesizer.utils import make_entry_name

CMP_ENDPOINT_NAME = 0
CMP_ENDPOINT_AND_ARG_NAME = 1
CMP_ENDPOINT_AND_ARG_VALUE = 2

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

    def __init__(self, entries, skip_fields, abstraction_level=0):
        self._entries = entries
        self._skip_fields = skip_fields
        self._environment = {}
        self._abstraction_level = abstraction_level

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

    def _sample_entry(self, entries, backup=[]):
        entry_vals = []
        for e in entries:
            if (isinstance(e.response, ErrorResponse) or 
                e.response.value is None):
                continue
            else:
                entry_vals.append(e.response.value)

        if not entry_vals:
            # print("cannot find trace in the given group, using backups")
            for e in backup:
                if (isinstance(e.response, ErrorResponse) or 
                    e.response.value is None):
                    continue
                else:
                    entry_vals.append(e.response.value)

        if entry_vals:
            return random.choice(entry_vals)
        else:
            print("not successful entry found")
            return None

    def get_trace(self, fun, args):
        # abstraction level matters here
        # get all entries with the same endpoint call
        same_endpoint_calls = []
        for entry in self._entries:
            if make_entry_name(entry.endpoint, entry.method) == fun:
                same_endpoint_calls.append(entry)

        if self._abstraction_level == CMP_ENDPOINT_NAME:
            return self._sample_entry(same_endpoint_calls)

        # get all entries with the same arg names
        same_args_calls = []
        for entry in same_endpoint_calls:
            param_names = [param.arg_name for param in entry.parameters]
            has_all_args = True
            for x, _ in args:
                if x not in param_names:
                    has_all_args = False
                    break

            arg_map = {x: v for x,v in args}
            # print("arg_map", arg_map)
            for param in entry.parameters:
                if param.arg_name in self._skip_fields:
                    continue

                if param.arg_name not in arg_map:
                    # print("cannot find the parameter from real trace", param.arg_name, "during execution")
                    has_all_args = False
                    break

            if has_all_args:
                same_args_calls.append(entry)

        if self._abstraction_level == CMP_ENDPOINT_AND_ARG_NAME:
            # return self._sample_entry(same_args_calls, same_endpoint_calls)
            return self._sample_entry(same_args_calls)

        # get all entries with the same arg values
        same_arg_val_calls = []
        for entry in same_args_calls:
            params = {param.arg_name: param.value for param in entry.parameters}
            has_all_values = True
            for x, v in args:
                if x not in param_names or params[x] != v:
                    has_all_values = False
                    break

            if has_all_values:
                same_arg_val_calls.append(entry)

        if self._abstraction_level == CMP_ENDPOINT_AND_ARG_VALUE:
            print("sampling entries for", fun)
            # return self._sample_entry(same_arg_val_calls, same_args_calls)
            return self._sample_entry(same_arg_val_calls, backup=same_args_calls)
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