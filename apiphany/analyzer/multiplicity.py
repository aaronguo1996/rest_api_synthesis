from collections import defaultdict
from re import L
from openapi import defs
from analyzer.entry import ErrorResponse

MUL_ZERO_ONE = 0
MUL_ZERO_MORE = 1
MUL_ONE_ONE = 2

class MultiplicityAnalysis:
    """A static analysis to determine whether a filter function returns 1 or more results
    """
    def __init__(self, entries, annotations):
        self._entries = entries
        self._annotations = annotations
        self._environment = {}
        self._unique_fields = []

    def reset(self):
        self._environment = {}

    def analyze(self, skip_fields):
        unique_fields = []
        response_reps = {}
        for entry in self._entries:
            # print(entry.endpoint)
            if isinstance(entry.response, ErrorResponse):
                continue

            responses = entry.response.flatten(
                "#/components/schemas",
                skip_fields
            )
            response_vals = {}
            response_counts = defaultdict(int)
            for r in responses:
                key = tuple(r.path)
                response_counts[key] += 1
                if key in response_vals:
                    response_vals[key].add(r.value)
                    response_reps[key].add(r)
                else:
                    response_vals[key] = set([r.value])
                    response_reps[key] = set([r])

            for k, lst in response_vals.items():
                # skip non arrays
                if defs.INDEX_ANY in k:
                    if len(lst) == response_counts[k]:
                        unique_fields.append(k)
                    elif k in unique_fields:
                        # invalidate some fields
                        # print("invalidate", k)
                        unique_fields.remove(k)
            
        for k in unique_fields:
            for p in response_reps[k]:
                if p.type:
                    self._unique_fields.append(p.type.name)

    def push_var(self, x, m):
        self._environment[x] = m

    def lookup_var(self, x):
        return self._environment.get(x, (0, MUL_ONE_ONE))

    def check_endpoint(self, fun):
        for _, entry in self._annotations.items():
            if entry.endpoint == fun:
                break

        is_array = entry.response.array_level
        if is_array:
            return is_array, MUL_ZERO_MORE
        else:
            return is_array, MUL_ONE_ONE

    @staticmethod
    def pretty(m):
        if m == MUL_ZERO_ONE:
            return "zero or one"
        elif m == MUL_ONE_ONE:
            return "one or one"
        elif m == MUL_ZERO_MORE:
            return "zero or more"
        else:
            raise Exception("Unknown multiplicity")
