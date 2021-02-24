# from analyzer.entry import Parameter

class DynamicAnalysis:
    """search for trace either by a parameter value or the endpoint name
    """

    def __init__(self, entries, skip_fields):
        self._entries = entries
        self._skip_fields = skip_fields

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