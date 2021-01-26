import re
from traces import log
import logging

class DSU:
    def __init__(self):
        self._parents = {}
        self._sizes = {}
        self._nexts = {}
        self._values = {}
        self._logger = logging.getLogger(__name__)

    def find(self, x):
        # self._logger.debug(f"Finding {x} in DSU")
        if x not in self._parents:
            return None

        if self._parents[x] != x:
            self._parents[x] = self.find(self._parents[x])
            
        return self._parents[x]

    def union(self, x, y):
        if x not in self._parents:
            self._parents[x] = x
            self._sizes[x] = 1
            self._nexts[x] = x
            self._values[x] = set([x.value])

        if y not in self._parents:
            self._parents[y] = y
            self._sizes[y] = 1
            self._nexts[y] = y
            self._values[y] = set([y.value])

        # if x != y and str(x) == str(y):
        #     self._logger.debug(f"Weird unequal for {x} and {y}")
        #     self._logger.debug(f"Func names: {x.func_name == y.func_name}")
        #     self._logger.debug(f"Arg names: {x.arg_name == y.arg_name}")
        #     self._logger.debug(f"Methods: {x.method.upper() == y.method.upper()}")
        #     self._logger.debug(f"Paths: {x.path == y.path}")

        # self._logger.debug(f"Union {x} and {y} in DSU")
        xr, yr = self.find(x), self.find(y)
        # if x == y and xr != yr:
        #     self._logger.debug(f"Weird unequal for {x} and {y}")
        #     self._logger.debug(f"Func names: {x.func_name == y.func_name}")
        #     self._logger.debug(f"Arg names: {x.arg_name == y.arg_name}")
        #     self._logger.debug(f"Methods: {x.method.upper() == y.method.upper()}")
        #     self._logger.debug(f"Paths: {tuple(x.path) == tuple(y.path)}")

        # self._logger.debug(f"Union roots {xr} and {yr} in DSU")
        if self._sizes[xr] < self._sizes[yr]:
            self._parents[yr] = xr
            # swap the next pointer of xr and yr
            self._nexts[yr], self._nexts[xr] = self._nexts[xr], self._nexts[yr]
            self._sizes[xr] += self._sizes[yr]
            self._values[xr] = self._values[xr].union(self._values[yr])
        elif self._sizes[yr] < self._sizes[xr] or xr != yr: # if they have the same size but are different nodes
            self._parents[xr] = yr
            # swap the next point of xr and yr
            self._nexts[xr], self._nexts[yr] = self._nexts[yr], self._nexts[xr]
            self._sizes[yr] += self._sizes[xr]
            self._values[yr] = self._values[yr].union(self._values[xr])

    def groups(self):
        groups = []
        for x in self._parents:
            if self._parents[x] == x:
                groups.append(self.get_group(x))

        return groups

    def get_value_bank(self, x):
        return self._values.get(self.find(x), set())

    def get_group(self, x):
        '''
            get all the elements in the same group as @x@
        '''
        if x not in self._parents:
            return []

        result = [x]
        cur = x
        nxt = self._nexts[x]
        while x != nxt:
            result.append(nxt)
            cur, nxt = nxt, self._nexts[cur]

        return result

class LogAnalyzer:
    def __init__(self):
        self.value_to_param = {}
        self.dsu = DSU()

    def analyze(self, entries):
        '''
            Match the value of each request argument or response parameter
            in a log entry and union the common ones
        '''
        for entry in entries:
            for p in entry.parameters:
                self.insert(p)
            for r in entry.responses:
                self.insert(r)

    def insert(self, param):
        value = str(param.value)
        
        # skip empty values, they are meaningless
        if not value:
            return

        if value not in self.value_to_param:
            self.value_to_param[value] = param

        root = self.value_to_param[value]
        self.dsu.union(root, param)

    def analysis_result(self):
        return self.dsu.groups()

    def to_graph(self, dot, **kwargs):
        '''
            output the analysis result as a graph in dot format
        '''
        allow_only_input = kwargs.get("allow_only_input", False)
        endpoints = kwargs.get("endpoints")
        
        groups = self.analysis_result()
        edges = set()
        for group in groups:
            # pick representative in each group, the shortest path name
            rep = ""
            for param in group:
                if isinstance(param, log.ResponseParameter):
                    path_str = '.'.join(param.path)
                    if not rep or len(rep) > len(path_str):
                        rep = path_str
            
            if not rep:
                if not allow_only_input:
                    continue
                # none of the parameters in the group is from a response
                # pick the first as the representative
                # print("not response, choosing", group[0])
                rep = group[0].arg_name
            
            dot.node(rep, label=rep, shape="oval")

            for param in group:
                dot.node(param.func_name, label=param.func_name, shape='rectangle')
                if isinstance(param, log.ResponseParameter):
                    # add an edge between the method and its return type
                    # TODO: modify the rep for array here
                    l, s = param.path_to_str(rep)
                    if '[' not in rep and not re.search("image_*", rep):
                        edges.add((param.func_name, s))

                    if l > 0:
                        edges.add((s, rep))
                else:
                    # add an edge between parameter name and the method
                    if '[' not in rep and not re.search("image_*", rep):
                        edges.add((rep, param.func_name))

        for v1, v2 in edges:
            if ((v1[0] == '/' and v1 not in endpoints) or 
                (v2[0] == '/' and v2 not in endpoints)):
                continue

            dot.edge(v1, v2, style="solid")