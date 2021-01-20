import re
import os
from graphviz import Digraph
from traces import log
from multiprocessing import Manager
import logging

class DSU:
    def __init__(self):
        self._parents = {}
        self._sizes = {}
        self._nexts = {}
        self._values = {}
        self._logger = logging.getLogger(__name__)

    def find(self, x):
        # self._logger.debug(f"Find {x} in DSU")
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

        xr, yr = self.find(x), self.find(y)
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
        return self._values.get(x, [])

    def get_group(self, x):
        '''
            get all the elements in the same group as @x@
        '''
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

    def to_graph(self, **kwargs):
        '''
            output the analysis result as a graph in dot format
        '''
        dot = Digraph()
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
                    if '[' not in rep and not re.search("image_*", rep):
                        edges.add((param.func_name, rep))
                else:
                    # add an edge between parameter name and the method
                    if '[' not in rep and not re.search("image_*", rep):
                        edges.add((rep, param.func_name))

        for v1, v2 in edges:
            if endpoints and v1 not in endpoints and v2 not in endpoints:
                continue

            dot.edge(v1, v2)

        return dot