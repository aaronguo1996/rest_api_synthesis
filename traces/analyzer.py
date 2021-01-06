import re
from graphviz import Digraph
from traces import log

class DSU:
    def __init__(self):
        self.parents = {}
        self.sizes = {}
        self.nexts = {}

    def find(self, x):
        if self.parents[x] != x:
            self.parents[x] = self.find(self.parents[x])
            
        return self.parents[x]

    def union(self, x, y):
        if x not in self.parents:
            self.parents[x] = x
            self.sizes[x] = 1
            self.nexts[x] = x

        if y not in self.parents:
            self.parents[y] = y
            self.sizes[y] = 1
            self.nexts[y] = y

        xr, yr = self.find(x), self.find(y)
        if self.sizes[xr] < self.sizes[yr]:
            self.parents[yr] = xr
            # swap the next pointer of xr and yr
            self.nexts[yr], self.nexts[xr] = self.nexts[xr], self.nexts[yr]
            self.sizes[xr] += self.sizes[yr]
        elif (self.sizes[yr] < self.sizes[xr] or 
            xr != yr): # if they have the same size but are different nodes
            self.parents[xr] = yr
            # swap the next point of xr and yr
            self.nexts[xr], self.nexts[yr] = self.nexts[yr], self.nexts[xr]
            self.sizes[yr] += self.sizes[xr]

    def groups(self):
        groups = []
        for x in self.parents:
            if self.parents[x] == x:
                groups.append(self.getGroup(x))

        return groups

    def getGroup(self, x):
        '''
            get all the elements in the same group as @x@
        '''
        result = [x]
        cur = x
        nxt = self.nexts[x]
        while x != nxt:
            result.append(nxt)
            cur, nxt = nxt, self.nexts[cur]

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

    def to_graph(self, allow_only_input=False):
        '''
            output the analysis result as a graph in dot format
        '''
        dot = Digraph()
        
        groups = self.analysis_result()
        edges = []
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
                print("not response, choosing", group[0])
                rep = group[0].arg_name
            
            dot.node(rep, label=rep, shape="oval")

            for param in group:
                dot.node(param.func_name, label=param.func_name, shape='rectangle')
                if isinstance(param, log.ResponseParameter):
                    # add an edge between the method and its return type
                    if '[' not in rep and not re.search("image_*", rep):
                        edges.append((param.func_name, rep))
                else:
                    # add an edge between parameter name and the method
                    if '[' not in rep and not re.search("image_*", rep):
                        edges.append((rep, param.func_name))

        unique_edges = list(dict.fromkeys(edges))
        for v1, v2 in unique_edges:
            dot.edge(v1, v2)

        dot.render('output/dependencies.gv', view=True)