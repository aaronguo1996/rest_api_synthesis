from graphviz import Digraph
from collections import defaultdict
import seaborn as sns
<<<<<<< HEAD
=======
import re
>>>>>>> 86ebf765dd6fe6ced9f9f1c5bab6d0c8c784c8bd

class GraphStats:
    def __init__(self):
        self._dot = Digraph(strict=True)
        self._nodes = defaultdict(int)
        self._edges = set()
<<<<<<< HEAD

    def add_node(self, node):
        self._nodes[node] += 1

    def add_edge(self, u, v):
        self._edges.add((u, v))

    def render(self, filename):
        # print(self._nodes)
=======
        self._parameters = {}
        self._responses = {}

    def add_node(self, node):
        if re.match('^/.*_response$', node):
            return
            
        self._nodes[node] += 1

    def add_edge(self, u, v):
        if re.match('^/.*_response$', u):
            self._responses[u] = v
        elif re.match('^/.*_response$', v):
            if v in self._parameters:
                self._parameters[v] += [u]
            else:
                self._parameters[v] = [u]
        else:
            self._edges.add((u, v))

    def skip_response_nodes(self):
        for r, us in self._parameters.items():
            for u in us:
                v = self._responses.get(r, None)
                if v:
                    self._edges.add((u, v))

    def render(self, filename):
        # print(self._nodes)
        self.skip_response_nodes()
>>>>>>> 86ebf765dd6fe6ced9f9f1c5bab6d0c8c784c8bd
        counts = list({v: v for v in self._nodes.values()}.keys())
        palette = sns.color_palette("Blues", len(counts)).as_hex()
        sorted_counts = sorted(counts)
        for n, v in self._nodes.items():
            i = sorted_counts.index(v)
            self._dot.node(
                n, label=n, 
                fillcolor=palette[i], style="filled"
            )

        for u, v in self._edges:
            self._dot.edge(u, v)

        self._dot.render(filename)