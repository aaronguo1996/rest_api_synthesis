from graphviz import Digraph
from collections import defaultdict
import seaborn as sns

class GraphStats:
    def __init__(self):
        self._dot = Digraph(strict=True)
        self._nodes = defaultdict(int)
        self._edges = set()

    def add_node(self, node):
        self._nodes[node] += 1

    def add_edge(self, u, v):
        self._edges.add((u, v))

    def render(self, filename):
        # print(self._nodes)
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