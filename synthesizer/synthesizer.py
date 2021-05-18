from collections import defaultdict
import itertools
import pickle
import time
import os

from analyzer.entry import TraceEntry, Parameter
from openapi import defs
from openapi.utils import blacklist
from program.generator import ProgramGenerator
from program.program import ProgramGraph, all_topological_sorts
from stats.graph_stats import GraphStats
from stats.time_stats import TimeStats, STATS_GRAPH
from synthesizer.hypergraph_encoder import HyperGraphEncoder
from synthesizer.petrinet_encoder import PetriNetEncoder
from synthesizer.utils import make_entry_name, DEFAULT_LENGTH_LIMIT
import config_keys as keys

STATE_FULL = -1
STATE_NORMAL = 0

class Synthesizer:
    def __init__(self, doc, config, entries, exp_dir):
        self._doc = doc
        self._config = config
        self._groups = {}
        self._group_names = {}
        self._landmarks = []
        self._unique_entries = {}
        self._entries = entries
        self._program_generator = ProgramGenerator({})
        # flags
        self._expand_group = config["synthesis"]["expand_group"]
        self._block_perms = config["synthesis"]["block_perms"]
        self._exp_dir = exp_dir

    @TimeStats(key=STATS_GRAPH)
    def init(self):
        TimeStats.reset()
        self._add_transitions()

    def run(self, landmarks, inputs, outputs):
        results = self.run_n(landmarks, inputs, outputs, 1)
        return results[0]

    def _write_solution(self, idx, t, p):
        result_path = os.path.join(self._exp_dir, f"results_{idx}.txt")
        with open(result_path, "a+") as f:
            f.write(f"time: {t: .2f}")
            f.write("\n")
            f.write(f"time breakdown:\n{TimeStats._timing}\n")
            f.write(str(p))
            f.write("\n")
            f.write(p.pretty(self._entries, 0))
            f.write("\n")

    def _serialize_solutions(self, idx, progs):
        solution_path = os.path.join(self._exp_dir, f"solutions_{idx}.pkl")
        if os.path.exists(solution_path):
            with open(solution_path, "rb") as f:
                solutions = pickle.load(f)
        else:
            solutions = []

        solutions += progs
        with open(solution_path, "wb") as f:
            pickle.dump(solutions, f)

    def _expand_groups(self, result):
        groups = []
        for name in result:
            if "_clone" in name:
                continue

            if self._expand_group:
                e = self._entries.get(name)
                if e is None:
                    raise Exception("Unknown transition", name)

                param_typs = [p.type.name for p in e.parameters]
                if isinstance(e.response.type, list):
                    response_typ = [t.name for t in e.response.type]
                else:
                    response_typ = [e.response.type.name]
                key = (tuple(param_typs), tuple(response_typ))
                group = self._groups.get(key, [name])
                groups.append(group)
            else:
                groups.append([name])

        return groups

    def _get_topo_sorts(self, p):
        perms = []
        pgraph = ProgramGraph()
        p.to_program_graph(graph=pgraph, var_to_trans={})
        all_topological_sorts(perms, pgraph, [], {})
        return perms

    def _generate_solutions(self, i, inputs, outputs, result, time):
        programs = []
        groups = self._expand_groups(result) 
        for r in itertools.product(*groups):
            programs += self._program_generator.generate_program(
                r, inputs, outputs[0]
            )

        all_perms = []
        for p in programs:
            # write solutions to file
            self._write_solution(i, time, p)

            # generate all topological sorts for blocking
            if self._block_perms:
                perms = self._get_topo_sorts(p)
                all_perms += perms

        # convert permutations into indices
        perm_indices = []
        if self._block_perms:
            for perms in all_perms:
                indices = []
                for tr in perms:
                    for idx, r in enumerate(result):
                        if tr == r[:len(tr)]:
                            indices.append(idx)
                            break

                if len(indices) == len(result):
                    perm_indices.append(indices)
                

        # print("Get perms", perm_indices, flush=True)
        if not perm_indices:
            perm_indices = [list(range(len(result)))]

        self._serialize_solutions(i, programs)

        return programs, perm_indices

    def _create_encoder(self):
        if self._config["synthesis"]["solver_type"] == "petri net":
            self._encoder = PetriNetEncoder({})
        elif self._config["synthesis"]["solver_type"] == "hypergraph":
            self._encoder = HyperGraphEncoder({})
        else:
            raise Exception("Unknown solver type in config")

        for e in self._unique_entries.values():
            self._encoder._add_transition(e)

    def run_n(self, landmarks, inputs, outputs, n):
        """Single process version of synthesis

        Args:
            landmarks ([type]): [description]
            inputs ([type]): [description]
            outputs ([type]): [description]
            n ([type]): [description]

        Returns:
            [type]: [description]
        """

        # create an encoder
        self._create_encoder()

        solutions = set()
        input_map = defaultdict(int)
        for _, typ in inputs.items():
            input_map[typ.name] += 1

        output_map = defaultdict(int)
        for typ in outputs:
            output_map[typ.name] += 1

        start = time.time()
        self._encoder.init(input_map, output_map)
        self._encoder.set_final(output_map)
        # self._encoder.add_all_constraints()

        while len(solutions) < n:
            result = self._encoder.solve()
            while result is not None:
                print("Find path", result, flush=True)
                programs, perms = self._generate_solutions(
                    0, inputs, outputs, result, 
                    time.time() - start
                )
                print("get programs", len(programs), flush=True)
                solutions = solutions.union(set(programs))
                print("get solutions", len(solutions), flush=True)
                if len(solutions) >= n:
                    break

                self._encoder.block_prev(perms)
                result = self._encoder.solve()

            if self._encoder._path_len > DEFAULT_LENGTH_LIMIT:
                print("Exceeding the default length limit")
                break

            if len(solutions) >= n:
                break

            print("No path found, incrementing the path length", flush=True)
            self._encoder.increment()
            self._encoder.set_final(output_map)
            # self._encoder.add_all_constraints()

        # write solutions
        with open("data/solutions.pkl", "wb") as f:
            pickle.dump(solutions, f)

        # write annotated entries
        with open("data/annotated_entries.pkl", "wb") as f:
            pickle.dump(self._entries, f)

        return solutions

    def _add_transitions(self):
        unique_entries = self._group_transitions(self._entries)
        lst = [
            # "/v1/subscriptions_POST",
            # "/v1/prices_GET",
            # "projection(/v1/prices_GET_response, data.[?])_",
            # "projection(price, id)_",
            "/v1/products_POST",
            "/v1/prices_POST",
            "/v1/invoiceitems_POST",
            # "/conversations.open_POST",
            # "/users.lookupByEmail_GET",
            # "/chat.postMessage_POST",
        ]

        for name in lst:
            e = self._entries.get(name)
            print('-----')
            print(name)
            print([(p.arg_name, p.type.name, p.is_required) for p in e.parameters])
            print(e.response.type, flush=True)

        for name, e in self._entries.items():
            self._program_generator.add_signature(name, e)

        self._unique_entries = unique_entries

    def _group_transitions(self, transitions):
        # group projections with the same input and output
        results = {}
        for proj, e in transitions.items():
            param_typs = [p.type.name for p in e.parameters]
            if isinstance(e.response.type, list):
                response_typ = [t.name for t in e.response.type]
            else:
                response_typ = [e.response.type.name]
            key = (tuple(param_typs), tuple(response_typ))
            if key not in self._groups:
                results[proj] = e
                self._groups[key] = [proj]
                self._group_names[proj] = [proj]
            else:
                rep = self._groups[key][0]
                self._groups[key].append(proj)
                self._group_names[rep].append(proj)

        return results