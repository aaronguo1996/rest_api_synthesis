from collections import defaultdict
import re
import time
import itertools
import pickle

from synthesizer.encoder import Encoder
from synthesizer.utils import make_entry_name
from stats.time_stats import TimeStats, STATS_GRAPH
from stats.graph_stats import GraphStats
from synthesizer import params
from openapi import defs
from analyzer.entry import TraceEntry, ResponseParameter, RequestParameter
from schemas.schema_type import SchemaType
from program.generator import ProgramGenerator
from program.program import ProgramGraph, all_topological_sorts
import config_keys as keys

DEFAULT_LENGTH_LIMIT = 20

class Synthesizer:
    def __init__(self, doc, config, analyzer):
        self._doc = doc
        self._config = config
        self._analyzer = analyzer
        self._encoder = Encoder({})
        self._groups = {}
        self._group_names = {}
        self._landmarks = []
        self._program_generator = ProgramGenerator({})
        # flags
        self._expand_group = config["synthesis"]["expand_group"]
        self._block_perms = config["synthesis"]["block_perms"]

    @TimeStats(key=STATS_GRAPH)
    def init(self):
        TimeStats.reset()
        self._add_transitions()

    def run(self, landmarks, inputs, outputs):
        self._encoder.init(landmarks, inputs, outputs)
        result = self._encoder.solve()
        while result is None:
            limit = self._config.get(params.LENGTH_LIMIT, DEFAULT_LENGTH_LIMIT)
            if self._encoder._path_len >= limit:
                break

            self._encoder.increment(landmarks, outputs)
            # print(self._encoder._solver.assertions())
            result = self._encoder.solve()
            # print(self._encoder._solver.unsat_core())

        return result

    def _write_solution(self, idx, t, p):
        with open("data/example_results.txt", "a+") as f:
            f.write(f"#{idx}")
            f.write("\n")
            f.write(f"time: {t: .2f}")
            f.write("\n")
            f.write(f"time breakdown:\n{TimeStats._timing}\n")
            f.write(p.pretty(0))
            f.write("\n")

    def _expand_groups(self, result):
        groups = []
        for name in result:
            if self._expand_group:
                e = self._entries.get(name)
                if e is None:
                    raise Exception("Unknown transition")

                param_typs = [p.type.name for p in e.parameters]
                response_typ = e.response.type.name
                key = (tuple(param_typs), response_typ)
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

    def run_n(self, landmarks, inputs, outputs, n):
        solutions = set()
        graph = GraphStats()
        input_map = defaultdict(int)
        for _, typ in inputs.items():
            input_map[typ.name] += 1

        output_map = defaultdict(int)
        for typ in outputs:
            output_map[typ.name] += 1

        start = time.time()
        self._encoder.init(landmarks, input_map, output_map)
        results = []
        result = self._encoder.solve()

        break_flag = False
        while len(results) < n:
            # find the correct path len
            while result is None:
                limit = self._config.get(params.LENGTH_LIMIT, DEFAULT_LENGTH_LIMIT)
                if self._encoder._path_len >= limit:
                    break_flag = True
                    break

                self._encoder.increment(landmarks, output_map)
                result = self._encoder.solve()

            if break_flag:
                break

            # find the solution for a given path len
            while result is not None and len(results) < n:
                # print(result)
                # FIXME: better implementation later
                end = time.time()

                groups = self._expand_groups(result)
                programs = []
                for r in itertools.product(*groups):
                    programs += self._program_generator.generate_program(
                        r, inputs, outputs[0]
                    )

                has_new_solution = False
                all_perms = []
                for p in programs:
                    if p in solutions:
                        continue

                    has_new_solution = True
                    # draw type graphs without transitions
                    p.to_graph(graph)
                    solutions.add(p)
                    # write solutions to file
                    self._write_solution(len(solutions), end-start, p)
                    # generate all topological sorts for blocking
                    if self._block_perms:
                        perms = self._get_topo_sorts(p)
                        all_perms += perms

                if has_new_solution:
                    results.append(result)
                    print(len(solutions), end-start, flush=True)
                else:
                    # print("Duplicate solution:", result)
                    pass

                if len(results) > n:
                    break

                # print(all_perms)
                # convert permutations into indices
                if self._block_perms:
                    perm_indices = []
                    for perms in all_perms:
                        indices = []
                        for tr in perms:
                            for idx, r in enumerate(result):
                                if tr == r[:len(tr)]:
                                    indices.append(idx)
                                    break

                        if len(indices) == len(result):
                            perm_indices.append(indices)
                else:
                    perm_indices = [list(range(len(result)))]

                # print(perm_indices)
                self._encoder.block_prev(perm_indices)
                result = self._encoder.solve()

        graph.render(filename="output/programs")
        
        # write solutions
        with open("data/solutions.pkl", "wb") as f:
            pickle.dump(solutions, f)

        # write annotated entries
        with open("data/annotated_entries.pkl", "wb") as f:
            pickle.dump(self._entries, f)

        return results

    def run_all(self, landmarks, inputs, outputs):
        self._encoder.init(landmarks, inputs, outputs)
        results = []
        result = self._encoder.solve()
        while result is None:
            limit = self._config.get(params.LENGTH_LIMIT, DEFAULT_LENGTH_LIMIT)
            if self._encoder._path_len >= limit:
                break

            self._encoder.increment(landmarks, outputs)
            result = self._encoder.solve()

        while result is not None:
            results.append(result)
            self._encoder.block_prev()
            result = self._encoder.solve()

        return results

    def _add_transitions(self):
        entries = self._create_entries()
        projections = self._create_projections()
        filters = self._create_filters()
        entries.update(projections)
        entries.update(filters)
        self._entries = entries
        unique_entries = self._group_transitions(entries)

        lst = [
            "/conversations.list:GET",
            "filter(objs_conversation, objs_conversation.name):",
            "projection(objs_conversation, id):",
            "/conversations.members:GET",
            "/users.info:GET",
            "projection(objs_user, profile):",
            "projection(objs_user.profile, email):",
            'projection(/conversations.members_response, response_metadata):'
        ]
        for name in lst:
            e = self._entries.get(name)
            print('-----')
            print(name)
            print([p.type.name for p in e.parameters])
            print(e.response.type.name)
            
        # only add unique entries into the encoder
        for name, e in unique_entries.items():
            self._encoder.add_transition(e)

        for name, e in entries.items():
            self._program_generator.add_signature(name, e)

    def _create_entries(self):
        entries = {}

        paths = self._doc.get(defs.DOC_PATHS)
        endpoints = self._config.get(keys.KEY_ENDPOINTS)
        if not endpoints:
            endpoints = paths.keys()

        for endpoint, ep_def in paths.items():
            if endpoint not in endpoints:
                continue

            for method, method_def in ep_def.items():
                results = self._create_entry(endpoint, method, method_def)
                # print("Endpoint:", endpoint, "Results:", results)
                for entry in results:
                    # set parameter and response types
                    for p in entry.parameters:
                        self._analyzer.set_type(p)

                    self._analyzer.set_type(entry.response)

                    # store results
                    entry_name = make_entry_name(entry.endpoint, entry.method)
                    entries[entry_name] = entry

        return entries

    def _create_entry(self, endpoint, method, entry_def):
        return TraceEntry.from_openapi(
            self._config.get(keys.KEY_SKIP_FIELDS),
            endpoint, method, entry_def,
        )

    def _create_projections(self):
        projections = {}
        objs = self._doc.get(defs.DOC_COMPONENTS).get(defs.DOC_SCHEMAS)
        for obj_name, obj_def in objs.items():
            # skip temporary types defined by ourselves
            if re.search(r"obj_ref_\d+", obj_name):
                continue

            projection_entries = self._create_projection(obj_name, obj_def)
            projections.update(projection_entries)

        # return self._group_transitions(projections)
        return projections

    def _group_transitions(self, transitions):
        # group projections with the same input and output
        results = {}
        for proj, e in transitions.items():
            param_typs = [p.type.name for p in e.parameters]
            response_typ = e.response.type.name
            key = (tuple(param_typs), response_typ)
            if key not in self._groups:
                results[proj] = e
                self._groups[key] = [proj]
                self._group_names[proj] = [proj]
            else:
                rep = self._groups[key][0]
                self._groups[key].append(proj)
                self._group_names[rep].append(proj)

        return results

    def _create_projection(self, obj_name, obj_def):
        results = {}
        if defs.DOC_ONEOF in obj_def:
            one_ofs = obj_def.get(defs.DOC_ONEOF)
            for s in one_ofs:
                projection = self._create_projection(obj_name, s)
                results.update(projection)
        elif defs.DOC_PROPERTIES in obj_def:
            properties = obj_def.get(defs.DOC_PROPERTIES)
            for name, prop in properties.items():
                if (prop.get(defs.DOC_TYPE) == "object" or
                    defs.DOC_PROPERTIES in prop):
                    projections = self._create_projection(
                        f"{obj_name}.{name}", prop)
                    results.update(projections)

                endpoint = f"projection({obj_name}, {name})"
                proj_in = RequestParameter(
                    "", "obj", endpoint,
                    True, SchemaType(obj_name, None), None
                )
                proj_out = ResponseParameter(
                    "", "field", endpoint,
                    [], True, 0, SchemaType(f"{obj_name}.{name}", None), None
                )
                proj_in = self._analyzer.find_same_type(proj_in)
                proj_out = self._analyzer.find_same_type(proj_out)
                entry = TraceEntry(endpoint, "", [proj_in], proj_out)
                results[endpoint+":"] = entry

        return results

    def _create_filters(self):
        filters = {}
        objs = self._doc.get(defs.DOC_COMPONENTS).get(defs.DOC_SCHEMAS)
        for obj_name, obj_def in objs.items():
            # skip temporary types defined by ourselves
            if re.search(r"obj_ref_\d+", obj_name):
                continue

            filter_entries = self._create_filter(obj_name, obj_name, obj_def)
            filters.update(filter_entries)

        # return self._group_transitions(filters)
        return filters

    def _create_filter(self, obj_name, field_name, field_def):
        results = {}
        if defs.DOC_ONEOF in field_def:
            one_ofs = field_def.get(defs.DOC_ONEOF)
            for s in one_ofs:
                equi_filter = self._create_filter(obj_name, field_name, s)
                results.update(equi_filter)
                # func_name = f"filter({obj_name}, {field_name})"
                # obj_entry = equi_filter.pop(func_name)
                # obj_entry.func_name = f"{func_name}_{i}"
                # results[func_name] = obj_entry
        elif defs.DOC_PROPERTIES in field_def: # if the object has sub-fields
            properties = field_def.get(defs.DOC_PROPERTIES)
            for name, prop in properties.items():
                if (prop.get(defs.DOC_TYPE) == "object" or
                    defs.DOC_PROPERTIES in prop):
                    projections = self._create_filter(
                        obj_name, f"{field_name}.{name}", prop)
                    results.update(projections)
                else:
                    endpoint = f"filter({obj_name}, {field_name}.{name})"
                    filter_in = [
                        RequestParameter(
                            "", "obj", endpoint,
                            True, SchemaType(obj_name, None), None
                        ),
                        RequestParameter(
                            "", "field", endpoint,
                            True, SchemaType(f"{field_name}.{name}", None), None
                        )
                    ]
                    filter_out = ResponseParameter(
                        "", "obj", endpoint,
                        [], True, 1, SchemaType(obj_name, None), None
                    )
                    filter_in = [self._analyzer.find_same_type(fin)
                        for fin in filter_in]
                    filter_out = self._analyzer.find_same_type(filter_out)
                    entry = TraceEntry(endpoint, "", filter_in, filter_out)
                    results[endpoint+":"] = entry

        return results