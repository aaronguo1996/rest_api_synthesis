from collections import defaultdict
import multiprocessing as mp
import itertools
import pickle
import re
import time
import os

from analyzer.entry import TraceEntry, ResponseParameter, RequestParameter
from openapi import defs
from program.generator import ProgramGenerator
from program.program import ProgramGraph, all_topological_sorts
from schemas.schema_type import SchemaType
from stats.graph_stats import GraphStats
from stats.time_stats import TimeStats, STATS_GRAPH
from synthesizer.hypergraph_encoder import HyperGraphEncoder
from synthesizer.petrinet_encoder import PetriNetEncoder
from synthesizer.utils import make_entry_name, DEFAULT_LENGTH_LIMIT
import config_keys as keys

STATE_FULL = -1
STATE_NORMAL = 0

class Synthesizer:
    def __init__(self, doc, config, analyzer, exp_dir):
        self._doc = doc
        self._config = config
        self._analyzer = analyzer
        self._groups = {}
        self._group_names = {}
        self._landmarks = []
        self._unique_entries = {}
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
            f.write(p.pretty(0))
            f.write("\n")

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
        # print("topo sort results:", perms)
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
        
        if not perm_indices:
            perm_indices = [list(range(len(result)))]

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
        # graph = GraphStats()
        input_map = defaultdict(int)
        for _, typ in inputs.items():
            input_map[typ.name] += 1

        output_map = defaultdict(int)
        for typ in outputs:
            output_map[typ.name] += 1

        start = time.time()
        self._encoder.init(input_map)
        self._encoder._set_final(output_map)
        
        while len(solutions) < n:
            result = self._encoder.solve()
            while result is not None:
                print("Find path", result, flush=True)
                programs, perms = self._generate_solutions(
                    0, inputs, outputs, result, 
                    time.time() - start
                )
                # print("get programs", programs, flush=True)
                solutions = solutions.union(set(programs))
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
            self._encoder._set_final(output_map)

        # write solutions
        with open("data/solutions.pkl", "wb") as f:
            pickle.dump(solutions, f)

        # write annotated entries
        with open("data/annotated_entries.pkl", "wb") as f:
            pickle.dump(self._entries, f)

        return solutions

    def _add_transitions(self):
        entries = self._create_entries()
        projections = self._create_projections()
        filters = self._create_filters()
        entries.update(projections)
        entries.update(filters)
        self._entries = entries
        unique_entries = self._group_transitions(entries)

        # slack logs
        # lst = [
        #     "/conversations.list:GET",
        #     # "projection(objs_conversation_0, id):",
        #     "projection(/conversations.list_response, channels):",
        #     "/conversations.members:GET",
        #     "/users.info:GET",
        #     '/users.list:GET',
        #     # 'filter(objs_conversation_9, objs_conversation_9.name):',
        #     # "projection(objs_user.profile, email):",
        #     # "projection(objs_conversation_9, creator):",
        #     "projection(/users.info_response, user):",
        #     # "projection(objs_user_0, profile):",
        #     "projection(/conversations.members_response, members):",
        #     'projection(/users.conversations_response, channels):',
        #     # "projection(objs_conversation, name):",
        #     # "projection(objs_conversation, id):",
        #     # "projection(objs_user.profile, email):",
        #     # 'projection(/conversations.members_response, response_metadata):'
        # ]

        # stripe logs
        lst = [
            "/v1/products_POST",
            "/v1/customers_GET",
            "/v1/customers/{customer}_GET",
            "/v1/prices_POST",
            "/v1/invoiceitems_POST",
            "projection(customer, email)_",
            "projection(product, id)_",
            "projection(price, id)_",
            "/v1/subscriptions_POST",
            "projection(charge, invoice)_",
            "projection(invoice, id)_",
            "/v1/invoices_GET",
            "projection(subscription, latest_invoice)_",
            "/v1/subscriptions/{subscription_exposed_id}_POST",
        ]
        for name in lst:
            e = self._entries.get(name)
            print('-----')
            print(name)
            print([(p.arg_name, p.type.name) for p in e.parameters])
            print(e.response.type, flush=True)
            
        # only add unique entries into the encoder
        # for name, e in unique_entries.items():
        #     self._add_transition(e)

        for name, e in entries.items():
            self._program_generator.add_signature(name, e)

        self._unique_entries = unique_entries

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
                if method.lower() == "delete": # do not handle delete for now
                    continue

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
            if re.search(r"objs_ref_\d+", obj_name):
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
                typ_path = obj_name.split('.')
                # root_typ = typ_path[0]
                if len(typ_path) > 1:
                    to_field_typ = '.'.join(typ_path[1:] + [name])
                else:
                    to_field_typ = name

                in_name = None

                parts = self._analyzer.type_partitions.get(obj_name)
                if parts is not None:
                    for i, part in enumerate(parts):
                        for p in part:
                            if to_field_typ == p[:len(to_field_typ)]:
                                in_name = f"{obj_name}_{i}"
                                break
                            if in_name is not None:
                                break
                        else:
                            in_name = None

                if in_name is None:
                    in_name = obj_name

                endpoint = f"projection({in_name}, {name})"
                proj_in = RequestParameter(
                    "", "obj", endpoint, True, SchemaType(in_name, None), None
                )
                proj_out = ResponseParameter(
                    "", "field", endpoint,
                    [], True, 0, SchemaType(f"{obj_name}.{name}", None), None
                )
                # FIXME: this is probably wrong in other cases
                proj_in = self._analyzer.find_same_type(proj_in)
                proj_out = self._analyzer.find_same_type(proj_out)
                entry = TraceEntry(endpoint, "", [proj_in], proj_out)
                result_key = make_entry_name(endpoint, "")
                results[result_key] = entry

                # add nested objects
                if (prop.get(defs.DOC_TYPE) == "object" or
                    defs.DOC_PROPERTIES in prop):
                    projections = self._create_projection(
                        f"{proj_out.type.name}.{name}", prop)
                    results.update(projections)

        return results

    def _create_filters(self):
        filters = {}
        objs = self._doc.get(defs.DOC_COMPONENTS).get(defs.DOC_SCHEMAS)
        for obj_name, obj_def in objs.items():
            # skip temporary types defined by ourselves
            if re.search(r"objs_ref_\d+", obj_name):
                continue

            filter_entries = self._create_filter(obj_name, obj_name, obj_def)
            filters.update(filter_entries)

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
                    

                    typ_path = field_name.split('.')
                    if len(typ_path) > 1:
                        to_field_typ = '.'.join(typ_path[1:] + [name])
                    else:
                        to_field_typ = name

                    in_name = None
                    parts = self._analyzer.type_partitions.get(obj_name)
                    opt_ins = []
                    if parts is not None:
                        for i, part in enumerate(parts):
                            if to_field_typ in part:
                                in_name = f"{obj_name}_{i}"
                                break
                            else:
                                in_name = None

                        for j in range(len(parts)):
                            if j != i:
                                param = RequestParameter(
                                    "", "obj", 
                                    f"filter({in_name}, {in_name}.{to_field_typ})", 
                                    False, 
                                    SchemaType(f"{obj_name}_{j}", None), None
                                ) 
                                opt_ins.append(param)

                        out_type = [
                            SchemaType(f"{obj_name}_{j}", None)
                            for j in range(len(parts))
                        ]

                    if in_name is None:
                        in_name = obj_name
                        out_type = SchemaType(obj_name, None)

                    endpoint = f"filter({in_name}, {in_name}.{to_field_typ})"
                    filter_in = [
                        RequestParameter(
                            "", "obj", endpoint, True, 
                            SchemaType(in_name, None), None
                        ),
                        RequestParameter(
                            "", "field", endpoint,
                            True, SchemaType(f"{field_name}.{name}", None), None
                        )
                    ] + opt_ins
                    filter_out = ResponseParameter(
                        "", "obj", endpoint,
                        [], True, 1, out_type, None
                    )
                    filter_in = [self._analyzer.find_same_type(fin)
                        for fin in filter_in]
                    
                    if parts is None:
                        filter_out = self._analyzer.find_same_type(filter_out)
                        
                    entry = TraceEntry(endpoint, "", filter_in, filter_out)
                    result_key = make_entry_name(endpoint, "")
                    results[result_key] = entry

        return results
