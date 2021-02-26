from collections import defaultdict
import re
import time

from synthesizer.encoder import Encoder
from synthesizer.utils import make_entry_name
from stats.time_stats import TimeStats, STATS_GRAPH
from stats.graph_stats import GraphStats
from synthesizer import params
from openapi import defs
from analyzer.entry import DocEntry, ResponseParameter, RequestParameter
from schemas.schema_type import SchemaType
from program.generator import ProgramGenerator
import config_keys as keys

DEFAULT_LENGTH_LIMIT = 10

class Synthesizer:
    def __init__(self, doc, config, analyzer):
        self._doc = doc
        self._config = config
        self._analyzer = analyzer
        self._encoder = Encoder({})
        self._groups = {}
        self._landmarks = []
        self._program_generator = ProgramGenerator({})

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

        while len(solutions) < n:
            # find the correct path len
            while result is None:
                limit = self._config.get(params.LENGTH_LIMIT, DEFAULT_LENGTH_LIMIT)
                if self._encoder._path_len >= limit:
                    break

                self._encoder.increment(landmarks, output_map)
                result = self._encoder.solve()

            
            # find the solution for a given path len
            while result is not None and len(solutions) < n:
                # print(result)
                # FIXME: better implementation latter
                
                end = time.time()
                programs = self._program_generator.generate_program(
                    result, inputs, outputs[0]
                )
                for p in programs:
                    if p in solutions:
                        continue

                    p.to_graph(graph)
                    solutions.add(p)
                    with open("data/example_results.txt", "a+") as f:
                        f.write(f"#{len(solutions)}")
                        f.write("\n")
                        f.write(f"time: {(end - start): .2f}")
                        f.write("\n")
                        f.write(f"time breakdown:\n{TimeStats._timing}\n")
                        f.write(p.pretty(0))
                        f.write("\n")

                results.append(result)
                if len(solutions) > n:
                    break

                self._encoder.block_prev()
                result = self._encoder.solve()
                
        graph.render(filename="output/programs")
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
        for name, e in entries.items():
            # if e.endpoint == "/conversations.members":
            #     print([(p.type.name, p.is_required) for p in e.parameters])
            #     print([(p.type.name, p.is_required) for p in e.responses])

            self._encoder.add_transition(e)
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
                entry = self._create_entry(endpoint, method, method_def)
                
                # set parameter and response types
                for p in entry.parameters:
                    self._analyzer.set_type(p)
                for p in entry.responses:
                    # if p.arg_name == "response_metadata" and p.func_name == "/conversations.list":
                    #     print(p.type)
                    self._analyzer.set_type(p)
                    # if p.arg_name == "response_metadata" and p.func_name == "/conversations.list":
                    #     print(p.type)

                # store results
                entry_name = make_entry_name(endpoint, method)
                entries[entry_name] = entry

                # if endpoint == "/conversations.members":
                #     print(entry)

        return entries

    def _create_entry(self, endpoint, method, entry_def):
        return DocEntry.from_openapi(
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

        return self._group_transitions(projections)

    def _group_transitions(self, transitions):
        # group projections with the same input and output
        results = {}
        for proj, e in transitions.items():
            param_typs = [p.type.name for p in e.parameters]
            response_typs = [p.type.name for p in e.responses]
            key = (tuple(param_typs), tuple(response_typs))
            if key not in self._groups:
                results[proj] = e
                self._groups[key] = [proj]
            else:
                self._groups[key].append(proj)

        return results

    def _create_projection(self, obj_name, obj_def):
        results = {}
        if defs.DOC_ONEOF in obj_def:
            one_ofs = obj_def.get(defs.DOC_ONEOF)
            for s in one_ofs:
                projection = self._create_projection(obj_name, s)
                results.update(projection)
                # obj_entry = projection.pop(obj_name)
                # obj_entry.func_name = f"{obj_entry.func_name}_{i}"
                # results[obj_entry.func_name] = obj_entry
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
                # if obj_name == "objs_conversation" and name == "priority":
                #     print(proj_in.type.name, proj_out.type.name)
                #     raise Exception
                entry = DocEntry(endpoint, "", [proj_in], [proj_out])
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

        return self._group_transitions(filters)

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
                    entry = DocEntry(endpoint, "", filter_in, [filter_out])
                    results[endpoint+":"] = entry

        return results