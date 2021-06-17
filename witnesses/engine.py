from concurrent.futures import ThreadPoolExecutor, as_completed, TimeoutError
from graphviz import Digraph
from xeger import Xeger
import json
import logging
import os
import pickle
import random
import re
import time

from analyzer.entry import ErrorResponse, Parameter, TraceEntry
from analyzer.utils import path_to_name, name_to_path
from openapi import defs
from schemas import types
from synthesizer.utils import make_entry_name
from witnesses.dependencies import DependencyResolver, EndpointProducer, EnumProducer
from witnesses.request import Connection
import consts
import witnesses.utils as utils

RESULT_FILE = os.path.join("output/", "results.pkl")

class Result:
    def __init__(self, entry, code, params, response):
        self.entry = entry
        self.return_code = code

        if code < defs.CODE_ERROR:
            self.has_error = False
            self.response_body = json.loads(response)
        else:
            self.has_error = True
            self.response_body = {"error": response}

        if self.response_body.get("error") is not None:
            self.has_error = True

        self.request_params = {}
        for name, val in params.items():
            path = name_to_path(name)
            self.request_params = utils.add_as_object(
                self.request_params, path, val
            )

    def __eq__(self, other):
        return (
            self.return_code == other.return_code and
            self.response_body == other.response_body and
            self.request_params == other.request_params
        )

    def __str__(self):
        return str((self.return_code, self.response_body, self.request_params))

    def __repr__(self):
        return self.__dict__


class BasicGenerator:
    def __init__(self, hostname, base_path, entry,
        token, skip_fields, value_dict,
        real_dependencies, annotations, opt_param_indices):
        # create a logger for this module
        self._logger = logging.getLogger(__name__)
        self._entry = entry
        self._hostname = hostname
        self._base_path = base_path
        self._value_dict = value_dict
        self._conn = Connection(hostname, base_path)
        self._opt_param_indices = opt_param_indices
        self._real_dependencies = real_dependencies
        self._annotations = annotations
        self._token = token
        self._skip_fields = skip_fields

    def _random_from_type(self, param_name, param_type):
        x = Xeger(limit=20)
        defined_regex = None
        if param_name in self._value_dict:
            self._logger.debug(f"Witness {param_name} in the value_dict")
            defined_regex = self._value_dict.get(param_name)

        if isinstance(param_type, types.ArrayType):
            return []
        elif isinstance(param_type, types.PrimInt):
            int_range = defined_regex or range(0, 1000)
            return random.choice(int_range)
        elif isinstance(param_type, types.PrimNum):
            float_range = defined_regex or (0, 1)
            return random.uniform(*float_range)
        elif isinstance(param_type, types.PrimBool):
            return random.choice([True, False])
        elif isinstance(param_type, types.ObjectType):
            return {}
        elif isinstance(param_type, types.PrimEnum):
            return random.choice(param_type.enums)
        else:
            print(param_name, type(param_type))
            regex = defined_regex or r"^[a-z0-9]{10,}$"
            return x.xeger(regex)

    def _generate_params(self, params):
        raise NotImplementedError

    def _generate_one(self):
        entry = self._entry
        self._logger.debug(f"generating for endpoint {entry.endpoint}")

        try:
            params = self._generate_params(
                entry.content_type,
                entry.parameters,
                self._opt_param_indices)
            code, response = self._conn.send_and_recv(
                entry.endpoint,
                entry.method.upper(),
                entry.content_type,
                {
                    defs.HEADER_CONTENT: entry.content_type,
                    defs.HEADER_AUTH: f"{defs.HEADER_BEARER} {self._token}",
                },
                params,
            )
            return Result(entry, code, params, response)
        except:
            return None


    def run(self):
        return self._generate_one()

class SaturationThread(BasicGenerator):
    def __init__(self, hostname, base_path, entry,
        token, skip_fields, value_dict,
        real_dependencies, annotations, analyzer, opt_param_indices):
        super().__init__(
            hostname, base_path,
            entry, token, skip_fields, value_dict,
            real_dependencies, annotations, opt_param_indices)
        self._analyzer = analyzer

    def _try_producer(self, producer):
        if isinstance(producer, EnumProducer):
            if producer.combine:
                n = random.randint(1, len(producer.values))
                selected = random.sample(producer.values, n)
                return ','.join([str(s) for s in selected])
            else:
                return random.choice(producer.values)
        elif isinstance(producer, EndpointProducer):
            self._logger.debug(f"Trying the producer {producer.endpoint} with path {producer.path}")
            resp = Parameter(
                producer.method,
                producer.path[-1],
                producer.endpoint,
                producer.path,
                True,
                0,
                None,
                None
            )
            bank = self._analyzer.dsu.get_value_bank(resp)
            if bank:
                self._logger.debug(f"Find a value from the producer {producer.endpoint} with path {producer.path}")
                return random.choice(list(bank))
            else:
                self._logger.debug(f"Didn't find a value from the producer {producer.endpoint} with path {producer.path}")
                return None
        else:
            self._logger.debug(f"Trying the parameter value {producer}")
            return producer

    def _generate_object(self, param):
        param_type = param.type

        self._logger.debug(f"Generating string values for {param.arg_name} with path {param.path}")
        if param.arg_name == defs.INDEX_ANY:
            arg_name = param.path[-2]
        else:
            arg_name = param.arg_name

        if self._analyzer.dsu.find(param) and arg_name != defs.DOC_NAME and arg_name != defs.DOC_TYPE:
            self._logger.debug(
                f"Trying fill parameter {arg_name} by real dependencies")
            # if we already have the value bank for this variable
            param_value_bank = self._analyzer.dsu.get_value_bank(param)
            param_val = random.choice(list(param_value_bank))
        elif (param_type.name in self._analyzer.type_values and
            arg_name != defs.DOC_NAME):
            self._logger.debug(
                f"Trying fill parameter {arg_name} with object values of type {param_type.name}")
            param_value_bank = self._analyzer.type_values[param_type.name]
            param_val = random.choice(list(param_value_bank))
        elif ((self._entry.endpoint, arg_name) in self._annotations and
           arg_name != defs.DOC_NAME):
            self._logger.debug(
                f"Trying fill parameter {arg_name}"
                f" by annotated dependencies")
            # try inferred dependencies but do not create new values
            producers = self._annotations.get(
                (self._entry.endpoint, arg_name), [])
            param_value_bank = set()
            for producer in producers:
                v = self._try_producer(producer)
                if v:
                    param_value_bank.add(v)

            if param_value_bank:
                param_val = random.choice(list(param_value_bank))
            else:
                param_val = None
        else:
            param_val = None

        if not param_val:
            self._logger.debug(
                f"No dependency found for {(self._entry.endpoint, arg_name)}. "
                f"Trying random values.")
            param_val = self._random_from_type(arg_name, param_type)

        return param_val

    # get params from bank
    def _generate_params(self, content_type, params, opt_indices):
        param_dict = {}

        req_params, opt_params = utils.filter_optional(params)
        selected_opt_params = list(map(lambda idx: opt_params[idx], opt_indices))
        for param in req_params + selected_opt_params:
            if (param.arg_name == defs.DOC_TOKEN or
                param.arg_name == defs.DOC_EXPAND):
                continue

            param_val = self._generate_object(param)

            # if we cannot find a value for an arg, skip it
            if param_val is not None:
                key = path_to_name(param.path)
                if content_type == defs.HEADER_JSON:
                    param_dict = utils.add_as_object(
                        param_dict, param.path, param_val)
                else:
                    param_dict[key] = param_val
            else:
                print("cannot find a value for param", param)

        return param_dict

class WitnessGenerator:
    def __init__(self, openapi_entries, hostname, base_path,
        entries, analyzer, token, val_dict, ann_path, exp_dir,
        path_to_defs=consts.REF_PREFIX,
        skip_fields=[], plot_freq = 1):
        self._logger = logging.getLogger(__name__)
        # parse the spec into dict
        self._doc_entries = openapi_entries
        self._hostname = hostname
        self._base_path = base_path
        self._entries = entries

        # resolve dependencies from the spec
        resolver = DependencyResolver(openapi_entries)
        self._analyzer = analyzer
        groups = analyzer.analysis_result()

        with open(ann_path, 'r') as f:
            annotations = json.load(f)

        dependencies = resolver.get_dependencies_from_annotations(annotations)
        self._annotations = dependencies
        self._real_dependencies = resolver.get_dependencies_from_groups(groups)

        # value patterns injected by users
        self._token = token
        self._value_dict = val_dict
        self._exp_dir = exp_dir

        # start a new connection for generating
        self._logger.debug(f"Get hostname: {self._hostname} and basePath: {self._base_path}")

        self._path_to_defs = path_to_defs
        self._skip_fields = skip_fields

        self._error_buckets = set()
        self._covered_endpoints = set()
        self._plot_freq = plot_freq
        # self._annotations = annotations

    def _add_new_result(self, entries, result: Result):
        params = []
        entry = self._doc_entries[result.entry.endpoint][result.entry.method]
        if len(entry.parameters) == 1 and entry.parameters[0].arg_name is None:
            match_param = entry.parameters[0]
            request = Parameter(
                entry.method, None, entry.endpoint, [],
                match_param.is_required, None, 
                match_param.type, result.response_body)
            params.append(request)
            requests, values = request.flatten(
                self._path_to_defs,
                self._skip_fields
            )
            
            if not result.has_error and result.response_body:
                self._analyzer.insert_value(values)
                for request in requests:
                    self._analyzer.insert(request)
        else:
            for name, val in result.request_params.items():
                # find the corresponding param type
                match_param = None
                for param in entry.parameters:
                    if param.arg_name == name:
                        match_param = param
                        break

                if match_param is None:
                    raise Exception(name, val, "does not have a matching param from params", 
                        [p.arg_name for p in entry.parameters],
                        result.entry.endpoint,
                        result.entry.method)

                request = Parameter(
                    entry.method, name, entry.endpoint, [name],
                    match_param.is_required, None, match_param.type, val)
                params.append(request)
                requests, values = request.flatten(
                    self._path_to_defs,
                    self._skip_fields
                )
                if not result.has_error and result.response_body:
                    self._analyzer.insert_value(values)
                    for request in requests:
                        self._analyzer.insert(request)

        if result.has_error:
            response = ErrorResponse(result.response_body)
        else:
            response = Parameter(
                entry.method, "", entry.endpoint, [],
                True, 0, entry.response.type, result.response_body)
        
        if not result.has_error and result.response_body:
            responses, values = response.flatten(
                self._path_to_defs,
                self._skip_fields
            )
            self._analyzer.insert_value(values)
            for r in responses:
                self._analyzer.insert(r)

        entries.append(
            TraceEntry(
                entry.endpoint, 
                entry.method, 
                entry.content_type,
                params, response
            ))
        return entries

    def _run_all(self, generate_type, endpoints, iterations, timeout, max_opt_params):
        for i in range(1, iterations+1):
            # fire many threads at one time
            with ThreadPoolExecutor(max_workers=8) as executor: # TODO: change this to configuration
                futures = []
                results = []

                for entry in self._entries.values():
                    # skip delete methods
                    if entry.method.upper() == defs.METHOD_DELETE:
                        continue

                    # skip projections
                    if re.search(r"^projection(.*, .*)$", entry.endpoint):
                        continue

                    self._logger.debug(f"Submit job for {entry.method} {entry.endpoint}")
                    num_params = utils.num_optional_params(entry)

                    def generate_opt_param_subsets(num_params, num_choose, indices):
                        if num_params == 0 or num_choose == 0:
                            t = generate_type(
                                self._hostname,
                                self._base_path,
                                entry,
                                self._token,
                                self._skip_fields,
                                self._value_dict,
                                self._real_dependencies,
                                self._annotations,
                                self._analyzer,
                                indices)
                            futures.append(executor.submit(t.run))
                            return

                        generate_opt_param_subsets(
                            num_params - 1, num_choose, indices)
                        generate_opt_param_subsets(
                            num_params - 1, num_choose - 1,
                            [num_params - 1] + indices)

                    generate_opt_param_subsets(
                        num_params,
                        min(num_params, max_opt_params), [])

                for future in as_completed(futures):
                    try:
                        results.append(future.result(timeout=timeout))
                    except TimeoutError:
                        print("We lacked patience and got a TimeoutError")

            witness_path = os.path.join(self._exp_dir, consts.FILE_TRACE)
            with open(witness_path, 'rb') as f:
                entries = pickle.load(f)
                print(len(entries))

            for generate_result in results:
                if generate_result:
                    entries = self._add_new_result(entries, generate_result)

            with open(witness_path, 'wb') as f:
                pickle.dump(entries, f)

            resolver = DependencyResolver(self._doc_entries)
            groups = self._analyzer.analysis_result()
            self._real_dependencies = resolver.get_dependencies_from_groups(groups)

            if i % self._plot_freq == 0:
                self.to_graph(endpoints, f"dependencies_{i}")

            self.get_coverage(i, results)
            self.write_results(i, results)

            # rest between iterations to avoid spoof
            time.sleep(60)

    def write_results(self, i, results):
        with open(RESULT_FILE, "ab+") as f:
            pickle.dump({
                "Iteration": i,
                "Results": results,
                "Endpoints": self._covered_endpoints,
                "Error buckets": self._error_buckets,
            }, f)

    def bucket_error(self, result):
        if result.has_error:
            self._error_buckets.add((result.code, result.response_body))

    def get_coverage(self, i, results):
        cnt = 0
        for r in results:
            if r and not r.has_error:
                cnt += 1
                self._covered_endpoints.add(r.entry.endpoint)

        coverage = cnt / len(results)
        self._logger.info(f"Coverage at iteration {i}: {coverage}")
        return coverage

    def saturate_all(self, endpoints, iterations, timeout, max_opt_params):
        if os.path.exists(RESULT_FILE):
            os.remove(RESULT_FILE)

        self._run_all(
            SaturationThread,
            endpoints, iterations,
            timeout, max_opt_params)

    def get_param_names(self, ep_method_def):
        params = ep_method_def.parameters
        return [p.arg_name for p in params]

    def to_graph(self, endpoints, filename):
        dot = Digraph(strict=True)

        # add inferred dependencies as dashed edges in the graph
        # print(self._inferred_dependencies.get("user"))
        for ep in endpoints:
            # print(ep)
            ep_def = self._doc_entries.get(ep)
            for _, ep_method_def in ep_def.items():
                param_names = self.get_param_names(ep_method_def)
                for name in param_names:
                    producers = self._annotations.get(name, [])
                    for producer in producers:
                        resp = Parameter(
                            producer.method,
                            producer.path[-1],
                            producer.endpoint,
                            producer.path,
                            True,
                            0,
                            None,
                            None
                        )
                        group = self._analyzer.dsu.get_group(resp)
                        rep = ""
                        for param in group:
                            if param.array_level is not None:
                                path_str = '.'.join(param.path)
                                if not rep or len(rep) > len(path_str):
                                    rep = path_str

                        # if not rep:
                        #     rep = '.'.join(producer.path)

                        if rep and producer.endpoint in endpoints:
                            dot.node(rep, shape="oval")
                            dot.node(ep, shape="rectangle")
                            dot.node(
                                make_entry_name(producer.endpoint, producer.method),
                                shape="rectangle"
                            )
                            dot.edge(rep, ep, style="dashed")
                            dot.edge(
                                make_entry_name(producer.endpoint, producer.method),
                                rep, style="dashed"
                            )

        self._analyzer.to_graph(
            dot,
            endpoints=endpoints,
            allow_only_input=False,
            filename=filename,
        )

        render_filename = os.path.join("output/", filename)
        dot.render(render_filename, view=False)

