from concurrent.futures import ThreadPoolExecutor, as_completed, TimeoutError
from graphviz import Digraph
from urllib.parse import urlparse
from xeger import Xeger
import json
import logging
import os
import pickle
import random
import time

from analyzer.entry import ErrorResponse, RequestParameter, ResponseParameter, TraceEntry
from openapi import defs
from witnesses.dependencies import DependencyResolver, EndpointProducer, EnumProducer
from witnesses.error import EndpointNotFoundError, ExceedDepthLimit
from witnesses.request import Connection
from synthesizer.utils import make_entry_name

RESULT_FILE = os.path.join("output/", "results.pkl")

class Result:
    def __init__(self, method, endpoint, code, response, params):
        self.method = method
        self.endpoint = endpoint
        self.return_code = code
        
        if code < defs.CODE_ERROR:
            self.has_error = False
            self.response_body = json.loads(response)
        else:
            self.has_error = True
            self.response_body = {"error": response}

        if self.response_body.get("error") is not None:
            self.has_error = True

        self.request_params = params

    def __eq__(self, other):
        return (
            self.return_code == other.return_code and
            self.response_body == other.response_body and
            self.request_params == other.request_params
        )

    def __str__(self):
        return str((self.return_code, self.response_body, self.request_params))

    def __repr__(self):
        return self.__str__()


class BasicGenerator:
    def __init__(self, hostname, base_path, endpoint, method, ep_method_def,
        token, skip_fields, value_dict, 
        real_dependencies, annotations, depth_limit):
        # create a logger for this module
        self._logger = logging.getLogger(__name__)
        self._endpoint = endpoint
        self._method = method
        self._ep_method_def = ep_method_def
        self._hostname = hostname
        self._base_path = base_path
        self._value_dict = value_dict
        self._conn = Connection(hostname, base_path)
        self._generateing_depth_limit = depth_limit
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

        if param_type == defs.TYPE_STRING:
            regex = defined_regex or r"^[a-zA-Z0-9]{10,}$"
            return x.xeger(regex)
        elif param_type == defs.TYPE_ARRAY:
            return []
        elif param_type == defs.TYPE_INT:
            int_range = defined_regex or range(0,5)
            return random.choice(int_range)
        elif param_type == defs.TYPE_NUM:
            float_range = defined_regex or (0, 1)
            return random.uniform(*float_range)
        elif param_type == defs.TYPE_BOOL:
            return random.choice([True, False])
        elif param_type == defs.TYPE_OBJECT:
            return {}
        else:
            print("Cannot generate random values for type", param_type, "with name", param_name)
            return None

    def _generate_get(self, depth):
        params = self._ep_method_def.get(defs.DOC_PARAMS, [])
        return self._generate_params(depth + 1, params, 2)

    def _generate_post(self, depth):
        header_params = self._ep_method_def.get(defs.DOC_PARAMS, [])
        headers = self._generate_params(depth + 1, header_params, 2)
        
        request_body = self._ep_method_def.get(defs.DOC_REQUEST)
        body = {}
        if request_body:
            body_def = request_body.get(defs.DOC_CONTENT).get(defs.HEADER_JSON)
            if not body_def:
                body_def = request_body.get(defs.DOC_CONTENT).get(defs.HEADER_FORM)
            body_schema = body_def.get(defs.DOC_SCHEMA)
            requires = body_schema.get(defs.DOC_REQUIRED, [])
            body_params = body_schema.get(defs.DOC_PROPERTIES, {})

            body_param_lst = []
            for param_name in body_params:
                param = body_params[param_name]
                param.update({
                    defs.DOC_NAME: param_name,
                    defs.DOC_REQUIRED: param_name in requires,
                })
                body_param_lst.append(param)
            body = self._generate_params(depth + 1, body_param_lst, 2)    

        body.update(headers)
        return body

    def _generate_params(self, depth, params):
        raise NotImplementedError

    def _generate_one(self, depth):
        if depth > self._generateing_depth_limit:
            raise ExceedDepthLimit

        self._logger.debug(f"generateing for endpoint {self._endpoint}"
            f" at depth {depth}")

        # get parameters
        if self._method.upper() == defs.METHOD_GET:
            # parameters are defined in the "parameters" section
            params = self._generate_get(depth)
            code, response = self._conn.send_and_recv(
                self._endpoint,
                self._method.upper(),
                {
                    defs.HEADER_AUTH: f"{defs.HEADER_BEARER} {self._token}",
                },
                params)
        elif self._method.upper() == defs.METHOD_POST:
            # parameters are defined in both the "parameters" and "requestBody"
            params = self._generate_post(depth)
            code, response = self._conn.send_and_recv(
                self._endpoint,
                self._method.upper(),
                {
                    defs.HEADER_AUTH: f"{defs.HEADER_BEARER} {self._token}",
                },
                params)
        else:
            raise Exception("Unsupported method for generateing:", self._method)

        return Result(self._method, self._endpoint, code, response, params)

    def run(self):
        # try:
            return self._generate_one(1)
        # except Exception as e:
        #     self._logger.debug(f"Exception: {e}")
        #     return None

class SaturationThread(BasicGenerator):
    def __init__(self, hostname, base_path, endpoint, method, ep_method_def, 
        token, skip_fields, value_dict, 
        real_dependencies, annotations, analyzer, depth_limit):
        super().__init__(
            hostname, base_path,
            endpoint, method, ep_method_def, token, skip_fields, value_dict,
            real_dependencies, annotations, depth_limit)
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
            self._logger.debug(f"Trying the producer {producer.endpoint}"
                f" with path {producer.path}")
            resp = ResponseParameter(
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
                return random.choice(list(bank))
            else:
                return None
        else:
            self._logger.debug(f"Trying the parameter value {producer}")
            return producer

    # get params from bank
    def _generate_params(self, _, params, n):
        param_dict = {}

        req_params = []
        opt_params = []
        for param_obj in params:
            required = param_obj.get(defs.DOC_REQUIRED)
            if required:
                req_params.append(param_obj)
            else:
                opt_params.append(param_obj)

        picked_num = random.randint(0, n)
        picked_num = min(picked_num, len(opt_params))
        picked_opt_params = random.sample(opt_params, picked_num)

        for param_obj in req_params + picked_opt_params:
            param_name = param_obj.get(defs.DOC_NAME)
            if param_name in self._skip_fields:
                continue

            param_schema = param_obj.get(defs.DOC_SCHEMA)
            if param_schema: # for parameters
                param_type = param_schema.get(defs.DOC_TYPE)
            else: # for requestBody
                param_type = param_obj.get(defs.DOC_TYPE)

            self._logger.debug(f"Filling for parameter {param_name}")
            param = RequestParameter(
                self._method,
                param_name, 
                self._endpoint, 
                required, 
                None, 
                None
            )
            if self._analyzer.dsu.find(param):
                self._logger.debug(f"Trying fill parameter {param_name} by real dependencies")
                # if we already have the value bank for this variable
                param_value_bank = self._analyzer.dsu.get_value_bank(param)
                param_val = random.choice(list(param_value_bank))
            elif (self._endpoint, param_name) in self._annotations:
                self._logger.debug(f"Trying fill parameter {param_name} by annotated dependencies")
                # try inferred dependencies but do not create new values
                producers = self._annotations.get(
                    (self._endpoint, param_name), [])
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

            # if we cannot find a value for an optional arg, skip it
            if not param_val and not required and param_type == "string":
                continue

            if not param_val:
                self._logger.debug(f"No dependency found for {(self._endpoint, param_name)}. Trying random values.")
                param_val = self._random_from_type(param_name, param_type)

            if param_val is not None:
                param_dict[param_name] = param_val

        return param_dict

class WitnessGenerator:
    def __init__(self, openapi_doc, analyzer, token, val_dict, ann_path, exp_dir,
        depth_limit=3, path_to_defs="#/components/schemas", 
        skip_fields=[], plot_freq = 1):
        self._logger = logging.getLogger(__name__)
        # parse the spec into dict
        self._doc = openapi_doc
        self._paths = self._doc.get(defs.DOC_PATHS)

        # resolve dependencies from the spec
        resolver = DependencyResolver(openapi_doc)
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
        self._depth_limit = depth_limit
        self._exp_dir = exp_dir

        # start a new connection for generateing
        servers = self._doc.get("servers")
        server = servers[0].get("url")
        server_result = urlparse(server)
        self._hostname = server_result.netloc
        self._base_path = server_result.path
        self._logger.debug(f"Get hostname: {self._hostname}"
            f" and basePath: {self._base_path}")

        self._path_to_defs = path_to_defs
        self._skip_fields = skip_fields

        self._error_buckets = set()
        self._covered_endpoints = set()
        self._plot_freq = plot_freq
        # self._annotations = annotations

    def _add_new_result(self, result: Result):
        requests = []
        for name, val in result.request_params.items():
            request = RequestParameter(
                result.method, name, result.endpoint, True, None, val)
            requests.append(request)
            self._analyzer.insert(request)

        if result.has_error:
            response = ErrorResponse(result.response_body)
        else:
            response = ResponseParameter(
                result.method, "", result.endpoint, [], True, 0, None, result.response_body)

        witness_path = os.path.join(self._exp_dir, 'traces.pkl')
        with open(witness_path, 'rb') as f:
            entries = pickle.load(f)
            print(len(entries))
            entries.append(
                TraceEntry(
                    result.endpoint,
                    result.method,
                    requests,
                    response,
                ))

        with open(witness_path, 'wb') as f:
            pickle.dump(entries, f)
            
        if result.has_error:
            return

        responses, _ = response.flatten(self._path_to_defs, self._skip_fields)
        for r in responses:
            self._analyzer.insert(r)

    def _run_all(self, generate_type, endpoints, iterations, timeout):
        for i in range(1, iterations+1):
            # fire many threads at one time
            with ThreadPoolExecutor(max_workers=8) as executor: # TODO: change this to configuration
                futures = []
                results = []
                for ep in endpoints:
                    ep_def = self._paths.get(ep)
                    if not ep_def:
                        raise EndpointNotFoundError(ep)

                    for method, ep_method_def in ep_def.items():
                        if method == "delete": # TODO: skip delete for now
                            continue

                        self._logger.debug(f"Submit job for {method} {ep}")
                        t = generate_type(
                            self._hostname, self._base_path, 
                            ep, method, ep_method_def,
                            self._token,
                            self._skip_fields,
                            self._value_dict, 
                            self._real_dependencies,
                            self._annotations,
                            self._analyzer, self._depth_limit)
                        futures.append(executor.submit(t.run))
                for future in as_completed(futures):
                    try:
                        results.append(future.result(timeout=timeout))
                    except TimeoutError:
                        print("We lacked patience and got a TimeoutError")
                    # except Exception as e:
                    #     print(e)
                    #     print("we get other exceptions")

            # self._logger.debug("===============Start to write new results into DSU")
            for generate_result in results:
                if generate_result:
                    self._add_new_result(generate_result)

            resolver = DependencyResolver(self._doc)
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
                self._covered_endpoints.add(r.endpoint)
        
        coverage = cnt / len(results)
        self._logger.info(f"Coverage at iteration {i}: {coverage}")
        return coverage

    def saturate_all(self, endpoints, iterations, timeout):
        if os.path.exists(RESULT_FILE):
            os.remove(RESULT_FILE)

        self._run_all(SaturationThread, endpoints, iterations, timeout)

    def get_param_names(self, ep_method_def):
        header_params = ep_method_def.get(defs.DOC_PARAMS)
        if header_params:
            param_names = [p[defs.DOC_NAME] for p in header_params]
        else:
            param_names = []

        request_body = ep_method_def.get(defs.DOC_REQUEST)
        if request_body:
            body_def = request_body.get(defs.DOC_CONTENT).get(defs.HEADER_JSON)
            if not body_def:
                body_def = request_body.get(defs.DOC_CONTENT).get(defs.HEADER_FORM)
            body_schema = body_def.get(defs.DOC_SCHEMA)
            body_params = body_schema.get(defs.DOC_PROPERTIES, {})
            param_names += list(body_params.keys())

        return param_names

    def to_graph(self, endpoints, filename):
        dot = Digraph(strict=True)
        
        # add inferred dependencies as dashed edges in the graph
        # print(self._inferred_dependencies.get("user"))
        for ep in endpoints:
            # print(ep)
            ep_def = self._paths.get(ep)
            for _, ep_method_def in ep_def.items():
                param_names = self.get_param_names(ep_method_def)
                for name in param_names:
                    producers = self._annotations.get(name, [])
                    for producer in producers:
                        resp = ResponseParameter(
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
                            if isinstance(param, ResponseParameter):
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
