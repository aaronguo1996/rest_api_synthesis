from fuzzer.error import EndpointNotFoundError, ExceedDepthLimit, NoParamInBank
from fuzzer.request import Connection
from fuzzer.dependencies import DependencyResolver, Producer
from openapi import defs
from traces.log import RequestParameter, ResponseParameter

from xeger import Xeger
import logging
import random
import json
import os
from urllib.parse import urlparse
from concurrent.futures import ThreadPoolExecutor, as_completed, TimeoutError

class FuzzResult:
    def __init__(self, method, endpoint, code, response, params):
        self.method = method
        self.endpoint = endpoint
        self.return_code = code
        
        if code in defs.SUCCESS_CODES:
            self.has_error = False
            self.response_body = json.loads(response)
        else:
            self.has_error = True
            self.response_body = {"error": response}

        if not self.response_body.get("ok"):
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


class BasicFuzzer:
    def __init__(self, hostname, base_path, 
        endpoint, method, ep_method_def, value_dict):
        # create a logger for this module
        self._logger = logging.getLogger(__name__)
        self._endpoint = endpoint
        self._method = method
        self._ep_method_def = ep_method_def
        self._hostname = hostname
        self._base_path = base_path
        self._value_dict = value_dict
        self._conn = Connection(hostname, base_path)

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
            int_range = defined_regex or range(0,100)
            return random.choice(int_range)
        elif param_type == defs.TYPE_NUM:
            float_range = defined_regex or range(0, 1)
            return random.uniform(*float_range)
        elif param_type == defs.TYPE_BOOL:
            return random.choice([True, False])
        elif param_type == defs.TYPE_OBJECT:
            return {}
        else:
            raise Exception("Cannot generate random values for type", param_type)

    def _fuzz_get(self, depth):
        params = self._ep_method_def.get(defs.DOC_PARAMS)
        return self._fuzz_params(depth + 1, params)

    def _fuzz_post(self, depth):
        header_params = self._ep_method_def.get(defs.DOC_PARAMS)
        headers = self._fuzz_params(depth + 1, header_params)
        
        request_body = self._ep_method_def.get(defs.DOC_REQUEST)
        body_def = request_body.get(defs.DOC_CONTENT).get(defs.HEADER_JSON)
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
        body = self._fuzz_params(depth + 1, body_param_lst)

        body.update(headers)
        return body

    def _fuzz_params(self, depth, params):
        raise NotImplementedError

    def _fuzz_one(self, depth):
        if depth > self._fuzzing_depth_limit:
            raise ExceedDepthLimit

        self._logger.debug(f"Fuzzing for endpoint {self._endpoint}"
            f" at depth {depth}")

        # get parameters
        if self._method.upper() == defs.METHOD_GET:
            # parameters are defined in the "parameters" section
            params = self._fuzz_get(depth)
            code, response = self._conn.send_and_recv(
                self._endpoint, {}, params)
        elif self._method.upper() == defs.METHOD_POST:
            # parameters are defined in both the "parameters" and "requestBody"
            params = self._fuzz_post(depth)
            code, response = self._conn.send_and_recv(
                self._endpoint, {}, params)
        else:
            raise Exception("Unsupported method for fuzzing:", self._method)

        return FuzzResult(self._method, self._endpoint, code, response, params)

    def run(self):
        try:
            return self._fuzz_one(1)
        except Exception as e:
            self._logger.debug(f"Exception: {e}")
            return None

class FuzzerThread(BasicFuzzer):
    def __init__(self, hostname, base_path, 
        endpoint, method, ep_method_def, value_dict, _, depth_limit):
        super().__init__(
            hostname, base_path,
            endpoint, method, ep_method_def, value_dict)
        self._fuzzing_depth_limit = depth_limit

    def _try_producer(self, depth, producer_gen):
        try:
            producer = next(producer_gen)
            
            if not isinstance(producer, Producer):
                self._logger.debug(f"Trying the parameter value {producer}")
                return producer

            self._logger.debug(f"Trying the producer {producer.endpoint}"
                f" with path {producer.path}")
            producer_thread = FuzzerThread(
                self._hostname, self._base_path, 
                producer.endpoint, producer.method, producer.ep_method_def,
                self._fuzzing_depth_limit - 1)
            producer_thread.start()
            code, result = producer_thread.join()
            if code not in defs.SUCCESS_CODES:
                raise Exception("Unsuccessful fuzzing")

            for field in producer.path:
                if field == defs.INDEX_ANY:
                    # TODO: do we want to backtrack here?
                    result = random.choice(result)
                else:
                    # instead of using "get", we want the exception to be thrown
                    # and caught by the recursive case below
                    result = result[field]

            self._logger.info(f"Selected producer {producer.endpoint}"
                f" with path {producer.path}")
            return result
        except (StopIteration, ExceedDepthLimit):
            return None
        except Exception as e:
            self._logger.debug(f"Previous producer failed with exception {e}."
                " Trying another one...")
            return self._try_producer(depth, producer_gen)

    def _fuzz_param_from_dependency(self, depth, param_name, dependencies):
        producers = list(dependencies.get(param_name))
        random.shuffle(producers)
        producer_gen = (x for x in producers)
        param_val = self._try_producer(depth, producer_gen)
        return param_val

    def _fuzz_params(self, depth, params):
        param_dict = {}
        for param_obj in params:
            required = param_obj.get(defs.DOC_REQUIRED)

            # skip optional arguments for now
            if not required:
                continue

            param_name = param_obj.get(defs.DOC_NAME)
            param_schema = param_obj.get(defs.DOC_SCHEMA)
            if param_schema: # for parameters
                param_type = param_schema.get(defs.DOC_TYPE)
            else: # for requestBody
                param_type = param_obj.get(defs.DOC_TYPE)

            self._logger.debug(f"Filling for parameter {param_name}")
            param_val = None
            if param_name in self._real_dependencies:
                self._logger.debug(f"Real dependency found.")
                param_val = self._fuzz_param_from_dependency(
                    depth, param_name, self._real_dependencies)
            
            if not param_val and param_name in self._inferred_dependencies:
                self._logger.debug(f"Inferred dependency found.")
                param_val = self._fuzz_param_from_dependency(
                    depth, param_name, self._inferred_dependencies)

            if not param_val:
                self._logger.debug(f"No dependency found. Trying random values.")
                param_val = self._random_from_type(param_name, param_type)
            
            param_dict[param_name] = param_val

        self._logger.debug("Found all the parameter values.")
        return param_dict

class SaturationThread(BasicFuzzer):
    def __init__(self, hostname, base_path,
        endpoint, method, ep_method_def, value_dict, analyzer, depth_limit):
        super().__init__(
            hostname, base_path,
            endpoint, method, ep_method_def, value_dict)
        self._fuzzing_depth_limit = depth_limit
        self._analyzer = analyzer

    # get params from bank
    def _fuzz_params(self, _, params):
        param_dict = {}
        for param_obj in params:
            required = param_obj.get(defs.DOC_REQUIRED)

            # skip optional arguments for now
            if not required:
                continue

            param_name = param_obj.get(defs.DOC_NAME)
            param_schema = param_obj.get(defs.DOC_SCHEMA)
            if param_schema: # for parameters
                param_type = param_schema.get(defs.DOC_TYPE)
            else: # for requestBody
                param_type = param_obj.get(defs.DOC_TYPE)

            self._logger.debug(f"Filling for parameter {param_name}")
            param = RequestParameter(
                self._method, param_name, self._endpoint, None)
            if self._analyzer.dsu.find(param):
                param_value_bank = self._analyzer.dsu.get_value_bank(param)
                param_val = random.choice(param_value_bank)
            else:
                self._logger.debug(f"No dependency found for {param_name}. Trying random values.")
                param_val = self._random_from_type(param_name, param_type)

            param_dict[param_name] = param_val

        return param_dict

class Fuzzer:
    def __init__(self, openapi_doc, analyzer, val_dict,
        depth_limit=3, path_to_defs="#/components/schemas", skip_fields=[]):
        self._logger = logging.getLogger(__name__)
        # parse the spec into dict
        self._doc = openapi_doc
        self._paths = self._doc.get(defs.DOC_PATHS)

        # resolve dependencies from the spec
        resolver = DependencyResolver()
        dependencies = resolver.get_dependencies_from_doc(self._paths)
        self._inferred_dependencies = dependencies

        self._analyzer = analyzer
        groups = analyzer.analysis_result()
        self._real_dependencies = resolver.get_dependencies_from_groups(
            self._paths, groups)

        # value patterns injected by users
        self._value_dict = val_dict
        self._depth_limit = depth_limit

        # start a new connection for fuzzing
        servers = self._doc.get("servers")
        server = servers[0].get("url")
        server_result = urlparse(server)
        self._hostname = server_result.netloc
        self._base_path = server_result.path
        self._logger.debug(f"Get hostname: {self._hostname}"
            f" and basePath: {self._base_path}")

        self._path_to_defs = path_to_defs
        self._skip_fields = skip_fields

    def _add_new_result(self, result: FuzzResult):
        if result.has_error:
            return

        for name, val in result.request_params.items():
            request = RequestParameter(
                result.method, name, result.endpoint, val)
            self._analyzer.insert(request)

        response = ResponseParameter(
            result.method, "", result.endpoint, [], result.response_body)
        for r in response.flatten(self._path_to_defs, self._skip_fields):
            self._analyzer.insert(r)

    def _run_all(self, fuzz_type, endpoints, iterations, timeout):
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
                        self._logger.debug(f"Submit job for {method} {ep}")
                        t = fuzz_type(
                            self._hostname, self._base_path, 
                            ep, method, ep_method_def,
                            self._value_dict, self._analyzer, self._depth_limit)
                        futures.append(executor.submit(t.run))
                for future in as_completed(futures):
                    try:
                        self._logger.debug(f"Get result")
                        results.append(future.result(timeout=timeout))
                    except TimeoutError:
                        print("We lacked patience and got a TimeoutError")
                    except Exception:
                        print("we get other exceptions")

            for fuzz_result in results:
                if fuzz_result:
                    self._add_new_result(fuzz_result)

            self.to_graph(endpoints, f"dependencies_{i}")
            
    def fuzz_all(self, endpoints, iterations, timeout):
        self._run_all(FuzzerThread, endpoints, iterations, timeout)
    
    def saturate_all(self, endpoints, iterations, timeout):
        self._run_all(SaturationThread, endpoints, iterations, timeout)

    def to_graph(self, endpoints, filename):
        dot = self._analyzer.to_graph(
            endpoints=endpoints, 
            allow_only_input=False,
            filename=filename,
        )

        render_filename = os.path.join("output/", filename)
        dot.render(render_filename, view=False)