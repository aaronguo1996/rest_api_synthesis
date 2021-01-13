from fuzzer.error import EndpointNotFoundError
from fuzzer.request import Connection
from fuzzer.dependencies import DependencyResolver
from openapi.preprocess import PreProcessor
from openapi import defs

from prance import ResolvingParser, ValidationError
from xeger import Xeger
import logging
import random
import json

class Fuzzer:
    def __init__(self, openapi_doc):
        # parse the spec into dict
        self._read_doc(openapi_doc)
        self._paths = self._doc.get("paths")
        # resolve dependencies from the spec
        resolver = DependencyResolver()
        dependencies = resolver.get_dependencies_from_doc(self._paths)
        # these may not be the real dependencies
        self._inferred_dependencies = dependencies
        self._real_dependencies = {}
        self._value_dict = {}
        # start a new connection for fuzzing
        servers = self._doc.get("servers")
        hostname = servers[0].get("url")
        self._conn = Connection(hostname)
        # create a logger for this module
        self._logger = logging.getLogger(__name__)
        # fake random for debugging
        random.seed(1)

    def _read_doc(self, doc_path):
        try:
            parser = ResolvingParser(doc_path)
            # spec with all the references resolved
            self._doc = parser.specification
        except ValidationError: # allow other exceptions to be thrown
            name_segs = doc_path.split('.')
            file_name = '.'.join(name_segs[:-1]) + "_preprocess.json"
            preprocessor = PreProcessor(doc_path)
            preprocessor.preprocess(file_name)
            self._read_doc(file_name)

    def _random_from_type(self, param_name, param_type):
        x = Xeger(limit=20)
        defined_regex = None
        if param_name in self._value_dict:
            defined_regex = self._value_dict.get(param_name)

        if param_type == defs.TYPE_STRING:
            regex = defined_regex or r"^[a-zA-Z0-9]{10,}$"
            yield x.xeger(regex)
        elif param_type == defs.TYPE_ARRAY:
            yield []
        elif param_type == defs.TYPE_INT:
            int_range = defined_regex or range(0,100)
            yield random.choice(int_range)
        elif param_type == defs.TYPE_NUM:
            float_range = defined_regex or range(0, 1)
            yield random.uniform(*float_range)
        elif param_type == defs.TYPE_BOOL:
            yield random.choice([True, False])
        elif param_type == defs.TYPE_OBJECT:
            yield {}
        else:
            raise Exception("Cannot generate random values for type", param_type)

    def _try_producer(self, producer_gen):
        try:
            producer = next(producer_gen)
            result = self.fuzz_one(producer.endpoint, producer.method)
            for field in producer.path:
                if field == defs.INDEX_ANY:
                    # TODO: do we want to backtrack here?
                    result = random.choice(result)
                else:
                    # instead of using "get", we want the exception to be thrown
                    # and caught by the recursive case below
                    result = result[field]
            return result
        except StopIteration:
            return None
        except Exception:
            self._try_producer(producer_gen)

    def _fuzz_params(self, params):
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

            if param_name in self._real_dependencies:
                producers = self._real_dependencies.get(param_name)
                random.shuffle(producers)
                producer_gen = (x for x in producers)
            elif param_name in self._inferred_dependencies:
                producers = self._inferred_dependencies.get(param_name)
                random.shuffle(producers)
                producer_gen = (x for x in producers)
            else:
                producer_gen = self._random_from_type(param_name, param_type)
            
            param_val = self._try_producer(producer_gen)
            if not param_val:
                param_val = self._random_from_type(param_name, param_type)
            param_dict[param_name] = param_val

        return param_dict

    def _fuzz_get(self, endpoint, method, ep_def):
        assert method == defs.METHOD_GET

        params = ep_def.get(defs.DOC_PARAMS)
        return self._fuzz_params(params)

    def _fuzz_post(self, endpoint, method, ep_def):
        assert method == defs.METHOD_POST

        header_params = ep_def.get(defs.DOC_PARAMS)
        headers = self._fuzz_params(header_params)
        request_body = ep_def.get(defs.DOC_REQUEST)
        body_params = request_body.get(defs.DOC_CONTENT).get(defs.HEADER_JSON)
        body = self._fuzz_params(body_params)

        return headers, body

    def fuzz_one(self, endpoint, method):
        ep_def = self._paths.get(endpoint)
        if not ep_def:
            raise EndpointNotFoundError(endpoint)
        
        ep_method_def = ep_def.get(method)
        if not ep_method_def:
            raise EndpointNotFoundError(endpoint, method)

        # get parameters
        if method == defs.METHOD_GET:
            # parameters are defined in the "parameters" section
            params = self._fuzz_get(endpoint, method, ep_method_def)
            self._conn.send_urlencoded(method, endpoint, {}, params)
        elif method == defs.METHOD_POST:
            # parameters are defined in both the "parameters" and "requestBody"
            headers, params = self._fuzz_post(endpoint, method, ep_method_def)
            self._conn.send_body(method, endpoint, headers, params)
        else:
            raise Exception("Unsupported method for fuzzing:", method)

        code, response = self._conn.recv()
        if code in defs.SUCCESS_CODES:
            return code, json.loads(response)
        else:
            return code, {"error": response}

    def fuzz_one_util(self, endpoint, method, limit=3):
        code, resp = self.fuzz_one(endpoint, method)
        
        trials = limit
        while trials >= 0 and code not in defs.SUCCESS_CODES:
            code, resp = self.fuzz_one(endpoint, method)
            trials -= 1

        return code, resp

    def fuzz_all(self, endpoint, method):
        pass