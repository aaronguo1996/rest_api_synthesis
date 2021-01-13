from typing import List
from openapi import defs
from fuzzer import error

class Producer:
    def __init__(self, ep: str, method: str, path: List[str]):
        self.endpoint = ep
        self.method = method
        self.path = path
    
    def __str__(self):
        return ' '.join([
            self.method,
            self.endpoint,
            str(self.path),
        ])

    def __repr__(self):
        return self.__str__()

class DependencyResolver:
    def __init__(self):
        # dependencies are a mapping from parameter names to list of producers
        self._dependencies = {}
        self._producers = set()

    #TODO: do we want to create dependency mapping from union find?
    def get_dependencies_from_doc(self, paths):
        self._flatten_responses(paths)

        for _, path_def in paths.items():
            for _, method_def in path_def.items():
                parameters = method_def.get(defs.DOC_PARAMS, [])
                for param in parameters:
                    param_name = param.get(defs.DOC_NAME)
                    self._get_dependencies_for_param(param_name)

                request_body = method_def.get(defs.DOC_REQUEST)
                if not request_body:
                    continue

                request_content = request_body.get(defs.DOC_CONTENT)
                if not request_content:
                    raise Exception("Request content is unavailable")

                for _, request_def in request_content.items():
                    request_schema = request_def.get(defs.DOC_SCHEMA)
                    request_properties = request_schema.get(defs.DOC_PROPERTIES)
                    for param_name in request_properties:
                        self._get_dependencies_for_param(param_name)

        return self._dependencies
        
    def _get_dependencies_for_param(self, param_name):
        if param_name in self._dependencies:
            return

        valid_producers = []
        for producer in self._producers:
            # the param name matches the end name of a json field or
            # the param name matches an object id
            end_field = producer.path[-1]
            if (end_field == param_name or
                (param_name in producer.path and defs.DOC_ID == end_field)):
                valid_producers.append(producer)
            
        self._dependencies[param_name] = valid_producers

    def _flatten_responses(self, paths):
        for path, path_def in paths.items():
            for method, method_def in path_def.items():
                responses = method_def.get(defs.DOC_RESPONSES)
                for code, code_def in responses.items():
                    content = code_def.get(defs.DOC_CONTENT)
                    if not content:
                        raise Exception("Cannot find content for response")

                    response = content.get(defs.HEADER_JSON)
                    if not response:
                        raise Exception("Response is not in JSON format, unsupported")

                    schema = response.get(defs.DOC_SCHEMA)
                    if not schema and code != defs.CODE_NO_CONTENT:
                        raise Exception("Response content is undefined")

                    self._flatten_response(path, method, [], schema)

    def _flatten_response(self, endpoint, method, path: List[str], schema):
        properties = schema.get(defs.DOC_PROPERTIES)
        schema_type = schema.get(defs.DOC_TYPE)
        schema_items = schema.get(defs.DOC_ITEMS)

        schema_one_of = schema.get(defs.DOC_ONEOF, [])
        schema_any_of = schema.get(defs.DOC_ANYOF, [])
        schema_all_of = schema.get(defs.DOC_ALLOF, [])
        schema_choices = schema_one_of + schema_any_of + schema_all_of

        if properties:
            for field in properties:
                prop_val = properties[field]
                curr_path = path + [field]
                self._flatten_response(endpoint, method, curr_path, prop_val)

        elif schema_items:
            if schema_type != defs.TYPE_ARRAY:
                raise error.InvalidSwaggerDoc

            curr_path = path + [defs.INDEX_ANY]
            self._flatten_response(endpoint, method, curr_path, schema_items)

        elif schema_choices:
            for sch in schema_choices:
                self._flatten_response(endpoint, method, path, sch)

        elif schema_type:
            # base case: create a new Producer object
            producer = Producer(endpoint, method, path)
            self._producers.add(producer)

        else:
            raise Exception("Unexcepted case:", schema)