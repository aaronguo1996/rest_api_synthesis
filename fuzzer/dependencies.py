from typing import List
import re

from openapi import defs
from fuzzer import error
from fuzzer.utils import split_by
from analyzer.entry import RequestParameter

class EndpointProducer:
    def __init__(self, ep: str, method: str, ep_method_def, path: List[str]):
        self.endpoint = ep
        self.method = method
        self.ep_method_def = ep_method_def
        self.path = path
    
    def __str__(self):
        return ' '.join([
            self.method,
            self.endpoint,
            str(self.path),
        ])

    def __repr__(self):
        return self.__str__()

    def __eq__(self, other):
        return (
            self.endpoint == other.endpoint and
            self.method == other.method and
            self.path == other.path
        )

    def __hash__(self):
        return hash((self.endpoint, self.method, tuple(self.path)))

class EnumProducer:
    def __init__(self, values, combine):
        self.values = values
        self.combine = combine

    def __str__(self):
        return f"enum: {self.values}"

    def __repr__(self):
        return self.__str__()

    def __eq__(self, other):
        return (
            self.values == other.values and
            self.combine == other.combine
        )

    def __hash__(self):
        return hash((tuple(self.values), self.combine))

class DependencyResolver:
    def __init__(self):
        # dependencies are a mapping from parameter names to list of producers
        self._dependencies = {}
        self._producers = set()

    # create dependency mapping from union-find results
    def get_dependencies_from_groups(self, paths, groups):
        self._dependencies = {}
        for group in groups:
            params, resps = split_by(
                lambda x: isinstance(x, RequestParameter), group)
            
            producers = set()
            for resp in resps:
                for i in range(len(resp.path)):
                    if re.search(r"\[[0-9]+\]", resp.path[i]):
                        resp.path[i] = defs.INDEX_ANY

                endpoint = resp.func_name
                if "/api" in endpoint:
                    endpoint = endpoint[4:]
                
                ep_def = paths.get(endpoint)
                if not ep_def:
                    # print(f"We get an undocumented method {endpoint}")
                    # TODO: construct a definition with the information we know
                    ep_method_def = None
                else:
                    ep_method_def = ep_def.get(resp.method)
                
                producer = EndpointProducer(
                    endpoint, resp.method, ep_method_def, resp.path)
                producers.add(producer)

            if producers:
                for param in params:
                    param_name = param.arg_name
                    self._dependencies[param_name] = producers

        return self._dependencies

    def _create_producers_with_same_output(self, resp_arg):
        producers = set()
        for producer in self._producers:
            if resp_arg == producer.path[-1]:
                producers.add(producer)

        return producers

    def _get_name_mapping(self, groups, param_name):
        for group in groups:
            params, resps = split_by(
                lambda x: isinstance(x, RequestParameter), group)
            
            param_names = [rp.arg_name for rp in params]
            if param_name in param_names:
                producers = self._create_producers_with_same_output(resps)
                curr_producers = self._dependencies.get(param_name, set())
                self._dependencies[param_name] = curr_producers.union(producers)

    def _generate_annotation_for(self, annotations, endpoint, param_name):
        valid_producers = set()
        for ann in annotations:
            if (ann.get(defs.ANN_CONSUMER) == param_name and
                (ann.get(defs.ANN_ENDPOINT) is None or
                ann.get(defs.ANN_ENDPOINT) == endpoint)):

                ann_producers = ann.get(defs.ANN_PRODUCER)
                for producer in ann_producers:
                    if defs.ANN_ENUM in producer:
                        values = producer.get(defs.ANN_ENUM)
                        combine = producer.get(defs.ANN_COMBINE)
                        valid_producers.add(EnumProducer(values, combine))
                    else:
                        ep = producer.get(defs.ANN_ENDPOINT)
                        path = producer.get(defs.ANN_PATH)

                        for p in self._producers:
                            if p.endpoint == ep and p.path == path.split('/'):
                                valid_producers.add(p)

        return valid_producers

    def get_dependencies_from_annotations(self, paths, annotations):
        self._dependencies = {}
        self._flatten_responses(paths)

        for ep, path_def in paths.items():
            for _, method_def in path_def.items():
                parameters = method_def.get(defs.DOC_PARAMS, [])
                for param in parameters:
                    param_name = param.get(defs.DOC_NAME)
                    producers = self._generate_annotation_for(
                        annotations, 
                        ep, param_name
                    )
                    if producers:
                        self._dependencies[(ep, param_name)] = producers

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
                        producers = self._generate_annotation_for(
                            annotations, 
                            ep, param_name
                        )
                        if producers:
                            self._dependencies[(ep, param_name)] = producers

        return self._dependencies

    def get_dependencies_from_doc(self, paths, groups):
        self._dependencies = {}
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
                        self._get_name_mapping(groups, param_name)

        return self._dependencies
        
    def _get_dependencies_for_param(self, param_name):
        if param_name in self._dependencies:
            return

        valid_producers = set()
        for producer in self._producers:
            # the param name matches the end name of a json field or
            # the param name matches an object id
            end_field = producer.path[-1]
            if (end_field == param_name or
                (param_name in producer.path and defs.DOC_ID == end_field)):
                valid_producers.add(producer)

            param_array = param_name + "s"
            if len(producer.path) > 2:
                last_two_field = producer.path[-2]
                last_three_field = producer.path[-3]
                if (end_field == defs.DOC_ID and 
                    last_two_field == defs.INDEX_ANY and
                    last_three_field == param_array):
                    valid_producers.add(producer)
            
        if valid_producers:
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

                    self._flatten_response(path, method, method_def, [], schema)

    def _flatten_response(self, endpoint, method, ep_method_def, 
        path: List[str], schema):
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
                self._flatten_response(
                    endpoint, method, ep_method_def, curr_path, prop_val)

        elif schema_items:
            if schema_type != defs.TYPE_ARRAY:
                raise error.InvalidSwaggerDoc

            curr_path = path + [defs.INDEX_ANY]
            self._flatten_response(
                endpoint, method, ep_method_def, curr_path, schema_items)

        elif schema_choices:
            for sch in schema_choices:
                self._flatten_response(
                    endpoint, method, ep_method_def, path, sch)

        elif schema_type:
            # base case: create a new Producer object
            producer = EndpointProducer(endpoint, method, ep_method_def, path)
            self._producers.add(producer)

        else:
            raise Exception("Unexcepted case:", schema)