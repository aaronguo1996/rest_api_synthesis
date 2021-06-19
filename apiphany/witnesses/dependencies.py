from typing import List
import re

from openapi import defs
from witnesses.utils import split_by

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

    def __eq__(self, other):
        return (
            self.values == other.values and
            self.combine == other.combine
        )

    def __hash__(self):
        return hash((tuple(self.values), self.combine))

class DependencyResolver:
    def __init__(self, doc):
        # dependencies are a mapping from parameter names to list of producers
        self._dependencies = {}
        self._doc = doc

    # create dependency mapping from union-find results
    def get_dependencies_from_groups(self, groups):
        self._dependencies = {}
        paths = self._doc
        for group in groups:
            params, resps = split_by(
                lambda x: x.array_level is None, group)
            
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
                    ep_method_def = None
                else:
                    ep_method_def = ep_def.get(resp.method.upper())
                
                producer = EndpointProducer(
                    endpoint, resp.method.upper(), ep_method_def, resp.path)
                producers.add(producer)

            if producers:
                for param in params:
                    param_name = param.arg_name
                    self._dependencies[param_name] = producers

        return self._dependencies

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
                        method = producer.get(defs.ANN_METHOD)
                        path = producer.get(defs.ANN_PATH).split('/')
                        # get the definition from doc
                        paths = self._doc
                        ep_def = paths.get(ep)
                        ep_method_def = ep_def.get(method.upper())
                        # create the producer for this
                        producer = EndpointProducer(
                            ep, method.upper(), ep_method_def, path
                        )
                        valid_producers.add(producer)

        return valid_producers

    def get_dependencies_from_annotations(self, annotations):
        self._dependencies = {}

        paths = self._doc
        for ep, path_def in paths.items():
            for _, method_def in path_def.items():
                parameters = method_def.parameters
                for param in parameters:
                    param_name = param.arg_name
                    producers = self._generate_annotation_for(
                        annotations, 
                        ep, param_name
                    )
                    if producers:
                        self._dependencies[(ep, param_name)] = producers

        return self._dependencies