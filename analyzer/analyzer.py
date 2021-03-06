import re
import logging

from schemas.schema_type import SchemaType
from analyzer.entry import ErrorResponse, ResponseParameter, RequestParameter
from analyzer.utils import get_representative
from openapi import defs

class DSU:
    def __init__(self):
        self._parents = {}
        self._sizes = {}
        self._nexts = {}
        self._values = {}
        self._logger = logging.getLogger(__name__)

    def find(self, x):
        if x not in self._parents:
            return None

        if self._parents[x] != x:
            self._parents[x] = self.find(self._parents[x])
            
        return self._parents[x]

    def union(self, x, y):
        if x not in self._parents:
            self._parents[x] = x
            self._sizes[x] = 1
            self._nexts[x] = x
            self._values[x] = set([x.value])

        if y not in self._parents:
            self._parents[y] = y
            self._sizes[y] = 1
            self._nexts[y] = y
            self._values[y] = set([y.value])

        xr, yr = self.find(x), self.find(y)
        group = self.get_group(xr)
        rep1, _ = get_representative(group)
        group = self.get_group(yr)
        rep2, _ = get_representative(group)

        if ((rep1 == "defs_group_id" and y.arg_name == "name") or 
            (rep2 == "defs_group_id" and x.arg_name == "name")):
            return

        if self._sizes[xr] < self._sizes[yr]:
            self._parents[yr] = xr
            # swap the next pointer of xr and yr
            self._nexts[yr], self._nexts[xr] = self._nexts[xr], self._nexts[yr]
            self._sizes[xr] += self._sizes[yr]
            self._values[xr] = self._values[xr].union(self._values[yr])
        elif self._sizes[yr] < self._sizes[xr] or xr != yr: # if they have the same size but are different nodes
            self._parents[xr] = yr
            # swap the next point of xr and yr
            self._nexts[xr], self._nexts[yr] = self._nexts[yr], self._nexts[xr]
            self._sizes[yr] += self._sizes[xr]
            self._values[yr] = self._values[yr].union(self._values[xr])

    def groups(self):
        groups = []
        for x in self._parents:
            if self._parents[x] == x:
                groups.append(self.get_group(x))

        return groups

    def get_value_bank(self, x):
        return self._values.get(self.find(x), set())

    def get_group(self, x):
        '''
            get all the elements in the same group as @x@
        '''
        if x not in self._parents:
            return []

        result = [x]
        cur = x
        nxt = self._nexts[x]
        while x != nxt:
            result.append(nxt)
            cur, nxt = nxt, self._nexts[cur]

        return set(result)

class LogAnalyzer:
    def __init__(self):
        self.value_to_param = {}
        self.dsu = DSU()

    def analyze(self, paths, entries, skip_fields, path_to_defs = "#/components/schemas"):
        '''
            Match the value of each request argument or response parameter
            in a log entry and union the common ones
        '''
        blacklist = [
            '/apps.actions.v2.list'
        ]
        for entry in entries:
            # do not add error responses to DSU
            if isinstance(entry.response, ErrorResponse):
                continue
            
            # match docs to correct integers and booleans
            entry_def = paths.get(entry.endpoint)
            if entry.endpoint in blacklist:
                continue

            if entry_def:
                entry_def = entry_def.get(entry.method.lower())

            entry_requests = {}
            entry_params = []
            if entry_def:
                entry_params = entry_def.get(defs.DOC_PARAMS, [])
                entry_requests = entry_def.get(defs.DOC_REQUEST, {})
                if entry_requests:
                    entry_requests = entry_requests.get(defs.DOC_CONTENT, {})
                    if defs.HEADER_FORM in entry_requests:
                        entry_requests = entry_requests.get(defs.HEADER_FORM)
                    else:
                        entry_requests = entry_requests.get(defs.HEADER_JSON)
                    entry_requests = entry_requests \
                        .get(defs.DOC_SCHEMA) \
                        .get(defs.DOC_PROPERTIES)

            responses = entry.response.flatten(path_to_defs, skip_fields)

            def correct_value(p, typ):
                if typ == "integer":
                    p.value = int(p.value)
                elif typ == "boolean":
                    p.value = bool(p.value)

            for p in entry.parameters:
                for param in entry_params:
                    if param.get(defs.DOC_NAME) == p.arg_name:
                        typ = param.get(defs.DOC_SCHEMA).get(defs.DOC_TYPE)
                        correct_value(p, typ)
                    
                    break
                
                if p.arg_name in entry_requests:
                    param = entry_requests.get(p.arg_name)
                    typ = param.get(defs.DOC_TYPE)
                    correct_value(p, typ)

                self.insert(p)
                
            for r in responses:
                self.insert(r)

    def insert(self, param):
        # if param.arg_name == "fields":
        #     print("fields:", value)

        if param.value is None:
            return

        # skip empty values, integers and booleans for merge, 
        # but add them as separate nodes, they are meaningless
        if not param.value or isinstance(param.value, int) or isinstance(param.value, bool):
            self.dsu.union(param, param)
            return

        value = str(param.value)
        if value not in self.value_to_param:
            self.value_to_param[value] = param

        root = self.value_to_param[value]
        # group = self.dsu.get_group(root)
        # rep, _ = get_representative(group)

        # if rep == "defs_group_id" and (param.arg_name == "topic" or param.arg_name == "value"):
        #     self.dsu.union(param, param)
        #     return

        # print("union", root, root.type, param, param.type, param.value)
        # print(self.dsu.get_group(param))
        self.dsu.union(root, param)
        # print(self.dsu.get_group(param))

    def analysis_result(self):
        return self.dsu.groups()

    def to_graph(self, dot, **kwargs):
        '''
            output the analysis result as a graph in dot format
        '''
        allow_only_input = kwargs.get("allow_only_input", False)
        endpoints = kwargs.get("endpoints")
        
        groups = self.analysis_result()
        edges = set()
        for group in groups:
            # pick representative in each group, the shortest path name
            rep, _ = get_representative(group)
            
            if not rep:
                if not allow_only_input:
                    continue
                # none of the parameters in the group is from a response
                # pick the first as the representative
                # print("not response, choosing", group[0])
                rep = group[0].arg_name
            
            # if not rep or rep == "blocks":
            #     print(f"not rep in group {group}")

            dot.node(rep, label=rep, shape="oval")

            for param in group:
                dot.node(param.func_name, label=param.func_name, shape='rectangle')
                if isinstance(param, ResponseParameter):
                    # add an edge between the method and its return type

                    if '[' not in rep and not re.search("image_.*", rep):
                        if param.type:
                            p = param.type.get_oldest_parent()
                            if p.name == param.type.name:
                                edges.add((param.func_name, rep))
                            else:
                                projection = f"projection ({param.type.name})"
                                dot.node(projection, label=projection, shape='rectangle')
                                edges.add((p.name, projection))
                                edges.add((projection, rep))
                                edges.add((param.func_name, p.name))
                        else:
                            edges.add((param.func_name, rep))
                else:
                    # add an edge between parameter name and the method
                    if '[' not in rep and not re.search("image_.*", rep):
                        edges.add((rep, param.func_name))

        for v1, v2 in edges:
            # print(v1, v2)
            if ((v1[0] == '/' and v1 not in endpoints) or 
                (v2[0] == '/' and v2 not in endpoints)):
                continue

            dot.edge(v1, v2, style="solid")

    def to_json(self):
        groups = self.analysis_result()
        nodes, edges = [], []
        for group in groups:
            # pick representative in each group, the shortest path name
            rep, _ = get_representative(group)
            
            if not rep:
                continue

            nodes.append({
                "key": rep,
                "name": rep,
                "isVisible": True,
                "children": [],
                "parent": None,
                "kind": "field",
            })

            for param in group:
                nodes.append({
                    "key": param.func_name,
                    "name": param.func_name,
                    "isVisible": True,
                    "children": [],
                    "parent": None,
                    "kind": "endpoint",
                })
                if '[' not in rep and not re.search("image_*", rep):
                    if isinstance(param, ResponseParameter):
                        # add an edge between the method and its return type
                        if param.type:
                            p = param.type.get_oldest_parent()
                            if p.name == param.type.name:
                                edges.append({
                                    "source": param.func_name, 
                                    "target": rep,
                                })
                            elif "unknown_obj" not in p.name:
                                # projection = f"projection ({param.type.name})"
                                # nodes.append({
                                #     "key": projection,
                                #     "name": projection,
                                #     "isVisible": True,
                                #     "children": [],
                                #     "parent": None,
                                #     "kind": "endpoint",
                                # })
                                nodes.append({
                                    "key": p.name,
                                    "name": p.name,
                                    "isVisible": True,
                                    "children": [],
                                    "parent": None,
                                    "kind": "field",
                                })
                                edges.append({
                                    "source": p.name,
                                    "target": rep,
                                })
                                # edges.append({
                                #     "source": p.name, 
                                #     "target": projection,
                                # })
                                # edges.append({
                                #     "source": projection, 
                                #     "target": rep,
                                # })
                                # edges.append({
                                #     "source": param.func_name, 
                                #     "target": p.name
                                # })
                        else:
                            edges.append({
                                "source": param.func_name, 
                                "target": rep
                            })
                    else:
                        # add an edge between parameter name and the method
                        edges.append({
                            "source": rep, 
                            "target": param.func_name
                        })

        edges = list({(v["source"], v["target"]):v for v in edges}.values())
        edgeNodes = [v for e in edges for v in (e["source"], e["target"])]
        nodes = list({v["key"]:v for v in nodes if v["key"] in edgeNodes}.values())
        return {
            "nodes": nodes,
            "links": edges,
        }

    def _find_descendant(self, param):
        params = self.dsu._parents.keys()
        for p in params:
            # if isinstance(p, ResponseParameter) and "response_metadata" in p.path:
            #     print("find descendent", p)
            if (isinstance(p, ResponseParameter) and
                p.func_name == param.func_name and
                # p.arg_name == param.arg_name and
                p.method.upper() == param.method.upper() and
                param.path == p.path[:len(param.path)]):

                return p
        return None

    def find_same_type(self, param):
        params = self.dsu._parents.keys()
        for p in params:
            if p.type and p.type.name == param.type.name:
                # print(p)
                group = self.dsu.get_group(p)
                # print(group)
                # print([(p, p.value) for p in group])
                _, rep_type = get_representative(group)
                # TODO: we do not want to find the parent of this type, correct?
                param.type = rep_type
                # print("find type for param", rep, rep_type.name, rep_type.schema)
                break
        
        return param

    def set_type(self, param):
        if param.type and re.search('^/.*_response$', param.type.name):
            return

        if isinstance(param, ResponseParameter):
            descendant = self._find_descendant(param)
            # if param does not belong to any group, create a new type
            if descendant is None or descendant.type is None:
                # print(f"{param} does not belong to any group")
                param.type = SchemaType(str(param), None)
            else:
                # group = self.dsu.get_group(descendant)
                # _, rep_type = get_representative(group)
                if descendant.type:
                    # if param.func_name == "/conversations.members":
                    #     print(descendant.type.name)
                    param.type = descendant.type.get_oldest_parent()
                    # if param.func_name == "/conversations.members":
                    #     print(param.type.name)
                else:
                    # print(f"{param} does not have a descendant type {descendant}")
                    param.type = descendant.type
        elif isinstance(param, RequestParameter):
            group = self.dsu.get_group(param)
            _, rep_type = get_representative(group)
            # if param does not belong to any group
            if group == [] or rep_type is None:
                param.type = SchemaType(str(param), None)
            else:
                param.type = rep_type
        else:
            raise Exception("Unexpected parameter type: "
                "neither ResponseParameter nor RequestParameter")