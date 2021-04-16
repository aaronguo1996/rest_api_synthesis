import re
import logging

from schemas.schema_type import SchemaType
from analyzer.entry import ErrorResponse, ResponseParameter, RequestParameter
from analyzer.utils import get_representative
from openapi import defs
from synthesizer.utils import make_entry_name

class DSU:
    # TODO: record types for each param here
    def __init__(self):
        self._parents = {}
        self._sizes = {}
        self._nexts = {}
        self._values = {}
        self._types = {}
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
            try:
                self._values[x] = set([x.value])
            except:
                self._values[x] = set([str(x.value)])

        if y not in self._parents:
            self._parents[y] = y
            self._sizes[y] = 1
            self._nexts[y] = y
            try:
                self._values[y] = set([y.value])
            except:
                self._values[y] = set([str(y.value)])

        # hard code rules for Slack, FIXME: check the type
        if (("name" in y.arg_name and isinstance(y, ResponseParameter) and y.type and "objs_message" in y.type.name) or 
            ("name" in x.arg_name and isinstance(x, ResponseParameter) and x.type and "objs_message" in x.type.name)):
            return

        # hard code rules for Stripe
        # if ((isinstance(x, ResponseParameter) and x.path == ['data', '[?]', 'data', 'object', 'id']) or
        #     (isinstance(y, ResponseParameter) and y.path == ['data', '[?]', 'data', 'object', 'id'])):
        #     return

        xr, yr = self.find(x), self.find(y)
        # if xr != yr:
        #     print("union", xr, yr)

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
        # print("[get_value_bank] root for", x, "is", self.find(x))
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
        self.type_fields = {}
        self.type_partitions = {}
        self.type_aliases = {}
        # temporary field
        self._checked_fields = {}

    def _add_type_fields(self, r):
        if r.type is None:
            return

        typ = r.type.get_oldest_parent()
        # if typ.name == "defs_user_id":
        #     print(typ.name)
        #     print(typ.schema)
        #     print(typ.is_object)
        if not typ.is_object:
            # print(typ.name, "is not an object")
            return

        typ_name = typ.name
        if typ_name not in self.type_fields:
            self.type_fields[typ_name] = {}
        
        if r.func_name not in self.type_fields[typ_name]:
            self.type_fields[typ_name][r.func_name] = set()

        # FIXME: this is specific to Slack API
        path = [p for p in r.path[1:] if p is not defs.INDEX_ANY]
        if path:
            self.type_fields[typ_name][r.func_name].add('.'.join(path))

    def _partition_type(self):
        for t, fun_map in self.type_fields.items():
            for typ_fields in fun_map.values():
                if t not in self.type_partitions:
                    self.type_partitions[t] = [list(typ_fields)]
                    continue

                curr_partitions = self.type_partitions[t]
                new_partitions = []
                all_diffs = []
                for part in curr_partitions:
                    overlap = [f for f in typ_fields if f in part]
                    diff = [f for f in typ_fields if f not in part]
                    if all_diffs:
                        all_diffs = [d for d in all_diffs if d in diff]
                    else:
                        all_diffs = diff

                    if not overlap or not diff: # if there is no overlapping
                        if len(part) == 0:
                            print("empty part")
                        new_partitions.append(part)
                    else: # they have some overlap but also some differences, divide this partition into two
                        if len(overlap) == 0:
                            print("empty overlap")
                        new_partitions.append(overlap)
                        split = [f for f in part if f not in typ_fields]
                        if split: # sometimes this is empty because typ_fields include all the elements in split but has more
                            new_partitions.append(split)
                            print("splitting", part, "into", split)

                if all_diffs:
                    new_partitions.append(all_diffs)

                self.type_partitions[t] = new_partitions


    def analyze(self, paths, entries, skip_fields, blacklist, path_to_defs="#/components/schemas", prefilter=False):
        '''
            Match the value of each request argument or response parameter
            in a log entry and union the common ones
        '''
        params = []
        for entry in entries:
            # do not add error responses to DSU
            if isinstance(entry.response, ErrorResponse):
                continue
            
            if entry.endpoint == "/chat.postMessage":
                print(entry.method)
                print([(p.arg_name, p.value) for p in entry.parameters])
                print(entry.response.value)

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

            responses, aliases = entry.response.flatten(
                path_to_defs, skip_fields
            )
            self.type_aliases.update(aliases)

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

                if p.arg_name in entry_requests:
                    param = entry_requests.get(p.arg_name)
                    typ = param.get(defs.DOC_TYPE)
                    correct_value(p, typ)

                params.append(p)
                
            for r in responses:
                self._add_type_fields(r)
                params.append(r)

        if prefilter:
            print(self.type_fields)
            self._partition_type()
            print(self.type_partitions)
        for p in params:
            self.insert(p)

    def insert(self, param):
        if param.value is None:
            return

        # skip empty values, integers and booleans for merge, 
        # but add them as separate nodes, they are meaningless
        if not param.value or isinstance(param.value, int) or isinstance(param.value, bool):
            # print(param.func_name, param.arg_name, param.value)
            param.value = str(param.value)
            self.dsu.union(param, param)
            return

        value = str(param.value)
        if value not in self.value_to_param:
            self.value_to_param[value] = param

        root = self.value_to_param[value]
        
        self.dsu.union(root, param)

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

            # for debug
            if rep == "source.id" or rep == "payment_source.id":
                group_params = []
                for param in group:
                    if isinstance(param, ResponseParameter):
                        group_params.append((param.func_name, param.method, param.path, param.value, param.type))
                    else:
                        group_params.append((param.func_name, param.method, ["REQUEST", param.arg_name], param.value, param.type))

                sorted(group_params)
                for p in group_params:
                    print(p)

                print("==================")

            dot.node(rep, label=rep, shape="oval")

            for param in group:
                trans = make_entry_name(param.func_name, param.method)
                dot.node(trans, label=trans, shape='rectangle')
                if isinstance(param, ResponseParameter):
                    # add an edge between the method and its return type
                    if '[' not in rep and not re.search("image_.*", rep):
                        if param.type:
                            if "unknown_" in param.type.name:
                                continue

                            p = param.type.get_oldest_parent()
                            # if trans == "/v1/customers/{customer}_GET":
                            #     print(trans, "connected with", rep, "by parameter", param.arg_name, param.value)

                            if p.name == param.type.name:
                                edges.add((trans, rep))
                            else:
                                projection = f"projection ({param.type.name})"
                                dot.node(projection, label=projection, shape='rectangle')
                                edges.add((p.name, projection))
                                edges.add((projection, rep))
                                edges.add((trans, p.name))
                        else:
                            edges.add((trans, rep))
                else:
                    if trans == "/v1/customers/{customer}_GET":
                        print(rep, "connected with", trans, "by parameter", param.arg_name, param.value)
                    # add an edge between parameter name and the method
                    if '[' not in rep and not re.search("image_.*", rep):
                        edges.add((rep, trans))

        for v1, v2 in edges:
            # print(v1, v2)
            f1 = '_'.join(v1.split('_')[:-1])
            f2 = '_'.join(v2.split('_')[:-1])
            if ((v1[0] == '/' and f1 not in endpoints) or 
                (v2[0] == '/' and f2 not in endpoints)):
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
            if (isinstance(p, ResponseParameter) and
                p.func_name == param.func_name and
                p.method.upper() == param.method.upper() and
                param.path == p.path[:len(param.path)]):

                return p
        return None

    def get_values_by_type(self, typ):
        params = self.dsu._parents.keys()
        values = []
        for param in params:
            if param.type and param.type.name == typ.name:
                group = self.dsu.get_group(param)
                for p in group:
                    if p.value is not None:
                        values.append(p.value)
                
                # break

        return values

    def find_same_type(self, param):
        typ_name = self.type_aliases.get(param.type.name)

        if typ_name is not None:
            param.type = SchemaType(typ_name, None)
            return param
        else:
            typ_name = param.type.name

        params = self.dsu._parents.keys()
        for p in params:
            if (isinstance(p, ResponseParameter) and
                p.type and p.type.name == typ_name):
                group = self.dsu.get_group(p)
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
                if descendant.type:
                    param_type = descendant.type.get_oldest_parent()
                    # get the fields
                    func_fields = self.type_fields.get(param_type.name, {})
                    fields = func_fields.get(param.func_name)
                    if fields is None: # we add all partitions that we can find
                        parts = self.type_partitions.get(param_type.name)
                        if parts is None:
                            # print("no partition available for type when fields not available", param_type)
                            param.type = param_type
                        else:
                            param.type = [
                                SchemaType(f"{param_type.name}_{i}", None)
                                for i in range(len(parts))
                            ]
                    else:
                        # get all the partitions that cover the fields
                        partitions = self.type_partitions.get(param_type.name)
                        if partitions is None:
                            # print("no partition available for type when fields available", param_type)
                            param.type = param_type
                        else:
                            indices = []
                            for i, part in enumerate(partitions):
                                if part[0] in fields:
                                    indices.append(i)

                            param.type = [
                                SchemaType(f"{param_type.name}_{i}", None)
                                for i in indices
                            ]
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

    def reset_context(self):
        self._checked_fields = {}

    def add_projection_field(self, obj_typ, inter_typ, fun, field):
        if re.search('^/.*_response$', obj_typ):
            return

        prefix = []
        if (obj_typ, fun) in self._checked_fields:
            obj_typ, prefix = self._checked_fields[(obj_typ, fun)]
        
        self._checked_fields[(inter_typ, fun)] = obj_typ, (prefix + [field])

    def check_type_fields(self, typ, fun, field):
        if re.search('^/.*_response$', typ):
            return True

        func_fields = self.type_fields.get(typ)
        prefix = []
        if func_fields is None:
            # check whether it is an intermediate type
            key = (typ, fun)
            try:
                obj_typ, prefix = self._checked_fields.get(key)
                func_fields = self.type_fields.get(obj_typ)
            except Exception:
                print(key)
                raise Exception

        fields = func_fields.get(fun)
        if fields is None:
            return True

        found = False
        for f in fields:
            fs = f.split('.')
            fixed_field = prefix + [field]
            if fixed_field == fs[:len(fixed_field)]:
                found = True
                break

        return found
