import re
import logging

from analyzer.entry import ErrorResponse, Parameter
from analyzer.utils import get_representative, same_type_name
from openapi import defs
from synthesizer.utils import make_entry_name
from schemas import types
import consts
import random

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
            self._values[x] = set([x.value])

        if y not in self._parents:
            self._parents[y] = y
            self._sizes[y] = 1
            self._nexts[y] = y
            self._values[y] = set([y.value])

        # # hard code rules for Slack, FIXME: check the type
        # if (("name" in y.arg_name and y.type and "objs_message" in y.type.name) or 
        #     ("name" in x.arg_name and x.type and "objs_message" in x.type.name)):
        #     return

        xr, yr = self.find(x), self.find(y)

        self._values[xr].add(x.value)
        self._values[yr].add(y.value)

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
    def __init__(self, uncovered_opt):
        self.value_to_param = {}
        self.type_to_param = {}
        self.dsu = DSU()
        self.type_fields = {}
        self.type_partitions = {}
        self.type_aliases = {}
        self.type_values = {}
        self.value_map = {}
        # temporary field
        self._checked_fields = {}
        # privates
        self._uncovered_opt = uncovered_opt

    # FIXME: this function no longer works, please fix me if you want to use it
    def _add_type_fields(self, r):
        if r.type is None:
            return

        typ = r.type.get_oldest_parent()
        if not typ.is_object:
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
                        if split: 
                            # sometimes this is empty because 
                            # typ_fields include all the elements in split but has more
                            new_partitions.append(split)
                            print("splitting", part, "into", split)

                if all_diffs:
                    new_partitions.append(all_diffs)

                self.type_partitions[t] = new_partitions

    def _analyze_params(self, skip_fields, params, path_to_defs):
        def correct_value(p):
            if isinstance(p.type, types.PrimInt):
                p.value = int(p.value)
            elif isinstance(p.type, types.PrimBool):
                p.value = bool(p.value)
            # elif isinstance(p.type, types.PrimNum):
            #     p.value = float(p.value)

        for param in params:
            flatten_params, values = param.flatten(path_to_defs, skip_fields)
            self.insert_value(values)

            for p in flatten_params:
                # print(p.arg_name, p.func_name, p.value)
                correct_value(p)
                self.insert(p)

    def _analyze_response(self, skip_fields, response, path_to_defs):
        responses, values = response.flatten(path_to_defs, skip_fields)
        self.insert_value(values)
        for r in responses:
            self.insert(r)

    def analyze(self, paths, entries, skip_fields, blacklist,
        path_to_defs=consts.REF_PREFIX, prefilter=False):
        '''
            Match the value of each request argument or response parameter
            in a log entry and union the common ones
        '''
        for entry in entries:
            # do not add error responses to DSU
            if (isinstance(entry.response, ErrorResponse) or
                entry.endpoint not in paths or
                entry.endpoint in blacklist or
                not entry.response.value):
                continue

            self._analyze_params(
                skip_fields, 
                entry.parameters, 
                path_to_defs)
            
            self._analyze_response(
                skip_fields, 
                entry.response, 
                path_to_defs)

    def insert_value(self, value_map):
        # add new values to the bank mapping
        for t, v in value_map.items():
            if t not in self.type_values:
                self.type_values[t] = []

            self.type_values[t] += v

    def insert(self, param):
        if param.value is None:
            return

        # skip empty values, we can do nothing with them
        if not param.value:
            return
        
        if isinstance(param.type, types.PrimInt):
            param.value = int(param.value)

        if isinstance(param.type, types.PrimNum):
            param.value = float(param.value)

        # integers and booleans for merge 
        # but add them as separate nodes, they are meaningless
        if ((isinstance(param.value, int) and (param.value <= 1000)) or
            (isinstance(param.value, float) and (param.value <= 1000)) or
            isinstance(param.value, bool)):
            self.dsu.union(param, param)
            return

        # if isinstance(param.value, int):
        #     print(param)

        # merge by value
        if param.value not in self.value_to_param:
            self.value_to_param[param.value] = param

        root = self.value_to_param[param.value]
        self.dsu.union(root, param)

        # merge by type
        param_typ = str(param.type)
        if (param_typ == defs.TYPE_BOOL or
            param_typ == defs.TYPE_INT or
            param_typ == defs.TYPE_STRING or
            param_typ == defs.TYPE_NUM or
            param_typ == defs.TYPE_OBJECT):
            return
            
        if param_typ not in self.type_to_param:
            self.type_to_param[param_typ] = param

        root = self.type_to_param[param_typ]
        # if param_typ == "plan.trial_period_days":
        #     print("param", param, param.value, type(param.type))
        #     print("root", root, root.value, root.type)
        # if param.value == 1621889723 or param.value == 1621890030:
        #     print("*******", param, param.value, param.type, "merging", root.type)

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
            rep = get_representative(group)
            
            if not rep:
                if not allow_only_input:
                    continue
                # none of the parameters in the group is from a response
                # pick the first as the representative
                # print("not response, choosing", group[0])
                rep = group[0].arg_name

            # for debug
            # if rep == "oldest_/chat.scheduledMessages.list_GET_oldest" or rep == "defs_ts":
            #     print("*******", rep)
            #     group_params = []
            #     for param in group:
            #         if param.type is not None:
            #             group_params.append((
            #                 param.func_name, 
            #                 param.method, 
            #                 param.path, 
            #                 param.value, 
            #                 param.type,
            #                 param.type.aliases
            #             ))

            #     for p in group_params:
            #         print(p)

            #     print("==================")

    def to_json(self):
        groups = self.analysis_result()
        nodes, edges = [], []
        for group in groups:
            # pick representative in each group, the shortest path name
            rep = get_representative(group)
            
            if not rep:
                continue

            nodes.append({
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
                    if param.array_level is not None:
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
        descendants = []

        params = self.dsu._parents.keys()
        for p in params:
            if ((param.array_level is None and p.array_level is None) or
                (param.array_level is not None and p.array_level is not None)):
                same_array_level = True
            else:
                same_array_level = False

            if (p.func_name == param.func_name and
                p.method.upper() == param.method.upper() and
                same_array_level and
                param.path == p.path[:len(param.path)]):
                descendants.append(p)

        return descendants

    def get_values_by_type(self, typ):
        return list(self.value_map.get(str(typ), []))

    def sample_value_by_type(self, typ):
        if isinstance(typ, types.ArrayType):
            lst_len = random.choice(range(1, 5))
            # vals = []
            # for _ in range(lst_len):
            #     val = self.sample_value_by_type(typ.item)
            #     vals.append(val)
            vals = [None for _ in range(lst_len)]
            return vals
        else:
            candidates = self.get_values_by_type(typ)
            vals = candidates

            if not vals:
                # print("Not val available for type", typ)
                # x = xeger.Xeger()
                # vals = [x.xeger("^[a-z0-9]{10,}$")]
                vals = ["fuzz_string"]
            
            # print("Sampling by type", typ, "from", vals)
            return random.choice(vals)

    def sample_values_by_type(self, typ):
        res = []
        for _ in range(10):
            res.append(self.sample_value_by_type(typ))

        return res

    def index_values_by_type(self):
        value_map = {}
        params = self.dsu._parents.keys()
        for param in params:
            if param.type:
                typs = param.type.aliases
                typs = typs.union(set([str(param.type)]))
                for typ in typs:
                    if typ not in value_map:
                        value_map[typ] = set()

                    value_map[typ] = value_map[typ].union(
                        self.dsu.get_value_bank(param)
                    )

        for typ, values in self.type_values.items():
            if typ not in value_map:
                value_map[typ] = []
            else:
                value_map[typ] = list(value_map[typ])

            for v in values:
                if v not in value_map[typ]:
                    value_map[typ].append(v)

        self.value_map = value_map

    def find_representative_for_type(self, typ, infer_type=True):
        # assume the input type is not a union type
        if isinstance(typ, types.ArrayType):
            typ.item = self.find_representative_for_type(typ.item, infer_type)
            return typ
            # raise Exception("Array type not supported")

        if not infer_type:
            return typ

        params = self.dsu._parents.keys()
        for param in params:
            if same_type_name(typ, param.type):
                group = self.dsu.get_group(param)
                rep = get_representative(group)

                if rep is not None:
                    typ.name = rep
                    return typ

        # if no representative found, return its name
        return typ #.name # typ.get_primitive_name()

    def find_same_type(self, param):
        if isinstance(param.type, types.UnionType):
            items = param.type.items
        elif isinstance(param.type, types.ArrayType):
            items = [param.type.item]
        else:
            items = [param.type]

        params = self.dsu._parents.keys()
        for p in params:
            has_same_name = False
            for item in items:
                if same_type_name(p.type, item):
                    has_same_name = True

            if p == param or has_same_name:
                group = self.dsu.get_group(p)
                rep = get_representative(group)

                if rep is not None:
                    # if param.type.name is not None:
                    #     param.type.aliases.add(param.type.name)
                    param.type.name = rep

                    if isinstance(param.type, types.ArrayType):
                        # if param.type.item.name is not None:
                        #     param.type.item.aliases.add(param.type.item.name)
                        param.type.item.name = rep

                break

        return param

    def set_type(self, param, infer_type=True):
        """set type for a given parameter
        if the parameter is an ad-hoc object,
        it will be splitted into several sub-params

        Args:
            param: the request/response parameter to be splitted
        """
        if not infer_type:
            return param
        # if param.func_name == "/conversations.members":
        #     print("finding type for parameter", param)
        param_typ = param.type
        if isinstance(param_typ, types.ArrayType):
            param_item = Parameter(
                param.method,
                defs.INDEX_ANY,
                param.func_name,
                param.path + [defs.INDEX_ANY],
                param.is_required,
                param.array_level + 1,
                param_typ.get_item(),
                None)
            param_item = self.set_type(param_item)
            param.type.item = param_item.type
        else:
            params = self.dsu._parents.keys()
            for p in params:
                if p == param:
                    # if param.func_name == "/conversations.members":
                    #     print("found parameter", p)
                    group = self.dsu.get_group(p)
                    rep = get_representative(group)
                    if rep is not None:
                        # if param.type.name is not None:
                        #     param.type.aliases.add(param.type.name)
                        param.type.name = rep
                        # if param.func_name == "/conversations.members":
                        #     print("found parameter type", rep)
                    break
            
            if (self._uncovered_opt == consts.UncoveredOption.EXCLUDE and (
                param.type.name == defs.TYPE_BOOL or
                param.type.name == defs.TYPE_INT or
                param.type.name == defs.TYPE_STRING or
                param.type.name == defs.TYPE_NUM or
                param.type.name == defs.TYPE_OBJECT)):
                param.type.name = str(param) # defs.TYPE_UNK

        return param

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
