from collections import defaultdict
import itertools
import functools
import re
import copy

from program.program import (Program, VarExpr, ProjectionExpr,
                             FilterExpr, MapExpr, AssignExpr, AppExpr)
from schemas.schema_type import SchemaType
from openapi import defs


class ProgramGenerator:
    def __init__(self, signatures):
        self._signatures = signatures
        self._name_counters = defaultdict(int)

    def _fresh_var(self, prefix):
        counter = self._name_counters.get(prefix, 0)
        self._name_counters[prefix] += 1
        return f"{prefix}{counter}"

    def add_signature(self, name, sig):
        self._signatures[name] = sig

    def generate_program(self, transitions, inputs, target):
        self._name_counters.clear()

        typ_subst = {}
        # add inputs
        for name, in_typ in inputs.items():
            # in_typ = in_typ.name
            self._add_typed_var(typ_subst, VarExpr(name, in_typ), in_typ, 0)

        results = []
        for trans in transitions:
            sig = self._signatures.get(trans)
            if not sig:
                raise Exception(f"Unknown transition name {trans}")

            if re.search(r"projection\(.*, .*\)", sig.endpoint):
                self._generate_projection(typ_subst, sig)
            elif re.search(r"filter\(.*, .*\)", sig.endpoint):
                self._generate_filter(typ_subst, sig)
            else:
                self._generate_let(typ_subst, sig)

            # print(sig.endpoint, exprs)

        # for t, exprs in typ_subst.items():
        #     print(t)
        #     for e in exprs:
        #         print(e)
        exprs = typ_subst.get(target.name, [])

        programs = []
        for expr, _ in exprs:
            expr.type = target
            p = Program(list(inputs.keys()), [expr])
            # print(p.pretty())
            if self._filter_by_names(transitions, p):
                # print(p)
                p = p.to_multiline(self._name_counters)
                p.simplify()
                # print(p.pretty())
                # print(p.remove_map().pretty())
                programs.append(p)
                # print("get satisfying program", p.to_expression({}))

        # raise Exception
        return programs

    def _filter_by_names(self, transitions, result):
        name_counts = defaultdict(int)
        name_counts.clear()
        for tr in transitions:
            name = re.search(r"(.*):.*", tr).group(1)
            name_counts[name] += 1

        real_counts = defaultdict(int)
        real_counts.clear()
        exprs = []

        def get_subexprs(e):
            if isinstance(e, AssignExpr):
                return get_subexprs(e._rhs)
            elif isinstance(e, MapExpr):
                obj_subexprs = get_subexprs(e._obj)
                prog_subexprs = get_subexprs(e._prog)
                return obj_subexprs + prog_subexprs
            elif isinstance(e, Program):
                results = []
                for expr in e._expressions:
                    results += get_subexprs(expr)
                return results
            elif isinstance(e, ProjectionExpr):
                subexprs = get_subexprs(e._obj)
                return [e] + subexprs
            elif isinstance(e, FilterExpr):
                obj_subexprs = get_subexprs(e._obj)
                val_subexprs = get_subexprs(e._val)
                return [e] + obj_subexprs + val_subexprs
            elif isinstance(e, VarExpr):
                return []
            elif isinstance(e, AppExpr):
                arg_subexprs = [get_subexprs(arg) for _, arg in e._args]
                return functools.reduce(lambda x, y: x + y, arg_subexprs, [e])
            else:
                return [e]

        for expr in result.reachable_expressions({}):
            exprs += get_subexprs(expr)

        for expr in exprs:
            if isinstance(expr, ProjectionExpr):
                name = f"projection({expr._obj.type}, {expr._field})"
            elif isinstance(expr, FilterExpr):
                name = f"filter({expr._obj.type}, {expr._obj.type}.{expr._field})"
            elif isinstance(expr, AppExpr):
                name = expr._fun
            else:
                raise Exception("Unknown expression type", expr)
            real_counts[name] += 1

        # print(real_counts)
        # print(name_counts)
        for name in name_counts:
            if name not in real_counts or real_counts[name] < name_counts[name]:
                return False

        return True

    def _add_typed_var(self, typ_subst, expr, typ, is_list):
        tname = typ.name
        if tname in typ_subst:
            typ_subst[tname].append((expr, is_list))
        else:
            typ_subst[tname] = [(expr, is_list)]

    def _add_results(self, typ_subst, x, typ, array_level):
        if isinstance(typ, list):
            for t in typ:
                self._add_typed_var(typ_subst, x, t, array_level)
        else:
            self._add_typed_var(typ_subst, x, typ, array_level)

    def _generate_args(self, typ_subst, sig):
        # get variables for each parameter type
        args = []
        for param in sig.parameters:
            # TODO: deal with optional arguments
            if not param.is_required and not param.type:
                continue

            typ = param.type.name
            if param.is_required and param.type.name not in typ_subst:
                raise Exception(
                    f"Given path is spurious, "
                    f"no program can be generated for {sig.endpoint}"
                )

            exprs = typ_subst.get(typ)
            if exprs is not None:
                # print("Find expressions for type", typ)
                arg_exprs = []
                for expr, list_lv in exprs:
                    maps, obj = self._add_map(expr, typ, list_lv)
                    obj.type = SchemaType(typ, None)
                    arg_exprs.append((param.arg_name, maps, obj))
                args.append(arg_exprs)

        return args

    def _add_map(self, obj, typ, lv):
        results = []

        map_obj = copy.deepcopy(obj)
        for _ in range(lv):
            map_x = self._fresh_var("x")
            results.append((map_obj, map_x))
            map_obj = VarExpr(map_x, typ)

        return results, map_obj

    def _generate_projection(self, typ_subst, sig):
        args = self._generate_args(typ_subst, sig)
        for params in itertools.product(*args):
            maps = params[0][1]
            obj = params[0][2]
            field = re.search(r"projection\(.*, (.*)\)", sig.endpoint).group(1)
            typ = sig.response.type

            map_body = ProjectionExpr(obj, field)
            for o, x in reversed(maps):
                map_body = MapExpr(o, Program([x], [map_body]))

            # print("get projection expr", map_body)
            self._add_results(
                typ_subst, map_body, typ, 
                len(maps) + sig.response.array_level
            )    

    def _generate_filter(self, typ_subst, sig):
        args = self._generate_args(typ_subst, sig)
        args = args[:2]
        # print("args for filter", args)
        for params in itertools.product(*args):
            # print("param length for filter", len(params))
            # get only the required obj
            obj_maps = params[0][1]
            obj = params[0][2]
            val_maps = params[1][1]
            val = params[1][2]
            # print("filter obj type", obj.type)
            # print("filter val type", val.type)
            field = re.search(r"filter\(.*, (.*)\)", sig.endpoint).group(1)
            field = '.'.join(field.split('.')[1:])
            # filter may only have one single output type
            typ = sig.response.type
            
            # print("collapse for filter")
            # filter works for one level of list, get rid of the first map
            if len(obj_maps) > 0:
                obj = obj.apply_subst({obj_maps[-1][1]: obj_maps[-1][0]})
            # print("collapsed obj", obj)
            if len(val_maps) > 0:
                val = val.apply_subst({val_maps[-1][1]: val_maps[-1][0]})
            # print("collapsed val", val)
            map_body = FilterExpr(obj, field, val, len(val_maps) > 0)
            for v, x in reversed(val_maps[:-1]):
                map_body = MapExpr(v, Program([x], [map_body]))

            for o, x in reversed(obj_maps[:-1]):
                map_body = MapExpr(o, Program([x], [map_body]))
            
            # print("get filter expr", map_body)
            self._add_results(
                typ_subst, map_body, typ, 
                1 + len(val_maps[:-1]) + len(obj_maps[:-1]),
            )

    def _generate_let(self, typ_subst, sig):
        args = self._generate_args(typ_subst, sig)
        for params in itertools.product(*args):
            map_pairs = []
            named_args = []
            for arg_name, arg_maps, arg in params:
                map_pairs += arg_maps
                named_args.append((arg_name, arg))

            map_body = AppExpr(sig.endpoint, named_args)
            for arg, x in reversed(map_pairs):
                map_body = MapExpr(arg, Program([x], [map_body]))

            self._add_results(
                typ_subst, map_body, sig.response.type,
                sig.response.array_level + len(map_pairs)
            )