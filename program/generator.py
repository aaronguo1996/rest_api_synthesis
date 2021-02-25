from collections import defaultdict
import itertools
import functools
import re

from program.program import *
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
            self._add_typed_var(typ_subst, name, in_typ, 0)

        results = []
        for trans in transitions:
            sig = self._signatures.get(trans)
            if not sig:
                raise Exception(f"Unknown transition name {trans}")

            if re.search(r"projection\(.*, .*\)", sig.endpoint):
                exprs = self._generate_projection(typ_subst, sig)
                if exprs:
                    results.append(exprs)
            elif re.search(r"filter\(.*, .*\)", sig.endpoint):
                exprs = self._generate_filter(typ_subst, sig)
                results.append(exprs)
            else:
                exprs = self._generate_let(typ_subst, sig)
                results.append(exprs)

            # print(sig.endpoint, exprs)

        expr = typ_subst.get(target.name, [])
        results.append([e[0] for e in expr])

        programs = []
        for exprs in itertools.product(*results):
            p = Program(list(inputs.keys()), list(exprs))
            # print(p)
            if self._filter_by_names(transitions, p):
                # p.merge_maps()
                # p.merge_projections({})
                programs.append(p)
                print(p.to_expression({}))

        # raise Exception
        return programs

    def _filter_by_names(self, transitions, result):
        name_counts = defaultdict(int)
        for tr in transitions:
            if re.search(r"projection\(.*, .*\)", tr):
                name = "projection"
            elif re.search(r"filter\(.*, .*\)", tr):
                name = "filter"
            else:
                name = re.search(r"(.*):.*", tr).group(1)

            name_counts[name] += 1

        real_counts = defaultdict(int)
        exprs = []

        def get_subexprs(e):
            if isinstance(e, AssignExpr):
                return get_subexprs(e._rhs)
            elif isinstance(e, MapExpr):
                return get_subexprs(e._prog)
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

        for expr in result.reachable_expressions():
            exprs += get_subexprs(expr)

        for expr in exprs:
            if isinstance(expr, ProjectionExpr):
                name = "projection"
            elif isinstance(expr, FilterExpr):
                name = "filter"
            elif isinstance(expr, AppExpr):
                name = expr._fun
            else:
                raise Exception("Unknown expression type", expr)
            real_counts[name] += 1

        # print(real_counts)
        # print(name_counts)
        for name in name_counts:
            if real_counts[name] != name_counts[name]:
                return False

        return True

    def _add_typed_var(self, typ_subst, name, typ, is_list):
        v = VarExpr(name, typ)
        tname = typ.name
        if tname in typ_subst:
            typ_subst[tname].append((v, is_list))
        else:
            typ_subst[tname] = [(v, is_list)]

    def _generate_args(self, typ_subst, sig):
        # get variables for each parameter type
        args = []
        for param in sig.parameters:
            # TODO: deal with optional arguments
            if not param.is_required and not param.type:
                continue

            typ = param.type.name
            if param.is_required and param.type.name not in typ_subst:
                raise Exception(f"Given path is spurious, no program can be generated for {sig.endpoint}")

            ids = typ_subst.get(typ)
            if ids:
                # raise Exception(f"Given path is spurious, no program can be generated for {sig.endpoint} with type {typ}")
                args.append([(param.arg_name, x, is_list) for (x, is_list) in ids])

        return args

    def _generate_projection(self, typ_subst, sig):
        results = []
        args = self._generate_args(typ_subst, sig)
        for params in itertools.product(*args):
            obj = params[0][1]
            obj_is_list = params[0][2]
            field = re.search(r"projection\(.*, (.*)\)", sig.endpoint).group(1)
            typ = sig.responses[0].type

            if obj_is_list:   
                map_x = self._fresh_var("x")
                proj_expr = ProjectionExpr(VarExpr(map_x, obj.type), field, typ)
                map_body = proj_expr
                for i in range(obj_is_list - 1):
                    next_x = self._fresh_var("x")
                    map_body = MapExpr(
                        VarExpr(next_x),
                        Program([map_x], [map_body])
                    )
                    map_x = next_x

                map_body = MapExpr(obj, Program([map_x], [map_body]))

                let_x = self._fresh_var("x")
                let_expr = AssignExpr(let_x, map_body)
                results.append(let_expr)

                for r in sig.responses:
                    typ = r.type
                    self._add_typed_var(typ_subst, let_x, typ, obj_is_list)
            else:
                proj_expr = ProjectionExpr(obj, field, typ)

                for r in sig.responses:
                    typ = r.type.name
                    if typ in typ_subst:
                        typ_subst[typ].append((proj_expr, 0))
                    else:
                        typ_subst[typ] = [(proj_expr, 0)]

        return results

    def _generate_filter(self, typ_subst, sig):
        x = self._fresh_var("x")

        results = []
        args = self._generate_args(typ_subst, sig)
        for params in itertools.product(*args):
            obj = params[0][1]
            obj_is_list = params[0][2]
            val = params[1][1]
            val_is_list = params[1][2]
            field = re.search(r"filter\(.*, (.*)\)", sig.endpoint).group(1)
            field = '.'.join(field.split('.')[1:])
            typ = sig.responses[0].type
            if obj_is_list > 1:
                map_x = self._fresh_var("x")
                filter_expr = FilterExpr(
                    VarExpr(map_x, obj.type),
                    field, val, val_is_list, typ
                )
                map_expr = MapExpr(obj, Program([map_x], [filter_expr]))
                results.append(AssignExpr(x, map_expr))
            else:
                filter_expr = FilterExpr(obj, field, val, val_is_list, typ)
                results.append(AssignExpr(x, filter_expr))

        for r in sig.responses:
            typ = r.type
            self._add_typed_var(typ_subst, x, typ, r.array_level)

        return results

    def _generate_let(self, typ_subst, sig):
        # get a fresh type variable
        x = self._fresh_var("x")

        results = []
        args = self._generate_args(typ_subst, sig)
        for params in itertools.product(*args):
            map_pairs = []
            named_args = []
            for arg_name, arg, is_list in params:
                if is_list:
                    map_x = self._fresh_var("x")
                    map_pairs.append((arg, map_x))
                    for _ in range(is_list - 1):
                        next_x = self._fresh_var("x")
                        map_pairs.append((VarExpr(map_x, arg.type), next_x))
                        map_x = next_x
                    named_args.append((arg_name, VarExpr(map_x, arg.type)))
                else:
                    named_args.append((arg_name, arg))

            expr = AppExpr(sig.endpoint, named_args)
            if len(map_pairs) > 0:
                let_x = self._fresh_var("x")
                expr = [AssignExpr(let_x, expr), VarExpr(let_x)]
            
            map_pairs.reverse()
            for arg, xx in map_pairs:
                if isinstance(expr, list):
                    expr = MapExpr(arg, Program([xx], expr))
                else:
                    expr = MapExpr(arg, Program([xx], [expr]))
            results.append(AssignExpr(x, expr))

        for r in sig.responses:
            typ = r.type
            self._add_typed_var(typ_subst, x, typ, r.array_level + len(map_pairs))

        return results