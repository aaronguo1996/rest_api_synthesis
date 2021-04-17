from collections import defaultdict
import itertools
import functools
import re
from synthesizer.utils import make_entry_name

from program.program import (Program, VarExpr, ProjectionExpr,
                             FilterExpr, MapExpr, AssignExpr, AppExpr)
from schemas.schema_type import SchemaType


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
            self._add_typed_var(typ_subst, VarExpr(name, in_typ), in_typ)

        for trans in transitions:
            if "_clone" in trans:
                continue

            sig = self._signatures.get(trans)
            if not sig:
                raise Exception(f"Unknown transition name {trans}")

            if re.search(r"projection\(.*, .*\)", sig.endpoint):
                self._generate_projection(typ_subst, sig)
            elif re.search(r"filter\(.*, .*\)", sig.endpoint):
                self._generate_filter(typ_subst, sig)
            else:
                self._generate_let(typ_subst, sig)

        exprs = typ_subst.get(target.name, [])

        programs = []
        for expr in exprs:
            expr.set_type(target)
            p = Program(list(inputs.keys()), [expr])
            if self._filter_by_names(self._signatures, transitions, p):
                programs.append(p)

        # raise Exception
        return programs

    def _filter_by_names(self, signatures, transitions, result):
        name_counts = defaultdict(int)
        name_counts.clear()
        for tr in transitions:
            if "_clone" in tr:
                continue
            elif re.search(r"projection\(.*, .*\)", tr):
                sig = signatures.get(tr)
                name = f"projection({[p.type for p in sig.parameters]}, {sig.response.type})"
            elif re.search(r"filter\(.*, .*\)", tr):
                sig = signatures.get(tr)
                name = f"filter({[p.type for p in sig.parameters]}, {sig.response.type})"
            else:
                name = tr

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

        # for expr in result:
        exprs = get_subexprs(result)

        for expr in exprs:
            if isinstance(expr, ProjectionExpr):
                name = f"projection([{expr._obj.type}], {expr.type})"
            elif isinstance(expr, FilterExpr):
                name = f"filter({[expr._obj.type, expr._val.type]}, {expr._obj.type})"
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

    def _add_typed_var(self, typ_subst, expr, typ):
        tname = typ.name
        if tname in typ_subst:
            typ_subst[tname].append(expr)
        else:
            typ_subst[tname] = [expr]

    def _add_results(self, typ_subst, x, typ):
        if isinstance(typ, list):
            for t in typ:
                self._add_typed_var(typ_subst, x, t)
        else:
            self._add_typed_var(typ_subst, x, typ)

    def _generate_args(self, typ_subst, sig):
        # get variables for each parameter type
        args_list = [[]]
        for param in sig.parameters:
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
                for expr in exprs:
                    expr.set_type(SchemaType(typ, None))
                    arg_exprs.append((param.arg_name, expr))

                old_args_list = [args[:] for args in args_list]
                for args in args_list:
                    args.append(arg_exprs)

                # optional arguments can be either added or not
                if not param.is_required:
                    args_list += old_args_list

        return args_list

    def _generate_projection(self, typ_subst, sig):
        args = self._generate_args(typ_subst, sig)
        args = args[0]
        for params in itertools.product(*args):
            obj = params[0][1]
            field = re.search(r"projection\(.*, (.*)\)", sig.endpoint).group(1)
            typ = sig.response.type
            proj_expr = ProjectionExpr(obj, field)
            self._add_results(typ_subst, proj_expr, typ)

    def _generate_filter(self, typ_subst, sig):
        args = self._generate_args(typ_subst, sig)
        args = args[0]
        args = args[:2]
        for params in itertools.product(*args):
            # get only the required obj
            obj = params[0][1]
            val = params[1][1]
            field = re.search(r"filter\(.*, (.*)\)", sig.endpoint).group(1)
            field = '.'.join(field.split('.')[1:])
            # filter may only have one single output type
            typ = sig.response.type
            filter_expr = FilterExpr(obj, field, val, False)
            self._add_results(typ_subst, filter_expr, typ)

    def _generate_let(self, typ_subst, sig):
        args_list = self._generate_args(typ_subst, sig)
        for args in args_list:
            for params in itertools.product(*args):
                named_args = []
                for arg_name, arg in params:
                    named_args.append((arg_name, arg))

                f = make_entry_name(sig.endpoint, sig.method)
                app_expr = AppExpr(f, named_args)
                self._add_results(typ_subst, app_expr, sig.response.type)
            
