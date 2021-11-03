from collections import defaultdict
import itertools
import re

from synthesizer.utils import make_entry_name
from analyzer.utils import path_to_name
from program.program import (Program, VarExpr, ProjectionExpr, ObjectExpr,
                             FilterExpr, AssignExpr, AppExpr)
import consts

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
        expr_subst = {}
        # add inputs
        for name, in_typ in inputs.items():
            self._add_typed_var(typ_subst, VarExpr(name, in_typ), in_typ)

        for trans in transitions:
            if consts.PREFIX_CLONE in trans:
                continue    

            sig = self._signatures.get(trans)
            if not sig:
                raise Exception(f"Unknown transition name {trans}")

            if consts.PREFIX_CONVERT in trans:
                # copy expressions with semantic types to corresponding syntactic types
                self._to_syntactic_mapping(typ_subst, sig)
            elif consts.PREFIX_PARTIAL in trans:
                self._generate_partial_object(typ_subst, expr_subst, sig)
            elif re.search(r"projection\(.*, .*\)", sig.endpoint):
                self._generate_projection(typ_subst, expr_subst, sig)
            elif re.search(r"filter\(.*, .*\)", sig.endpoint):
                self._generate_filter(typ_subst, expr_subst, sig)
            else:
                self._generate_let(typ_subst, expr_subst, sig)

        # print(typ_subst)
        returns = typ_subst.get(str(target.ignore_array()), [])
        # print("returns", returns)
        exprs = expr_subst.values()
        expr_vars = expr_subst.keys()

        program_bodys = set()
        for expr_list in itertools.product(*exprs):
            program_exprs = []
            for x, e in zip(expr_vars, expr_list):
                let_expr = AssignExpr(x, e, False)
                program_exprs.append(let_expr)

            for r in returns:
                program_bodys.add(tuple(program_exprs + [r]))

        # return programs that are equivalent in strings
        programs = set()
        for body in program_bodys:
            body = list(body)
            p = Program(list(inputs.keys()), body)
            p._expressions = p.reachable_expressions({})
            # print(typ_subst)
            # print(expr_subst)
            # print("before filtering", p)
            if self._filter_by_names(self._signatures, transitions, inputs, p):
                # if len(transitions) == 5:
                # print("Before lifting", p, flush=True)
                cache = {}
                p = p.lift(cache, self._name_counters, self._signatures, target)
                if p is not None:
                    # print("after lifting", p, flush=True)
                    # print(p.to_expression({}))
                    programs.add(p)

        # raise Exception
        return programs

    def _to_syntactic_mapping(self, typ_subst, sig):
        from_typ = str(sig.parameters[0].type.ignore_array())
        to_typ = str(sig.response.type.ignore_array())
        exprs = typ_subst.get(from_typ, [])
        typ_subst[to_typ] = [k for k,_ in itertools.groupby(sorted(typ_subst.get(to_typ, []) + exprs, key=str))]

    def _filter_by_names(self, signatures, transitions, inputs, result):
        name_counts = defaultdict(int)
        name_counts.clear()
        for tr in transitions:
            if (consts.PREFIX_CLONE in tr or 
                consts.PREFIX_CONVERT in tr or
                consts.PREFIX_PARTIAL in tr):
                continue
            elif re.search(r"projection\(.*, .*\)", tr):
                sig = signatures.get(tr)
                name = (f"projection("
                    f"{[p.type.ignore_array() for p in sig.parameters]},"
                    f" {sig.response.type.ignore_array()})")
            elif re.search(r"filter\(.*, .*\)", tr):
                sig = signatures.get(tr)
                name = (f"filter("
                    f"{[p.type.ignore_array() for p in sig.parameters]},"
                    f" {sig.response.type.ignore_array()})")
            else:
                name = tr

            name_counts[name] += 1

        real_counts = defaultdict(int)
        real_counts.clear()
        
        for e in result._expressions:
            if isinstance(e, AssignExpr):
                expr = e._rhs

                if isinstance(expr, ProjectionExpr):
                    name = (f"projection("
                        f"[{expr._obj.type.ignore_array()}],"
                        f" {expr.type.ignore_array()})")
                elif isinstance(expr, FilterExpr):
                    name = (f"filter("
                        f"{[expr._obj.type.ignore_array(), expr._val.type.ignore_array()]},"
                        f" {expr._obj.type.ignore_array()})")
                elif isinstance(expr, AppExpr):
                    name = expr._fun
                else:
                    continue

                real_counts[name] += 1

        # print(real_counts)
        # print(name_counts)
        for name in name_counts:
            if (name not in real_counts or
                real_counts[name] != name_counts[name]):
                return False

        result_vars = result.get_vars()
        if not set(inputs.keys()).issubset(result_vars):
            return False

        return True

    def _add_typed_var(self, typ_subst, expr, typ):
        expr.set_type(typ)
        # print("setting", expr, "to type", typ)
        tname = str(typ.ignore_array())
        if tname in typ_subst:
            if expr not in typ_subst[tname]:
                typ_subst[tname].append(expr)
        else:
            typ_subst[tname] = [expr]

    def _add_results(self, typ_subst, expr_subst, let_x, expr, typ):
        if let_x not in expr_subst:
            expr_subst[let_x] = []            
        expr_subst[let_x].append(expr)

        var_x = VarExpr(let_x)
        if isinstance(typ, list):
            for t in typ:
                self._add_typed_var(typ_subst, var_x, t)
        else:
            self._add_typed_var(typ_subst, var_x, typ)

    def _generate_args(self, typ_subst, expr_subst, sig):
        # get variables for each parameter type
        args_list = [[]]
        for param in sig.parameters:
            if not param.is_required and not param.type:
                continue

            typ = param.type
            typ_name = str(typ.ignore_array())
            if param.is_required and typ_name not in typ_subst:
                print(typ_subst)
                raise Exception(
                    f"Given path is spurious, "
                    f"no program can be generated for {sig.endpoint}, "
                    f"param {param} with type {typ_name}"
                )

            exprs = typ_subst.get(typ_name)
            if exprs is not None:
                if exprs == []:
                    print("Find no expression for type", typ_name)

                # print("Find expressions for type", typ)
                arg_exprs = []
                for expr in exprs:
                    if not isinstance(expr, VarExpr):
                        raise Exception("should get variable here")

                    # expr.set_type(typ)
                    # for e in expr_subst.get(expr.var, []):
                    #     e.set_type(typ)

                    # arg_name = path_to_name(param.path)
                    arg_exprs.append((param, expr))

                old_args_list = [args[:] for args in args_list]
                for i, args in enumerate(old_args_list):
                    if len(args) >= 4: 
                        # set a upper bound for how many parameter we will use
                        # replace any of the existing args instead of expanding it
                        for i in range(len(args)):
                            if args[i][0][0].is_required: # don't replace required args
                                continue

                            tmp_args = args[:]
                            tmp_args[i] = arg_exprs
                            args_list.append(tmp_args)
                    else:
                        args_list[i].append(arg_exprs)

                # optional arguments can be either added or not
                if not param.is_required:
                    args_list += old_args_list

        return args_list

    def _generate_partial_object(self, typ_subst, expr_subst, sig):
        args_list = self._generate_args(typ_subst, expr_subst, sig)
        let_x = self._fresh_var("x")
        for args in args_list:
            for params in itertools.product(*args):
                obj = {}
                for param, expr in params:
                    obj[param.arg_name] = expr

                typ = sig.response.type
                obj_expr = ObjectExpr(obj, typ, sig)
                self._add_results(typ_subst, expr_subst, let_x, obj_expr, typ)

    def _generate_projection(self, typ_subst, expr_subst, sig):
        args = self._generate_args(typ_subst, expr_subst, sig)
        args = args[0]
        let_x = self._fresh_var("x")
        for params in itertools.product(*args):
            obj = params[0][1]
            field = re.search(r"projection\(.*, (.*)\)", sig.endpoint).group(1)
            typ = sig.response.type
            # print("!!!!", sig.endpoint, typ)
            proj_expr = ProjectionExpr(obj, field, typ, sig)
            self._add_results(typ_subst, expr_subst, let_x, proj_expr, typ)

    def _generate_filter(self, typ_subst, expr_subst, sig):
        args = self._generate_args(typ_subst, expr_subst, sig)
        args = args[0]
        args = args[:2]
        let_x = self._fresh_var("x")
        for params in itertools.product(*args):
            # get only the required obj
            obj = params[0][1]
            val = params[1][1]
            field = re.search(r"filter\(.*, (.*)\)", sig.endpoint).group(1)
            field = '.'.join(field.split('.')[1:])
            # filter may only have one single output type
            typ = sig.response.type
            # print("!!!!", sig.endpoint, typ)
            # print("!!!!", obj, obj.type)
            # print("!!!!", val, val.type)
            filter_expr = FilterExpr(obj, field, val, False, typ, sig)
            self._add_results(typ_subst, expr_subst, let_x, filter_expr, typ)

    def _generate_let(self, typ_subst, expr_subst, sig):
        args_list = self._generate_args(typ_subst, expr_subst, sig)
        let_x = self._fresh_var("x")
        for args in args_list:
            for params in itertools.product(*args):
                named_args = []
                for param, arg in params:
                    arg_name = path_to_name(param.path)
                    named_args.append((arg_name, arg))

                f = make_entry_name(sig.endpoint, sig.method)
                app_expr = AppExpr(f, named_args, sig.response.type, sig)
                self._add_results(
                    typ_subst, expr_subst,
                    let_x, app_expr, sig.response.type)
            
