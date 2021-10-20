import random

from synthesizer.utils import make_entry_name
from analyzer.multiplicity import MUL_ONE_ONE, MUL_ZERO_MORE, MUL_ZERO_ONE
from analyzer.dynamic import Goal
import program.utils as utils
import consts
from analyzer.utils import name_to_path
from schemas import types
from openapi import defs

class Expression:
    def __init__(self, typ, signature):
        self.type = typ
        self.signature = signature

    def __repr__(self):
        return self.__str__()

    def __hash__(self):
        return hash(self.__str__())

    def apply_subst(self):
        raise NotImplementedError

    def pretty_with_type(self):
        return f"{self}: {self.type}"

    def set_type(self, typ):
        self.type = typ

    def pretty(self, hang):
        return f"{consts.SPACE * hang}" + self.__str__()

    def collect_exprs(self):
        raise NotImplementedError

    def has_conversion(self):
        return False

class AppExpr(Expression):
    def __init__(self, fun, args, typ=None, sig=None):
        super().__init__(typ, sig)
        self._fun = fun
        self._args = args

    def __str__(self):
        arg_strs = [f"{x}={arg}" for x, arg in self._args]
        return f"{self._fun}({', '.join(arg_strs)})"

    def __eq__(self, other):
        if not isinstance(other, AppExpr):
            return NotImplemented

        return (
            self._fun == other._fun and
            self._args == other._args
        )

    @property
    def function(self):
        return self._fun

    @property
    def arguments(self):
        return self._args

    def get_arg(self, i):
        if i < 0 or i > self._args:
            raise IndexError

        return self._args[i]

    def apply_subst(self, subst):
        args = [(x, arg.apply_subst(subst)) for x, arg in self._args]
        return AppExpr(self._fun, args, self.type, self.signature)

    def collect_exprs(self):
        res = [self]
        for _, arg in self._args:
            res += arg.collect_exprs()

        return res
            
    def to_graph(self, graph):
        # print(self)
        nodes = [arg.to_graph(graph) for _, arg in self._args]
        v = self.type.name
        graph.add_node(v)
        for node in nodes:
            if node:
                graph.add_edge(node, v)
        return v

    def get_vars(self):
        arg_vars = [arg.get_vars() for _, arg in self._args]
        return set().union(*arg_vars)

    def execute(self, analyzer, _):
        # print("call:", self._fun)
        # print("names:", [x for x, _ in self._args])
        args = [arg.execute(analyzer, []) for _, arg in self._args]
        # print("vals:", args)

        # if any of the argument fails, the whole term fails
        for arg, _ in args:
            if arg is None:
                return None, consts.MAX_COST

        if args:
            arg_vals, arg_scores = zip(*args)
            arg_names = list(zip(*self._args))[0]
            # print("[App] arg names", arg_names)
            named_arg_vals = list(zip(arg_names, arg_vals))
            # print("[App] arg names and vals", list(named_arg_vals))
        else:
            arg_scores = [0]
            named_arg_vals = []

        val = analyzer.get_trace(self._fun, named_arg_vals)
        if val is None:
            # print("fail to get successful trace for", self._fun, named_arg_vals)
            return None, consts.MAX_COST
        else:
            # print("[App] get back", val, "for", self._fun, named_arg_vals)
            return val, 1 + sum(arg_scores)

    def get_multiplicity(self, analyzer):
        return analyzer.check_endpoint(self._fun)

    def to_program_graph(self, graph, var_to_trans):
        for _, arg in self._args:
            arg_trans = arg.to_program_graph(graph, var_to_trans)
            if arg_trans is not None:
                graph.add_edge(arg_trans, self._fun)
            
        return self._fun

    def goal_search(self, analyzer, goal):
        print(self._fun, "has goal", goal)
        # we need to match the value and the fields, considering multiplicity
        if self._args:
            arg_names = list(zip(*self._args))[0]
        else:
            arg_names = []

        entries = analyzer.get_trace_by_goal(self._fun, arg_names, goal)
        if entries is None:
            return

        arg_values = {}
        for entry in entries:
            for param in entry.parameters:
                param_name = param.arg_name
                if param_name not in arg_values:
                    arg_values[param_name] = []

                arg_values[param_name].append(param.value)

        for x, arg in self._args:
            multi = MUL_ONE_ONE # TODO: is this correct?
            values = arg_values[x]
            fields = []
            arg_goal = Goal(multi, values, fields)
            arg.goal_search(analyzer, arg_goal)

    def to_multiline(self, signatures, subst, counter):
        exprs = []
        var = utils.find_expr(subst, self)
        if var is not None:
            let_var = var
        else:
            args = []
            for name, arg in self._args:
                arg_exprs, arg_expr = arg.to_multiline(
                    signatures, subst, counter)
                args.append((name, arg_expr))
                exprs.extend(arg_exprs)

            app_expr = AppExpr(self._fun, args, self.type, self.signature)

            let_x = counter.get("x", 0)
            counter["x"] += 1
            let_var = VarExpr(f"x{let_x}", self.type)

            sig = signatures.get(self._fun)
            if sig and sig.response.array_level > 0:
                let_expr = AssignExpr(f"x{let_x}", app_expr, True)
            else:
                let_expr = AssignExpr(f"x{let_x}", app_expr, False)

            exprs.append(let_expr)
            subst.append((self, let_var))

        return exprs, let_var

    def lookup_param(self, name):
        path = name_to_path(name)
        params = self.signature.parameters
        for param in params:
            if param.path == path:
                return param

    def lift(self, counter, signatures):
        sig = self.signature
        
        arguments = []
        exprs = []
        for name, arg in self._args:
            param = self.lookup_param(name)
            arg_binds, x, xt = insert_binds(counter, arg, param.type)
            exprs += arg_binds
            arguments.append((name, VarExpr(x, xt)))

        app_expr = AppExpr(self._fun, arguments, sig.response.type, sig)        
        return exprs, app_expr

    def check_fields(self, analyzer, var_to_trans):
        for _, arg in self._args:
            match, _ = arg.check_fields(analyzer, var_to_trans)
            if not match:
                return False, self._fun

        return True, self._fun

    def pretty(self, hang):
        return self.__str__()

    def sizes(self):
        num_endpoints, num_projections, size = 0, 0, 0
        for _, arg in self._args:
            eps, projs, sz = arg.sizes()
            num_endpoints += eps
            num_projections += projs
            size += sz

        return (num_endpoints + 1), num_projections, (size + 1)

    def has_conversion(self):
        # match the expected type with its actual type
        for name, arg in self._args:
            param = self.lookup_param(name)
            # print("param type", param.type)
            # print("arg type", arg.type)
            if str(arg.type) != str(param.type):
                return True

        return False

class VarExpr(Expression):
    def __init__(self, x, typ=None, sig=None):
        super().__init__(typ, sig)
        self._var = x

    def __str__(self):
        return self._var

    def __eq__(self, other):
        if not isinstance(other, VarExpr):
            return NotImplemented

        return self._var == other._var

    @property
    def var(self):
        return self._var

    def apply_subst(self, subst):
        ret = subst.get(self._var, VarExpr(self._var, self.type))
        ret.type = self.type
        return ret

    def collect_exprs(self):
        return [self]

    def to_graph(self, graph):
        # print(self)
        if self.type:
            v = self.type.name
            graph.add_node(v)
            return v

    def get_vars(self):
        return set([self._var])

    def execute(self, analyzer, candidates):
        val = analyzer.lookup_var(self._var)
        if val is None:
            if candidates:
                # print("sampling", self.var, "from", candidates)
                val = random.choice(candidates)
            else:
                # sample a value by type
                val = analyzer.sample_value_by_type(self.type)

            analyzer.push_var(self._var, val)

        # print("[Var] get back", val, "for", self._var)
        return val, 0

    def get_multiplicity(self, analyzer):
        var_mul = analyzer.lookup_var(self._var)
        # print("[Var]", self._var, analyzer.pretty(var_mul[1]))
        return var_mul

    def to_program_graph(self, graph, var_to_trans):
        return var_to_trans.get(self._var)

    def goal_search(self, analyzer, goal):
        analyzer.push_var(self._var, goal)

    def to_multiline(self, signatures, subst, counter):
        return [], self

    def check_fields(self, analyzer, var_to_trans):
        return True, var_to_trans.get(self._var)

    def pretty(self, hang):
        return self.__str__()

    def sizes(self):
        return 0, 0, 1

    def lift(self, counter, signatures):
        return [], self

class ProjectionExpr(Expression):
    def __init__(self, obj, field, typ=None, sig=None):
        super().__init__(typ, sig)
        self._obj = obj
        self._field = field

    def __str__(self):
        return f"{self._obj}.{self._field}"

    def __eq__(self, other):
        if not isinstance(other, ProjectionExpr):
            return NotImplemented

        return (
            self._obj == other._obj and
            self._field == other._field
        )

    def apply_subst(self, subst):
        return ProjectionExpr(
            self._obj.apply_subst(subst),
            self._field,
            self.type,
            self.signature,
        )

    def collect_exprs(self):
        res = [self] + self._obj.collect_exprs()
        return res

    def to_graph(self, graph):
        # print(self)
        n1 = self._obj.to_graph(graph)
        v = self.type.name
        graph.add_node(v)
        graph.add_edge(n1, v)
        return v

    def get_vars(self):
        obj_vars = self._obj.get_vars()
        return obj_vars

    def execute(self, analyzer, _):
        val, cost = self._obj.execute(analyzer, [])
        try:
            val = val.get(self._field)
            # if val is None:
            #     print("[Projection] field projection fails for", self._field)
            # print("[Projection] get back", val, "for", self._field)
            return val, cost + 1
        except:
            # print("[Projection] field projection fails for", self._field)
            return None, consts.MAX_COST

    def get_multiplicity(self, analyzer):
        return analyzer.check_endpoint(f"projection({self._obj.type}, {self._field})")
        # return self._obj.get_multiplicity(analyzer)

    def to_program_graph(self, graph, var_to_trans):
        obj_trans = self._obj.to_program_graph(graph, var_to_trans)
        proj_trans = f"projection({self._obj.type}, {self._field})"
        
        if obj_trans is not None:
            graph.add_edge(obj_trans, proj_trans)

        return proj_trans

    def goal_search(self, analyzer, goal):
        fields = goal.fields
        fields.insert(0, self._field)
        obj_goal = Goal(goal.multiplicity, goal.values, fields)
        self._obj.goal_search(analyzer, obj_goal)

    def to_multiline(self, signatures, subst, counter):
        var = utils.find_expr(subst, self)
        exprs = []
        if var is not None:
            proj_expr = var
        else:
            exprs, obj_expr = self._obj.to_multiline(signatures, subst, counter)
            proj_expr = ProjectionExpr(obj_expr, self._field, self.type, self.signature)

            proj_trans = f"projection({self._obj.type}, {self._field})"
            proj_name = make_entry_name(proj_trans, "")
            proj_sig = signatures.get(proj_name)
            if not proj_sig:
                raise Exception("cannot find signature for projection", proj_name)
            if proj_sig and proj_sig.response.array_level > 0:
                let_x = counter.get("x", 0)
                counter["x"] += 1
                bind_expr = AssignExpr(f"x{let_x}", proj_expr, True)
                exprs.append(bind_expr)
                proj_expr = VarExpr(f"x{let_x}", self.type)

            subst.append((proj_expr, self))
        
        return exprs, proj_expr

    def lift(self, counter, signatures):
        proj_sig = self.signature
        
        param = proj_sig.parameters[0]
        arg_binds, x, xt = insert_binds(counter, self._obj, param.type)
        proj_expr = ProjectionExpr(
            VarExpr(x, param.type),
            self._field,
            xt,
            proj_sig)
        return arg_binds, proj_expr

    def check_fields(self, analyzer, var_to_trans):
        # print(self)
        # print(type(self.type))
        match, trans = self._obj.check_fields(analyzer, var_to_trans)
        if match:
            match = analyzer.check_type_fields(
                self._obj.type.name, trans, self._field
            )
            analyzer.add_projection_field(
                self._obj.type.name, self.type.name, 
                trans, self._field
            )
        return match, trans

    def pretty(self, hang):
        return self.__str__()

    def sizes(self):
        endpoints, projections, sz = self._obj.sizes()
        return endpoints, (projections + 1), (sz + 1)

class EquiExpr(Expression):
    def __init__(self, lhs, rhs, typ=None, sig=None):
        super().__init__(typ, sig)
        self._lhs = lhs
        self._rhs = rhs

    def __str__(self):
        return f"if {self._lhs} = {self._rhs}"

    def __eq__(self, other):
        if not isinstance(other, EquiExpr):
            return NotImplemented

        return (
            self._lhs == other._lhs and
            self._rhs == other._rhs
        )

    def apply_subst(self, subst):
        return EquiExpr(
            self._lhs.apply_subst(subst),
            self._rhs.apply_subst(subst)
        )

    def collect_exprs(self):
        return self._lhs.collect_exprs() + self._rhs.collect_exprs() + [self]

    def execute(self, analyzer, _):
        lhs, lscore = self._lhs.execute(analyzer, [])
        candidates = [lhs]
        rhs, rscore = self._rhs.execute(analyzer, candidates)
        return lhs == rhs, lscore + rscore + 1

    def pretty(self, hang):
        return consts.SPACE * hang + f"if {self._lhs} = {self._rhs}"

    def lift(self, counter, signatures):
        raise NotImplementedError

    def get_vars(self):
        lhs_vars = self._lhs.get_vars()
        rhs_vars = self._rhs.get_vars()
        return lhs_vars.union(rhs_vars)

class FilterExpr(Expression):
    def __init__(self, obj, field, val, is_val_list, typ=None, sig=None):
        super().__init__(typ, sig)
        self._obj = obj
        self._field = field
        self._val = val
        self._is_val_list = is_val_list

    def __str__(self):
        return f"if {self._obj}.{self._field} = {self._val}"

    def __eq__(self, other):
        if not isinstance(other, FilterExpr):
            return NotImplemented

        return (
            self._obj == other._obj and
            self._field == other._field and
            self._val == other._val
        )

    def apply_subst(self, subst):
        return FilterExpr(
            self._obj.apply_subst(subst),
            self._field,
            self._val.apply_subst(subst),
            self._is_val_list,
            self.type,
        )

    def collect_exprs(self):
        res = [self] + self._obj.collect_exprs()
        return res + self._val.collect_exprs()

    def to_graph(self, graph):
        # print(self)
        n1 = self._obj.to_graph(graph)
        n2 = self._val.to_graph(graph)
        v = self.type.name
        graph.add_node(v)
        graph.add_edge(n1, v)
        graph.add_edge(n2, v)
        return v

    def get_vars(self):
        obj_vars = self._obj.get_vars()
        val_vars = self._val.get_vars()
        return obj_vars.union(val_vars)

    def execute(self, analyzer, _):
        obj, score1 = self._obj.execute(analyzer, [])
        
        if obj is None:
            return None, consts.MAX_COST

        paths = self._field.split('.')
        tmp = obj

        for p in paths:
            tmp = utils.get_field_value(tmp, p)
            if tmp is None:
                # print("[Filter] cannot find field", p, "in", tmp)
                break

        if isinstance(tmp, list):
            tmp = list(utils.flatten(tmp))
            val_candidates = tmp
        else:
            val_candidates = [tmp]
        
        val, score2 = self._val.execute(analyzer, val_candidates)
        # print("[Filter] get back", val, "as filter")
        if val is None:
            return None, consts.MAX_COST

        if tmp == val:
            variables = self._obj.get_vars()
            analyzer.push_var(list(variables)[0], obj)
            return obj, score1 + score2 + 1

        else:
            return None, consts.MAX_COST


    def get_multiplicity(self, analyzer):
        obj_mul = self._obj.get_multiplicity(analyzer)
        obj_typ = self._obj.type.name
        val_mul = self._val.get_multiplicity(analyzer)
        filter_field = obj_typ + "." + self._field
        if (filter_field in analyzer._unique_fields and 
            val_mul[1] is not MUL_ZERO_MORE):
            # print("[Filter]", filter_field, "is found in the analysis result")
            return obj_mul[0], MUL_ZERO_ONE
        else:
            # print("[Filter]", filter_field, "is not in the analysis result")
            return obj_mul[0], MUL_ZERO_MORE

    def to_program_graph(self, graph, var_to_trans):
        obj_trans = self._obj.to_program_graph(graph, var_to_trans)
        val_trans = self._val.to_program_graph(graph, var_to_trans)
        filter_trans = f"filter({self._obj.type}, {self._obj.type}.{self._field})"

        if obj_trans is not None:
            graph.add_edge(obj_trans, filter_trans)
        
        if val_trans is not None:
            graph.add_edge(val_trans, filter_trans)

        return filter_trans

    def goal_search(self, analyzer, goal):
        self._obj.goal_search(analyzer, goal)
        # find a field value such that the filter does not return empty lists
        val_goal = Goal(MUL_ONE_ONE, goal.values[:1])
        self._val.goal_search(analyzer, val_goal)

    def to_multiline(self, signatures, subst, counter):
        var = utils.find_expr(subst, self)
        exprs = []
        if var is not None:
            obj_expr = var
        else:
            val_exprs, val_expr = self._val.to_multiline(
                signatures, subst, counter)
            obj_exprs, obj_expr = self._obj.to_multiline(
                signatures, subst, counter)
            exprs = obj_exprs + val_exprs
            filter_expr = FilterExpr(
                obj_expr, self._field, 
                val_expr, self._is_val_list, self.type
            )

            exprs.append(filter_expr)
            # TODO: is this correct?
            subst.append((obj_expr, self))

        return exprs, obj_expr

    def check_fields(self, analyzer, var_to_trans):
        # print("Checking field", self._field, "for object", self._obj.type)
        match, trans = self._obj.check_fields(analyzer, var_to_trans)
        if match:
            match, _ = self._val.check_fields(analyzer, var_to_trans)

        if match:
            match = analyzer.check_type_fields(
                self._obj.type.name, trans, self._field
            )

        # print("check result:", match)
        return match, trans

    def pretty(self, hang):
        return consts.SPACE * hang + f"if {self._obj}.{self._field} = {self._val}"

    def sizes(self):
        obj_eps, obj_prs, obj_sz = self._obj.sizes()
        val_eps, val_prs, val_sz = self._val.sizes()
        return (obj_eps + val_eps), (obj_prs + val_prs), (obj_sz + val_sz + 1)

    def _expand_field(self, counter, signatures, field, in_typ, in_obj):
        proj_name = f"projection({in_typ}, {field})"
        trans_name = make_entry_name(proj_name, "")
        # print("getting signature for", trans_name)
        proj_sig = signatures.get(trans_name)
        if proj_sig is None:
            # print("cannot find projection", trans_name)
            return [], None

        proj_expr = ProjectionExpr(
            in_obj, field, 
            proj_sig.response.type, 
            proj_sig)
        binds, proj_expr = proj_expr.lift(counter, signatures)
        let_x = counter.get("x", 0)
        counter["x"] += 1
        expr = AssignExpr(f"x{let_x}", proj_expr, False)
        binds.append(expr)
        var = VarExpr(f"x{let_x}", proj_sig.response.type)
        return binds, var

    def lift(self, counter, sigs):
        """
        First expand the field into projections, then do the actual lifting
        """
        # print("lifting", self)
        filter_sig = self.signature
        # print("filter sig", [p.type for p in filter_sig.parameters], filter_sig.response.type)
        
        obj_param = filter_sig.parameters[0]
        obj_binds, obj_x, xt = insert_binds(counter, self._obj, obj_param.type)
        obj_expr = VarExpr(obj_x, xt)

        fields = self._field.split('.')
        in_typ = obj_param.type
        in_obj = obj_expr
        for f in fields:
            if f == defs.INDEX_ANY:
                continue

            in_typ = in_typ.ignore_array()
            binds, in_obj = self._expand_field(counter, sigs, f, in_typ, in_obj)

            # when previous expand step fails
            if in_obj is None:
                return [], None, None

            obj_binds += binds
            in_typ = in_obj.type

        val_param = filter_sig.parameters[1]
        # print("val param type", val_param.type, flush=True)
        lhs_binds, lhs_x, lhs_t = insert_binds(counter, in_obj, val_param.type)
        in_obj = VarExpr(lhs_x, lhs_t)
        val_binds, val_x, val_t = insert_binds(counter, self._val, val_param.type)
        val = VarExpr(val_x, val_t)

        filter_expr = EquiExpr(in_obj, val)

        return (obj_binds + lhs_binds + val_binds), filter_expr, obj_expr

class ListExpr(Expression):
    def __init__(self, expr, typ=None, sig=None):
        super().__init__(typ, sig)
        self._item = expr

    def __str__(self):
        return f"[{self._item}]"

    def __eq__(self, other):
        if not isinstance(other, ListExpr):
            return NotImplemented

        return self._item == other._item

    def pretty(self, hang):
        return f"return {self._item}"

    def apply_subst(self, subst):
        return ListExpr(self._item.apply_subst(subst))

    def collect_exprs(self):
        return [self] + self._item.collect_exprs()

    def get_vars(self):
        return self._item.get_vars()

    def execute(self, analyzer, _):
        item, score = self._item.execute(analyzer, [])
        return [item], score

    def to_program_graph(self, graph, var_to_trans):
        return self._item.to_program_graph(graph, var_to_trans)

    def check_fields(self, analyzer, var_to_trans):
        return self._item.check_fields(analyzer, var_to_trans)

    def sizes(self):
        item_eps, item_prs, item_sz = self._obj.sizes()
        return item_eps, item_prs, item_sz + 1

    def lift(self, counter, signatures):
        raise NotImplementedError

class AssignExpr(Expression):
    def __init__(self, x, expr, is_bind):
        super().__init__(None, None)
        self._lhs = x
        self._rhs = expr
        self._is_bind = is_bind

    def __str__(self):
        if self._is_bind:
            return f"{self._lhs} <- {self._rhs}"
        else:
            return f"let {self._lhs} = {self._rhs}"

    def __eq__(self, other):
        if not isinstance(other, AssignExpr):
            return NotImplemented

        return (
            self._lhs == other._lhs and
            self._rhs == other._rhs and
            self._is_bind == other._is_bind
        )

    @property
    def var(self):
        return self._lhs

    @property
    def expr(self):
        return self._rhs

    def taint_var(self, taint):
        rhs_vars = self._rhs.get_vars()
        rhs_reachable_vars = [taint.get(v, set()) for v in rhs_vars]
        reachable_vars = set().union(*rhs_reachable_vars)
        curr_reachable = taint.get(self._lhs, set())
        taint[self._lhs] = curr_reachable.union(rhs_vars, reachable_vars)

    def apply_subst(self, subst):
        return AssignExpr(
            self._lhs,
            self._rhs.apply_subst(subst),
            self._is_bind,
        )

    def collect_exprs(self):
        return [self] + self._rhs.collect_exprs()

    def to_graph(self, graph):
        # print(self)
        return self._rhs.to_graph(graph)

    def get_vars(self):
        rhs_vars = self._rhs.get_vars()
        rhs_vars.add(self._lhs)
        return rhs_vars

    def execute(self, analyzer, _):
        val, score = self._rhs.execute(analyzer, [])
        if val is None:
            return None

        analyzer.push_var(self.var, val)
        return score

    def get_multiplicity(self, analyzer):
        mul = self._rhs.get_multiplicity(analyzer)
        analyzer.push_var(self.var, mul)

    def to_program_graph(self, graph, var_to_trans):
        raise NotImplementedError

    def goal_search(self, analyzer, goal):
        raise NotImplementedError

    def to_multiline(self, signatures, subst, counter):
        raise NotImplementedError

    def check_fields(self, analyzer, var_to_trans):
        match, trans = self._rhs.check_fields(analyzer, var_to_trans)
        if match:
            var_to_trans[self.var] = trans

        return match, trans

    def pretty(self, hang):
        if self._is_bind:
            return f"{consts.SPACE * hang}{self._lhs} <- {self._rhs.pretty(hang)}"
        else:
            return f"{consts.SPACE * hang}let {self._lhs} = {self._rhs.pretty(hang)}"

    def sizes(self):
        endpoints, projections, sz = self._rhs.sizes()
        if self._is_bind:
            return endpoints, projections, sz + 1
        else:
            return endpoints, projections, sz

    def lift(self, counter, signatures):
        if isinstance(self._rhs, FilterExpr):
            binds, rhs, obj = self._rhs.lift(counter, signatures)
            if rhs is None:
                return None

            binds.append(rhs)
            expr = AssignExpr(self._lhs, obj, False)
        else:
            binds, rhs = self._rhs.lift(counter, signatures)
            expr = AssignExpr(self._lhs, rhs, False)
        
        binds.append(expr)
        return binds

    def has_conversion(self):
        return self._rhs.has_conversion()

class ProgramGraph:
    def __init__(self):
        self._adj = {}
        self._indegree = {}

    def add_edge(self, u, v):
        if u not in self._adj:
            self._adj[u] = []

        if v not in self._indegree:
            self._indegree[v] = 0

        self._adj[u].append(v)
        self._indegree[v] += 1

    def all_nodes(self):
        nodes = set()
        for k, v in self._adj.items():
            nodes.add(k)
            nodes = nodes.union(set(v))

        return nodes

    def indegree(self, v):
        if v not in self._indegree:
            self._indegree[v] = 0
        return self._indegree.get(v, 0)

    def dec_indegrees(self, v):
        for u in self._adj.get(v, []):
            self._indegree[u] -= 1

    def inc_indegrees(self, v):
        for u in self._adj.get(v, []):
            self._indegree[u] += 1

def all_topological_sorts(paths, graph, path, discovered):
    nodes = graph.all_nodes()
    for v in nodes:
        if graph.indegree(v) == 0 and not discovered.get(v, False):
            graph.dec_indegrees(v)
            path.append(v)
            discovered[v] = True
            all_topological_sorts(paths, graph, path, discovered)
            graph.inc_indegrees(v)
            path.pop()
            discovered[v] = False

    # print(path)
    if len(path) == len(nodes):
        # print("adding to result: ", path)
        paths.append(path[:])

class Program:
    def __init__(self, inputs, expressions):
        self._inputs = inputs
        self._expressions = expressions

    def __str__(self):
        expr_strs = [str(expr) + '    \n' for expr in self._expressions[:-1]]
        return (
            f"\\{' '.join(self._inputs)} -> {{\n"
            f"{''.join([consts.SPACE + expr for expr in expr_strs])}"
            f"{consts.SPACE}return {self._expressions[-1]}\n}}"
        )

    def __eq__(self, other):
        if not isinstance(other, Program):
            return NotImplemented

        if self._inputs == other._inputs:
            return self.to_expression({}) == other.to_expression({})
        elif len(self._inputs) == len(other._inputs):
            subst = {}
            for i, x in enumerate(other._inputs):
                if x != self._inputs[i]:
                    subst[x] = VarExpr(self._inputs[i])
            other = other.apply_subst(subst)
            return self.to_expression({}) == other.to_expression({})
        else:
            return False

    def __hash__(self):
        return hash((tuple(self._inputs), str(self.to_expression({}))))

    def __repr__(self):
        return self.__str__()

    def has_conversion(self):
        for expr in self._expressions:
            if expr.has_conversion():
                return True

        return False

    def to_expression(self, subst={}):
        exprs = []
        for expr in self._expressions:
            # eagerly substitute the previous variables into the new expression
            # print(expr)
            expr = expr.apply_subst(subst)
            if isinstance(expr, AssignExpr):
                subst[expr.var] = expr.expr
            else:
                exprs.append(expr)

        return exprs

    def apply_subst(self, subst={}):
        exprs = []
        for expr in self._expressions:
            expr = expr.apply_subst(subst)
            exprs.append(expr)

        return Program(self._inputs, exprs)

    def collect_exprs(self):
        exprs = []
        for expr in self._expressions:
            exprs += expr.collect_exprs()

        return exprs

    def remove_tautology(self):
        exprs = []
        for expr in self._expressions:
            if isinstance(expr, EquiExpr) and expr._lhs == expr._rhs:
                continue
            else:
                exprs.append(expr)

        self._expressions = exprs

    def get_vars(self):
        all_vars = set()
        for expr in self._expressions:
            all_vars = all_vars.union(expr.get_vars())

        return all_vars

    def reachable_expressions(self, taint={}):
        # print(self)
        for expr in self._expressions:
            if isinstance(expr, AssignExpr):
                expr.taint_var(taint)

        # print(taint)
        # print(expr)
        expr_vars = expr.get_vars()
        reachable_sets = [taint.get(v, set()) for v in expr_vars]
        reachable_vars = set(expr_vars).union(*reachable_sets)
        # print("reachable vars", reachable_vars)
        # raise Exception
        reachable_exprs = []
        for expr in self._expressions:
            if not isinstance(expr, AssignExpr) or expr.var in reachable_vars:
                reachable_exprs.append(expr)

        return reachable_exprs

    def to_graph(self, graph):
        # print("program, to_graph", self)
        expr = self.to_expression({})
        return expr.to_graph(graph)

    def merge_projections(self, subst={}):
        mark_delete = set()
        exprs = []
        for expr in self._expressions:
            before_vars = expr.get_vars()
            expr = expr.apply_subst(subst)
            after_vars = expr.get_vars()
            mark_delete = mark_delete.union(before_vars.difference(after_vars))
            if isinstance(expr, AssignExpr) and not expr._is_bind: 
                if isinstance(expr._rhs, ProjectionExpr):
                    subst[expr.var] = expr._rhs

            exprs.append(expr)

        self._expressions = [e for e in exprs
            if not isinstance(e, AssignExpr) or e.var not in mark_delete
        ]

    def merge_direct_eqs(self, subst={}):
        mark_delete = set()
        exprs = []
        for expr in self._expressions:
            expr = expr.apply_subst(subst)
            if isinstance(expr, AssignExpr) and not expr._is_bind:
                if isinstance(expr.expr, VarExpr):
                    subst[expr.var] = expr.expr
                    mark_delete.add(expr.var)

            exprs.append(expr)

        self._expressions = [e for e in exprs
            if not isinstance(e, AssignExpr) or e.var not in mark_delete
        ]

    def simplify(self):
        old_expressions = None
        while old_expressions != self._expressions:
            old_expressions = self._expressions.copy()
            self.merge_direct_eqs(subst={})
            self.merge_projections(subst={})
            # self.remove_tautology()
            # print("old", old_expressions)
            # print("new", self._expressions)

    def assign_type(self, t):
        self._expressions[-1].type = t

    def lift(self, counter, signatures, target):
        exprs = []
        for expr in self._expressions:
            if isinstance(expr, AssignExpr):
                lifted_exprs = expr.lift(counter, signatures)
                if lifted_exprs is None:
                    return None

                exprs += lifted_exprs
            else: # return statement
                # FIXME: is this correct?
                binds, x, _ = insert_binds(counter, expr, target.ignore_array())
                exprs += binds
                exprs.append(VarExpr(x, target))

        # print(exprs)
        program = Program(self._inputs, exprs)
        # print("before simplify", program, flush=True)
        program.simplify()
        return program

    def _execute_exprs(self, exprs, analyzer):
        if len(exprs) == 1:
            return exprs[0].execute(analyzer, [])
        else:
            expr = exprs[0]
            if isinstance(expr, AssignExpr): 
                val, cost = expr._rhs.execute(analyzer, [])
                if val is None:
                    # print(expr, "cannot be evaled")
                    return None, consts.MAX_COST

                if expr._is_bind:
                    if not isinstance(val, list):
                        # print(expr, "cannot be evaled")
                        return None, consts.MAX_COST

                    vals = []
                    bind_cost = 0
                    random.shuffle(val)
                    for v in val:
                        analyzer.push_var(expr.var, v)
                        sub_val, sub_cost = self._execute_exprs(exprs[1:], analyzer)
                        if sub_val is not None:
                            vals.append(sub_val)
                            bind_cost += sub_cost
                        analyzer.pop_var(expr.var)

                    if len(vals) == 0:
                        return None, consts.MAX_COST

                    if len(vals) > 0:
                        cost += bind_cost / len(vals)

                    val = vals
                else:
                    analyzer.push_var(expr.var, val)
                    val, sub_cost = self._execute_exprs(exprs[1:], analyzer)
                    cost += sub_cost
            elif isinstance(expr, EquiExpr):
                val, cost = expr.execute(analyzer, [])
                if val is None or val == False:
                    return None, consts.MAX_COST
                else:
                    val, sub_cost = self._execute_exprs(exprs[1:], analyzer)
                    cost += sub_cost
            else:
                val, cost = expr.execute(analyzer, [])
                if val is None:
                    # print(expr, "cannot be evaled")
                    return None, consts.MAX_COST

                val, sub_cost = self._execute_exprs(exprs[1:], analyzer)
                cost += sub_cost
            
            return val, cost

    def execute(self, analyzer):
        return self._execute_exprs(self._expressions, analyzer)
        
    def get_multiplicity(self, analyzer):
        for expr in self._expressions[:-1]:
            expr.get_multiplicity(analyzer)

        return self._expressions[-1].get_multiplicity(analyzer)

    def pretty(self, hang=0):
        indent = consts.SPACE * (hang + 1)
        newline = '\n'
        expr_strs = [
            expr.pretty(hang + 1) + newline
            for expr in self._expressions
        ]
        
        return (
            f"\\{' '.join(self._inputs)} -> {{{newline}"
            f"{''.join(expr_strs[:-1])}"
            f"{indent}return {expr_strs[-1][:-1]}{newline}"
            f"{consts.SPACE * hang}}}"
        )

    def to_program_graph(self, graph=ProgramGraph(), var_to_trans={}):
        for expr in self._expressions:
            if isinstance(expr, AssignExpr):
                v = expr.var
                trans = expr.expr.to_program_graph(graph, var_to_trans)
                var_to_trans[v] = trans
        
        # the last expression in the list
        return expr.to_program_graph(graph, var_to_trans)

    def goal_search(self, analyzer, goal):
        # initialization
        self._expressions[-1].goal_search(analyzer, goal)
        # iterate the previous lets
        for expr in reversed(self._expressions[:-1]):
            if isinstance(expr, AssignExpr):
                # expression: let x = rhs;
                rhs = expr.expr
                x = expr.var
                goal = analyzer.lookup_var(x)
                if goal is None:
                    return None

                rhs.goal_search(analyzer, goal)

        return goal

    def to_multiline(self, signatures, subst, counter):
        exprs = []
        for expr in self._expressions:
            expr_lines, ret_expr = expr.to_multiline(signatures, subst, counter)
            exprs += expr_lines

        exprs.append(ret_expr)
        return Program(self._inputs, exprs)

    def check_fields(self, analyzer, var_to_trans):
        for expr in self._expressions:
            match, trans = expr.check_fields(analyzer, var_to_trans)
            if not match:
                return False, trans

        return True, trans

    def set_type(self, typ):
        self._expressions[-1].set_type(typ)

    @property
    def sizes(self):
        num_endpoints, num_projections, size = 0, 0, 0
        for expr in self._expressions:
            endpoints, projections, sz = expr.sizes()
            num_endpoints += endpoints
            num_projections += projections
            size += sz

        return num_endpoints, num_projections, size

# helper function
def insert_lists(counter, var, arg_typ):
    binds = []
    var_typ = var.type
    
    # if two types match with each other
    if (var_typ is not None and
        arg_typ is not None and
        (
            str(var_typ) == str(arg_typ) or
            var_typ.get_primitive_name() == str(arg_typ) or
            str(var_typ) == arg_typ.get_primitive_name()
        )):
        # print("No binding, real var type", var.type, ", expect arg type", arg_typ)
        return binds, var.var, var.type

    # print("[insert_lists] lifting", var_typ, "into type", arg_typ)
    if isinstance(arg_typ, types.ArrayType):
        let_x = counter.get("x", 0)
        counter["x"] += 1
        bind_typ = types.ArrayType(None, var_typ)
        bind = AssignExpr(f"x{let_x}", ListExpr(var, bind_typ), False)
        subvar = VarExpr(f"x{let_x}", bind_typ)
        inner_binds, x, xt = insert_lists(counter, subvar, arg_typ)
        return ([bind] + inner_binds), x, xt
    else:
        raise Exception("cannot lift a non-array type", var_typ, type(var_typ), arg_typ, type(arg_typ))

def insert_binds(counter, var, arg_typ):
    var_typ = var.type
    
    # if two types match with each other
    if (var_typ is not None and
        arg_typ is not None and
        (
            str(var_typ) == str(arg_typ) or
            var_typ.get_primitive_name() == str(arg_typ) or
            str(var_typ) == arg_typ.get_primitive_name()
        )):
        # print("No binding, real var type", var.type, ", expect arg type", arg_typ)
        return [], var.var, var.type

    # print("[insert_binds] lifting", var_typ, "into type", arg_typ)
    if isinstance(var_typ, types.ArrayType):
        # print("Binding", var, "with type", var.type)
        let_x = counter.get("x", 0)
        counter["x"] += 1
        bind = AssignExpr(f"x{let_x}", var, True)
        subvar = VarExpr(f"x{let_x}", var_typ.item)
        inner_binds, x, xt = insert_binds(counter, subvar, arg_typ)
        return ([bind] + inner_binds), x, xt
    else:
        return insert_lists(counter, var, arg_typ)
