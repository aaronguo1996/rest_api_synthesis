import re
from itertools import chain

from analyzer.multiplicity import MUL_ONE_ONE, MUL_ZERO_MORE, MUL_ZERO_ONE
from analyzer.dynamic import Goal

SPACE = '    '

class Expression:
    def __init__(self, typ):
        self.type = typ

    def __repr__(self):
        return self.__str__()

    def apply_subst(self):
        raise NotImplementedError

    def pretty_with_type(self):
        return f"{self}: {self.type}"

    def set_type(self, typ):
        self.type = typ

    def pretty(self, hang):
        return f"{SPACE * hang}" + self.__str__()

    def collect_exprs(self):
        raise NotImplementedError

class AppExpr(Expression):
    def __init__(self, fun, args, typ=None):
        super().__init__(typ)
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
        return AppExpr(self._fun, args, self.type)

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

    def execute(self, analyzer):
        args = [arg.execute(analyzer) for _, arg in self._args]
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
            return None, 0
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

    def to_multiline(self, counter):
        args = []
        exprs = []
        for name, arg in self._args:
            arg_exprs, arg_expr = arg.to_multiline(counter)
            args.append((name, arg_expr))
            exprs.extend(arg_exprs)

        app_expr = AppExpr(self._fun, args, self.type)

        let_x = counter.get("x", 0)
        counter["x"] += 1
        let_var = VarExpr(f"x{let_x}", self.type)
        let_expr = AssignExpr(f"x{let_x}", app_expr)
        exprs.append(let_expr)
        return exprs, let_var

    def check_fields(self, analyzer, var_to_trans):
        for _, arg in self._args:
            match, _ = arg.check_fields(analyzer, var_to_trans)
            if not match:
                return False, self._fun

        return True, self._fun

    def pretty(self, hang):
        return self.__str__()

class VarExpr(Expression):
    def __init__(self, x, typ=None):
        super().__init__(typ)
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
        ret = subst.get(self._var, self)
        ret.type = self.type
        # propagate type into each return statement of Map
        if isinstance(ret, MapExpr):
            ret._prog.assign_type(self.type)

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

    def execute(self, analyzer):
        val = analyzer.lookup_var(self._var)
        if val is None:
            return None, 0
        else:
            # print("[Var] get back", val, "for", self._var)
            return val, 1

    def get_multiplicity(self, analyzer):
        var_mul = analyzer.lookup_var(self._var)
        print("[Var]", self._var, analyzer.pretty(var_mul[1]))
        return var_mul

    def to_program_graph(self, graph, var_to_trans):
        return var_to_trans.get(self._var)

    def goal_search(self, analyzer, goal):
        analyzer.push_var(self._var, goal)

    def to_multiline(self, counter):
        return [], self

    def check_fields(self, analyzer, var_to_trans):
        return True, var_to_trans.get(self._var)

    def pretty(self, hang):
        return self.__str__()

class ProjectionExpr(Expression):
    def __init__(self, obj, field, typ=None):
        super().__init__(typ)
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
        # return AppExpr(
        #     "projection",
        #     [
        #         ("obj", self._obj.apply_subst(subst)),
        #         ("field", VarExpr("@@" + self._field)),
        #     ],
        #     self.type
        # )
        return ProjectionExpr(
            self._obj.apply_subst(subst),
            self._field,
            self.type,
        )

    def collect_exprs(self):
        res = [self] ++ self._obj.collect_exprs()

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

    def execute(self, analyzer):
        val, score = self._obj.execute(analyzer)
        if val is not None and self._field in val:
            val = val.get(self._field)
            # print("[Projection] get back", val, "for", self._field)
            return val, score + 1
        else:
            return None, 0

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

    def to_multiline(self, counter):
        exprs, obj_expr = self._obj.to_multiline(counter)
        # print(self, self.type)
        proj_expr = ProjectionExpr(obj_expr, self._field, self.type)
        return exprs, proj_expr

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

class FilterExpr(Expression):
    def __init__(self, obj, field, val, is_val_list, typ=None):
        super().__init__(typ)
        self._obj = obj
        self._field = field
        self._val = val
        self._is_val_list = is_val_list

    def __str__(self):
        if self._is_val_list:
            return f"{self._obj}.filter(x => x.{self._field} in {self._val})"
        else:
            return f"{self._obj}.filter(x => x.{self._field} == {self._val})"

    def __eq__(self, other):
        if not isinstance(other, FilterExpr):
            return NotImplemented

        return (
            self._obj == other._obj and
            self._field == other._field and
            self._val == other._val
        )

    def apply_subst(self, subst):
        # return AppExpr(
        #     "filter",
        #     [
        #         ("obj1", self._obj.apply_subst(subst)),
        #         ("field", VarExpr("@@" + self._field)),
        #         ("obj2", self._val.apply_subst(subst)),
        #     ],
        #     self.type
        # )
        return FilterExpr(
            self._obj.apply_subst(subst),
            self._field,
            self._val.apply_subst(subst),
            self._is_val_list,
            self.type,
        )

    def collect_exprs(self):
        res = [self] ++ self._obj.collect_exprs()
        # if self._is_val_list:
        #     return res ++ chain(*[x.collect_exprs() for x in self._val])
        # else:
        #     return res ++ self._val.collect_exprs()
        return res ++ self._val.collect_exprs()

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

    def execute(self, analyzer):
        obj, score1 = self._obj.execute(analyzer)
        val, score2 = self._val.execute(analyzer)
        
        if obj is None or val is None or not isinstance(obj, list):
            return None, 0

        paths = self._field.split('.')
        # print("[Filter] filtering by path", paths)
        result = []
        for o in obj:
            tmp = o
            for p in paths:
                if p in tmp:
                    tmp = tmp.get(p)
                    # print("[Filter] get field", p, "returns", tmp)
                else:
                    tmp = None
                    # print("[Filter] cannot find field", p, "in", tmp)
                    break
            
            if tmp == val:
                result.append(o)

        # print("[Filter] get back", result, "for", self._field)
        return result, score1 + score2

    def get_multiplicity(self, analyzer):
        obj_mul = self._obj.get_multiplicity(analyzer)
        obj_typ = self._obj.type.name
        val_mul = self._val.get_multiplicity(analyzer)
        filter_field = obj_typ + "." + self._field
        if (filter_field in analyzer._unique_fields and 
            val_mul[1] is not MUL_ZERO_MORE):
            print("[Filter]", filter_field, "is found in the analysis result")
            return obj_mul[0], MUL_ZERO_ONE
        else:
            print("[Filter]", filter_field, "is not in the analysis result")
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

    def to_multiline(self, counter):
        obj_exprs, obj_expr = self._obj.to_multiline(counter)
        val_exprs, val_expr = self._val.to_multiline(counter)
        exprs = obj_exprs + val_exprs
        filter_expr = FilterExpr(
            obj_expr, self._field, 
            val_expr, self._is_val_list, self.type
        )

        let_x = counter.get("x", 0)
        counter["x"] += 1
        let_var = VarExpr(f"x{let_x}", self.type)
        let_expr = AssignExpr(f"x{let_x}", filter_expr)
        exprs.append(let_expr)
        return exprs, let_var

    def check_fields(self, analyzer, var_to_trans):
        print("Checking field", self._field, "for object", self._obj.type)
        match, trans = self._obj.check_fields(analyzer, var_to_trans)
        if match:
            match, _ = self._val.check_fields(analyzer, var_to_trans)

        if match:
            match = analyzer.check_type_fields(
                self._obj.type.name, trans, self._field
            )

        print("check result:", match)
        return match, trans

    def pretty(self, hang):
        return self.__str__()

class MapExpr(Expression):
    def __init__(self, obj, prog, typ=None):
        super().__init__(typ)
        self._obj = obj
        self._prog = prog

    def __str__(self):
        return f"{self._obj}.map({self._prog})"

    def __eq__(self, other):
        if not isinstance(other, MapExpr):
            return NotImplemented

        return (
            self._obj == other._obj and
            self._prog == other._prog
        )

    def apply_subst(self, subst):
        # print(self._prog._inputs)
        # print(type(self._prog._inputs[0]))
        # expr = self._prog.to_expression({self._prog._inputs[0]: self._obj})
        # return expr.apply_subst(subst)
        # f = self._prog.to_expression(subst)
        # f.type = self.type
        # return AppExpr(
        #     "map",
        #     [
        #         ("obj", self._obj.apply_subst(subst)),
        #         ("f", f),
        #     ],
        # )
        return MapExpr(
            self._obj.apply_subst(subst),
            self._prog.apply_subst(subst),
            self.type,
        )

    def collect_exprs(self):
        return [self] ++ self._obj.collect_exprs() ++ self._prog.collect_exprs()

    def body(self):
        expr = self._prog.to_expression({self._prog._inputs[0]: self._obj})
        return expr

    def to_graph(self, graph):
        # print(self)
        # n1 = self._obj.to_graph(dot)
        expr = self.body()
        # expr.type = self.type
        n2 = expr.to_graph(graph)
        # return [n1, n2]
        # raise NotImplementedError
        return n2

    def get_vars(self):
        obj_vars = self._obj.get_vars()
        prog_vars = self._prog.get_vars()
        return obj_vars.union(prog_vars)

    def taint_var(self, taint):
        obj_vars = self._obj.get_vars()
        exprs = self._prog.reachable_expressions(taint)
        expr_vars = [e.get_vars() for e in exprs]
        return obj_vars.union(*expr_vars)

    def execute(self, analyzer):
        obj, obj_score = self._obj.execute(analyzer)
        if obj is None:
            return None, 0

        scores = 0
        results = []
        x = self._prog._inputs[0]
        for o in obj:
            analyzer.push_var(x, o)
            prog, prog_score = self._prog.execute(analyzer)
            analyzer.pop_var(x)
            scores += prog_score
            # do not add None to the results, ensure the following operations can be applied
            if prog is not None:
                results.append(prog)

        # print("get back", results, "for Map")
        return results, (obj_score + scores / len(obj) if obj else obj_score)

    def get_multiplicity(self, analyzer):
        obj_mul = self._obj.get_multiplicity(analyzer)
        x = self._prog._inputs[0]
        x_mul = obj_mul[0] - 1, MUL_ONE_ONE
        analyzer.push_var(x, x_mul)
        prog_mul = self._prog.get_multiplicity(analyzer)
        print("[Map]", analyzer.pretty(prog_mul[1]))
        if obj_mul[1] == MUL_ZERO_MORE:
            return obj_mul[0], MUL_ZERO_MORE
        else:
            return obj_mul[0], prog_mul[1]

    def to_program_graph(self, graph, var_to_trans):
        obj_trans = self._obj.to_program_graph(graph, var_to_trans)
        if obj_trans is not None:
            x = self._prog._inputs[0]
            var_to_trans[x] = obj_trans
        return self._prog.to_program_graph(graph, var_to_trans)

    def goal_search(self, analyzer, goal):
        raise NotImplementedError

    def to_multiline(self, counter):
        exprs, obj_expr = self._obj.to_multiline(counter)
        map_body = self._prog.to_multiline(counter)
        map_expr = MapExpr(obj_expr, map_body, self.type)
        
        let_x = counter.get("x", 0)
        counter["x"] += 1
        let_var = VarExpr(f"x{let_x}", self.type)
        let_expr = AssignExpr(f"x{let_x}", map_expr)
        exprs.append(let_expr)
        return exprs, let_var

    def check_fields(self, analyzer, var_to_trans):
        match, trans = self._obj.check_fields(analyzer, var_to_trans)
        if match:
            x = self._prog._inputs[0]
            var_to_trans[x] = trans
            match, trans = self._prog.check_fields(analyzer, var_to_trans)
        return match, trans

    def set_type(self, typ):
        self.type = typ
        self._prog.set_type(typ)

    def pretty(self, hang):
        # print("calling from MapExpr")
        return (
            f"{self._obj}.map("
            f"{self._prog.pretty(hang)})"
        )

class AssignExpr(Expression):
    def __init__(self, x, expr):
        super().__init__(None)
        self._lhs = x
        self._rhs = expr

    def __str__(self):
        return f"{self._lhs} <- {self._rhs}"

    def __eq__(self, other):
        if not isinstance(other, AssignExpr):
            return NotImplemented

        return (
            self._lhs == other._lhs and
            self._rhs == other._rhs
        )

    @property
    def var(self):
        return self._lhs

    @property
    def expr(self):
        return self._rhs

    def taint_var(self, taint):
        if isinstance(self._rhs, MapExpr):
            rhs_vars = self._rhs.taint_var(taint)
        else:
            rhs_vars = self._rhs.get_vars()
        rhs_reachable_vars = [taint.get(v, set()) for v in rhs_vars]
        reachable_vars = set().union(*rhs_reachable_vars)
        curr_reachable = taint.get(self._lhs, set())
        taint[self._lhs] = curr_reachable.union(rhs_vars, reachable_vars)

    def apply_subst(self, subst):
        return AssignExpr(
            self._lhs,
            self._rhs.apply_subst(subst),
        )

    def collect_exprs(self):
        return [self] ++ self._rhs.collect_exprs()

    def to_graph(self, graph):
        # print(self)
        return self._rhs.to_graph(graph)

    def get_vars(self):
        rhs_vars = self._rhs.get_vars()
        rhs_vars.add(self._lhs)
        return rhs_vars

    def execute(self, analyzer):
        val, score = self._rhs.execute(analyzer)
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

    def to_multiline(self, counter):
        exprs, rhs = self._rhs.to_multiline(counter)
        exprs.append(AssignExpr(self._lhs, rhs))
        return exprs, VarExpr(self._lhs, rhs.type), counter

    def check_fields(self, analyzer, var_to_trans):
        match, trans = self._rhs.check_fields(analyzer, var_to_trans)
        if match:
            var_to_trans[self.var] = trans

        return match, trans

    def pretty(self, hang):
        return f"{SPACE * hang}let {self._lhs} = {self._rhs.pretty(hang)} in"

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
            f"\\{' '.join(self._inputs)} -> {{"
            f"{' '.join(expr_strs)}"
            f" return {self._expressions[-1]}}}"
        )

    def __eq__(self, other):
        if not isinstance(other, Program):
            return NotImplemented

        if self._inputs == other._inputs:
            return self.to_expression({}) == other.to_expression({})
        elif len(self._inputs) == len(other._inputs):
            subst = {}
            for i, x in enumerate(other._inputs):
                subst[x] = VarExpr(self._inputs[i])
            other = other.apply_subst(subst)
            return self.to_expression({}) == other.to_expression({})
        else:
            return False

    def __hash__(self):
        return hash((tuple(self._inputs), str(self.to_expression({}))))

    def __repr__(self):
        return self.__str__()

    def to_expression(self, subst={}):
        for expr in self._expressions:
            # eagerly substitute the previous variables into the new expression
            # print(expr)
            expr = expr.apply_subst(subst)
            if isinstance(expr, AssignExpr):
                # expr.expr.type = expr.type
                if isinstance(expr.expr, MapExpr):
                    subst[expr.var] = expr.expr.body()
                else:
                    subst[expr.var] = expr.expr

        return expr

    def apply_subst(self, subst={}):
        exprs = []
        for expr in self._expressions:
            expr = expr.apply_subst(subst)
            exprs.append(expr)

        return Program(self._inputs, exprs)

    def collect_exprs(self):
        expr = self.to_expression({})
        return expr.collect_exprs()

    def get_vars(self):
        all_vars = set()
        for expr in self._expressions:
            all_vars.union(expr.get_vars())

        return all_vars

    def reachable_expressions(self, taint={}):
        # print(self)
        for expr in self._expressions:
            if isinstance(expr, AssignExpr):
                expr.taint_var(taint)

        # print(taint)
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

    def merge_maps(self):
        maps = {}
        mark_delete = set()
        for expr in self._expressions:
            if isinstance(expr, AssignExpr) and isinstance(expr._rhs, MapExpr):
                var_obj = expr._rhs._obj
                map_body = expr._rhs._prog
                if (isinstance(var_obj, VarExpr) and var_obj._var in maps):
                    rhs = maps[var_obj._var]
                    # modify the last expression into let
                    last_expr = AssignExpr(
                        map_body._inputs[0],
                        rhs._prog._expressions[-1]
                    )
                    expr._rhs._obj = rhs._obj
                    expr._rhs._prog = rhs._prog
                    expr._rhs._prog._expressions = (
                        rhs._prog._expressions[:-1] + 
                        [last_expr] + 
                        map_body._expressions
                    )
                    mark_delete.add(var_obj._var)

                maps[expr.var] = expr._rhs

        # print("Before filtering", self._expressions)
        self._expressions = [e for e in self._expressions
            if not isinstance(e, AssignExpr) or e.var not in mark_delete
        ]
        # print("After filtering", self._expressions)

    def merge_projections(self, subst={}):
        mark_delete = set()
        exprs = []
        for expr in self._expressions:
            before_vars = expr.get_vars()
            expr = expr.apply_subst(subst)
            after_vars = expr.get_vars()
            # print("before", before_vars, "after", after_vars)
            mark_delete = mark_delete.union(before_vars.difference(after_vars))
            if isinstance(expr, AssignExpr): 
                if isinstance(expr._rhs, ProjectionExpr):
                    subst[expr.var] = expr._rhs
                elif isinstance(expr._rhs, MapExpr):
                    # print("find a map expression")
                    # print("map expressions", expr._rhs._prog._expressions)
                    expr._rhs._prog.merge_projections(subst)
                    expr._rhs._prog.simplify()
                    # print("after map expressions", expr._rhs._prog._expressions)

            exprs.append(expr)

        # print("delete", mark_delete)
        self._expressions = [e for e in exprs
            if not isinstance(e, AssignExpr) or e.var not in mark_delete
        ]

    def merge_direct_eqs(self, subst={}):
        mark_delete = set()
        exprs = []
        for expr in self._expressions:
            expr = expr.apply_subst(subst)
            if isinstance(expr, AssignExpr):
                if isinstance(expr.expr, VarExpr):
                    subst[expr.var] = expr.expr
                    mark_delete.add(expr.var)
                elif isinstance(expr.expr, MapExpr):
                    expr.expr._prog.merge_direct_eqs(subst)

            exprs.append(expr)

        self._expressions = [e for e in exprs
            if not isinstance(e, AssignExpr) or e.var not in mark_delete
        ]

    def simplify(self):
        old_expressions = None
        while old_expressions != self._expressions:
            old_expressions = self._expressions.copy()
            self.merge_direct_eqs(subst={})
            # print("after merge direct eq", self.pretty())
            self.merge_maps()
            # print("after merge maps", self.pretty())
            self.merge_projections(subst={})
            # print("after merge projections", self.pretty())

    def assign_type(self, t):
        self._expressions[-1].type = t
        if (len(self._expressions) > 1 and 
            isinstance(self._expressions[-2], MapExpr)):
            expr = self._expressions[-2]
            expr._prog.assign_type(t)

    def execute(self, analyzer):
        scores = 0
        for expr in self._expressions[:-1]:
            s = expr.execute(analyzer)
            if s is None:
                return None, 0

            scores += s

        ret, score = self._expressions[-1].execute(analyzer)
        return ret, (scores + score) / len(self._expressions) # normalize by number of expressions

    def get_multiplicity(self, analyzer):
        for expr in self._expressions[:-1]:
            expr.get_multiplicity(analyzer)

        return self._expressions[-1].get_multiplicity(analyzer)

    def pretty(self, hang=0):
        indent = SPACE * (hang + 1)
        newline = '\n'
        expr_strs = [expr.pretty(hang + 1) + newline for expr in self._expressions]
        
        return (
            f"(\\', '.join(self._inputs)) -> {{{newline}"
            f"{''.join(expr_strs[:-1])}"
            f"{indent}return {expr_strs[-1][:-1]}{newline}"
            f"{SPACE * hang}}}"
        )

    def to_program_graph(self, graph=ProgramGraph(), var_to_trans={}):
        for expr in self._expressions:
            if isinstance(expr, AssignExpr):
                v = expr.var
                trans = expr.expr.to_program_graph(graph, var_to_trans)
                var_to_trans[v] = trans
        
        # the last expression in the list
        return expr.to_program_graph(graph, var_to_trans)

    def remove_map(self):
        exprs = []
        for expr in self._expressions:
            if isinstance(expr, AssignExpr):
                rhs = expr.expr
                v = expr.var
                if isinstance(rhs, MapExpr):
                    prog = rhs._prog.remove_map()
                    x = prog._inputs[0]
                    prog = prog.apply_subst({x: rhs._obj})
                    exprs += prog._expressions[:-1]
                    exprs.append(AssignExpr(v, prog._expressions[-1]))
                    continue

            exprs.append(expr)

        return Program(self._inputs, exprs)

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

    def to_multiline(self, counter):
        exprs = []
        for expr in self._expressions:
            expr_lines, ret_expr = expr.to_multiline(counter)
            exprs += expr_lines

        exprs.append(ret_expr)
        # exprs.append(VarExpr("x"+str(counter-1), exprs[-1].type))
        return Program(self._inputs, exprs)

    def check_fields(self, analyzer, var_to_trans):
        # print("calling check fields for programs")
        for expr in self._expressions:
            # print("checking fields in", expr)
            match, trans = expr.check_fields(analyzer, var_to_trans)
            if not match:
                return False, trans

        return True, trans

    def set_type(self, typ):
        self._expressions[-1].set_type(typ)
