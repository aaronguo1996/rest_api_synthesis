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

    def pretty(self, hang):
        return f"{SPACE * hang}" + self.__str__()

class AppExpr(Expression):
    def __init__(self, fun, args, typ=None):
        super().__init__(typ)
        self._fun = fun
        self._args = args

    def __str__(self):
        arg_strs = [f"{x}={arg}" for x, arg in self._args]
        return f"{self._fun}({','.join(arg_strs)})"

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

    def to_graph(self, graph):
        # print(self)
        if self.type:
            v = self.type.name
            graph.add_node(v)
            return v

    def get_vars(self):
        return set([self._var])

    def pretty(self, hang):
        return self.__str__()

class AssignExpr(Expression):
    def __init__(self, x, expr):
        super().__init__(None)
        self._lhs = x
        self._rhs = expr

    def __str__(self):
        return f"let {self._lhs} = {self._rhs};"

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

    def to_graph(self, graph):
        # print(self)
        return self._rhs.to_graph(graph)

    def get_vars(self):
        rhs_vars = self._rhs.get_vars()
        rhs_vars.add(self._lhs)
        return rhs_vars

    def pretty(self, hang):
        return f"{SPACE * hang}let {self._lhs} = {self._rhs.pretty(hang)};"

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

    def pretty(self, hang):
        # print("calling from MapExpr")
        return (
            f"{self._obj}.map("
            f"{self._prog.pretty(hang)})"
        )

class Program:
    def __init__(self, inputs, expressions):
        self._inputs = inputs
        self._expressions = expressions

    def __str__(self):
        expr_strs = [str(expr) + '    \n' for expr in self._expressions[:-1]]
        return (
            f"({','.join(self._inputs)}) => {{"
            f"{' '.join(expr_strs)}"
            f" return {self._expressions[-1]};}}"
        )

    def __eq__(self, other):
        if not isinstance(other, Program):
            return NotImplemented

        return (
            self.to_expression({}) == other.to_expression({}) and
            self._inputs == other._inputs
        )

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

    def get_vars(self):
        all_vars = set()
        for expr in self._expressions:
            all_vars.union(expr.get_vars())

        return all_vars

    def reachable_expressions(self):
        # print(self)
        taint = {}
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
                    # print("after map expressions", expr._rhs._prog._expressions)

            exprs.append(expr)

        # print("delete", mark_delete)
        self._expressions = [e for e in exprs
            if not isinstance(e, AssignExpr) or e.var not in mark_delete
        ]

    def assign_type(self, t):
        self._expressions[-1].type = t
        if (len(self._expressions) > 1 and 
            isinstance(self._expressions[-2], MapExpr)):
            expr = self._expressions[-2]
            expr._prog.assign_type(t)

    def pretty(self, hang):
        indent = SPACE * (hang + 1)
        newline = '\n'
        expr_strs = [expr.pretty(hang + 1) + newline for expr in self._expressions]
        
        return (
            f"({','.join(self._inputs)}) => {{{newline}"
            f"{''.join(expr_strs[:-1])}"
            f"{indent}return {expr_strs[-1][:-1]};{newline}"
            f"{SPACE * hang}}}"
        )
