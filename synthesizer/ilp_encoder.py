import re
from snakes.nets import *
import time
import gurobipy as gp
from gurobipy import GRB

from stats.time_stats import TimeStats, STATS_ENCODE, STATS_SEARCH
from synthesizer.utils import group_params, make_entry_name
from synthesizer.underapprox import Approximation

SOLS_PER_SOLVE = 100

# preprocess the spec file and canonicalize the parameters and responses
class ILPetriEncoder:
    def __init__(self, path_entries):
        self._entries = path_entries
        self._net = PetriNet("net")
        self._path_len = 0
        self._approx = Approximation(self._net)

        # ILP stuff
        self._env = gp.Env()
        self._env.setParam('LogToConsole', 0)
        self._env.setParam('PoolSearchMode', 2)
        self._env.setParam('PoolSolutions', SOLS_PER_SOLVE)
        self._model = gp.Model(env=self._env)

        self._cf = None
        self._soln_ix = None
        self._finals = None

        # encode place and transition names into integers
        self._place_names = []
        self._trans_names = []

        # testing
        self._block = []

    @TimeStats(key=STATS_ENCODE)
    def init(self, inputs, outputs):
        self._model.reset()
        self._path_len = 0

        # variables and constraints
        self._add_copy_transitions()

        self._run_approximation(inputs, outputs)

        self._add_initial_vars()
        self._add_initial_constrs(inputs)

    # We don't use solve_all to match the API of the other things.
    @TimeStats(key=STATS_ENCODE)
    def solve_all(self):
        res = []
        self._model.optimize()
        if self._model.status == GRB.OPTIMAL:
            for sol in range(self._model.solCount):
                self._model.setParam(GRB.Param.SolutionNumber, sol)
                res.append(self._get_sol())

        return res

    def get_length_of(self, path_len, inputs, outputs):
        self.init(inputs, outputs)
        while self._path_len < path_len:
            self.increment()
        self.set_final(outputs)

        return self.solve()

    def solve(self):
        # previous run failed; assume everything's been incremented and rerun the solver
        if self._soln_ix is None:
            # run the solver
            self._soln_ix = 0
            self._model.setParam(GRB.Param.SolutionNumber, 0)
            start = time.time()
            self._model.optimize()
            print("running solver | sols:", self._model.solCount, 
                "| len:", self._path_len, 
                "| solve time:", time.time() - start)
        # uncomment for batch/tiled blocking
        # elif self._soln_ix >= SOLS_PER_SOLVE:
        #     # run the solver
        #     self._soln_ix = 0
        #     self._model.setParam(GRB.Param.SolutionNumber, 0)
        #     self._block = []
        #     start = time.time()
        #     self._model.optimize()
        #     print("post-block | sols:", self._model.solCount, "| len:", self._path_len, "| solve time:", time.time() - start)

        if self._model.solCount == 0:
            self._soln_ix = None
            return None

        # if we've explored all available solns, try another pool
        if self._soln_ix >= self._model.solCount:
            self._soln_ix = None
            self.solve()

        # at this point, we know the solver has been run. if we can't find a
        if self._model.status == GRB.OPTIMAL:
            s = self._get_sol()
            self._block.append(self._model.addConstr(
                gp.quicksum(self._fires.sum(x, '*') for x in s) <= len(s) - 1, 
                name='block'))
            transitions = [self._trans_names[t] for t in s]
            return transitions
        else:
            # debug
            # self.computeIIS()
            # self.write("model.ilp")
            self._soln_ix = None
            return None

    # blocking impl:
    def block_prev(self, arg):
        self._soln_ix += 1
        self._model.setParam(GRB.Param.SolutionNumber, self._soln_ix)

    # todo: this hella unperformant lol
    # if we replace this with e.g. pandas table or numpy array + numba,
    # we can get way more perf.
    # (we'd have to introduce the trans_ix table back again but oh well
    # or see model.printAttr/getAttr
    def _get_sol(self):
        # start = time.time()
        res = []
        for i in range(self._path_len):
            for t in range(len(self._trans_names)):
                if self._fires[(t, i)].xn >= 0.0001:
                    res.append(t)
                    continue
        # print("get sol in:", time.time() - start)
        return res

    @TimeStats(key=STATS_ENCODE)
    def increment(self):
        self._path_len += 1
        self._add_variables(self._path_len)
        self._fire_transitions(self._path_len - 1)
        self._reset_finals(self._path_len)

        self._model.remove(self._block)
        self._block = []

    def _run_approximation(self, inputs, output):
        # print("before approximation:", len(self._net.transition()))
        # on top of the input types,
        # we also need to add output types of transitions with no required args
        self._reachables = set()
        input_places = list(inputs.keys())
        null_places = []
        for trans, e in self._entries.items():
            no_required = True
            for p in e.parameters:
                if p.is_required:
                    no_required = False
                    break

            if no_required:
                null_places.append(str(e.response.type.ignore_array()))
                self._reachables.add(trans)

        reachables = self._approx.approx_reachability(
            input_places + null_places, output
        )
        self._reachables = self._reachables.union(reachables)

        for trans in self._net.transition():
            if trans.name not in self._reachables:
                self._net.remove_transition(trans.name)
            else:
                if "projection({'ok': defs_ok_true, 'profile': objs_user_profile}, profile)_" == trans.name:
                    print("!!! Find the desired one!!!")
                self._trans_names.append(trans.name)

        for place in self._net.place():
            self._place_names.append(place.name)

    def _add_variables(self, ck):
        places = range(len(self._place_names))
        for p in places:
            self._tokens[(p, ck)] = self._model.addVar(
                name=f'tokens[{p},{ck}]',
                vtype=GRB.INTEGER)

    def _fire_transitions(self, ck):
        places = range(len(self._place_names)) # self._net.place()
        trans = range(len(self._trans_names)) # self._net.transition()

        # token_map records lower and upper bounds for each token as we iterate
        # through each of the transitions.
        # we only want to impose upper and lower bounds on the token values
        # after we've collected them for all transitions.
        bounds = {}

        # Next, add new vars for firing transitions at the current time.
        for t_idx in trans:
            trans_name = self._trans_names[t_idx]
            t = self._net.transition(trans_name)
            entry = self._entries.get(trans_name)
            # Add var for this transition
            self._fires[(t_idx, ck)] = self._model.addVar(
                name=f'fires[{t_idx},{ck}]',
                vtype=GRB.BINARY)

            # This transition can be fired some non-negative number of times.
            self._model.addConstr(
                self._fires[(t_idx, ck)] >= 0,
                name=f'fires_nonneg[{t_idx},{ck}]')

            tokens = {}
            # Inputs
            inputs = t.input()

            if entry is not None:
                param_map = {}
                for param in entry.parameters:
                    param_str = str(param.type.ignore_array())
                    if param_str not in param_map:
                        param_map[param_str] = []

                    param_map[param_str].append(param)

            for p, _ in inputs:
                # count required and optional arguments
                required = 0
                optional = 0

                if entry is None:
                    required = 1
                else:
                    for param in param_map[p.name]:
                        if param.is_required:
                            required += 1
                        else:
                            optional += 1

                p_idx = self._place_names.index(p.name)
                self._model.addConstr(
                    required * self._fires[(t_idx, ck)] <= \
                        self._tokens[(p_idx, ck)],
                    name='enough_tokens')
                tokens[p.name] = required, optional, 0

            # Outputs
            outputs = t.output()
            # If we have optional outputs, we need to produce more outputs than we
            # consume.
            output_changes = None
            for p, _ in outputs:
                p_idx = self._place_names.index(p.name)
                req_in, opt_in, _ = tokens.get(p.name, (0, 0, 0))
                if len(outputs) > 1: # optional outputs
                    print("!!!goes into this weird constraint")
                    tokens[p.name] = (req_in, opt_in, 1)

                    if re.search(r"filter\(.*, .*\)", t.name):
                        self._model.addConstr(
                            self._tokens[(p_idx, ck + 1)] * \
                            self._fires[(t_idx, ck)] == \
                            self._tokens[(p_idx, ck)] * \
                            self._fires[(t_idx, ck)],
                            name='idk_lol')

                        if output_changes is None:
                            output_changes = self._tokens[(p_idx, ck + 1)]
                        else:
                            output_changes += self._tokens[(p_idx, ck + 1)]
                    else: # FIXME: changes separate for filters and non-filters
                        if output_changes is None:
                            output_changes = self._tokens[(p_idx, ck + 1)] - \
                                self._tokens[(p_idx, ck + 1)]
                        else:
                            output_changes += self._tokens[(p_idx, ck + 1)] - \
                                self._tokens[(p_idx, ck + 1)]
                else: # required outputs
                    if entry is None: # clone transitions
                        tokens[p.name] = (req_in - 2, opt_in, 0)
                    else: # normal transitions
                        tokens[p.name] = (req_in - 1, opt_in, 0)

            if output_changes is not None:
                self._model.addConstr(output_changes >= 1 * \
                    self._fires[(t_idx, ck)],
                    name='output_changes')

            # handle deltas
            for p, (required, opt_in, opt_out) in tokens.items():
                # maximum token bound: cur - required + out_out
                # i.e. max token bound: cur - (required - opt_out)
                # we can't use less than required - optional outs.
                upper = (opt_out - required) * self._fires[(t_idx, ck)]
                # self._model.addConstr(self._tokens[(p, ck + 1)] <= self._tokens[(p, ck)] - (required - opt_out) * self._fires[(t.name, ck)], name='max_next_tok')
                # minimum token bound: cur - required - opt_in
                # i.e. min token bound: cur - (required + opt_in)
                # we can't use more than "required + opt_in" tokens.
                lower = (-opt_in - required) * self._fires[(t_idx, ck)]
                # self._model.addConstr(self._tokens[(p, ck + 1)] >= self._tokens[(p, ck)] - (required + opt_in) * self._fires[(t.name, ck)], name='min_next_tok')
                if p not in bounds:
                    bounds[p] = (lower, upper)
                else:
                    bounds[p] = (bounds[p][0] + lower, bounds[p][1] + upper)

        for p_idx in places:
            pname = self._place_names[p_idx]
            lower, upper = bounds.get(pname, (0, 0))
            # max token bound
            self._model.addConstr(
                self._tokens[(p_idx, ck + 1)] <= self._tokens[(p_idx, ck)] + upper,
                name='max_next_tok')
            # min token bound
            self._model.addConstr(
                self._tokens[(p_idx, ck + 1)] >= self._tokens[(p_idx, ck)] + lower,
                name='min_next_tok')

        # Only one transition fires at each time
        self._model.addConstr(
            self._fires.sum('*', ck) == 1,
            name='one_fires[{ck}]')

    def add_transition(self, trans_name, entry):
        # trans_name = make_entry_name(entry.endpoint, entry.method)
        # if trans_name != make_entry_name(entry.endpoint, entry.method):
        #     raise Exception("name mismatch", trans_name, make_entry_name(entry.endpoint, entry.method))
        # print(trans_name)
        self._entries[trans_name] = entry
        self._net.add_transition(Transition(trans_name))

        params = group_params(entry.parameters)
        for param, token in params.items():
            if not self._net.has_place(param):
                self._net.add_place(Place(param))
            self._net.add_input(param, trans_name, Value(token))

        resp_typ = entry.response.type.ignore_array()
        if isinstance(resp_typ, list):
            for t in resp_typ:
                param = str(t)
                if not self._net.has_place(param):
                    self._net.add_place(Place(param))
                self._net.add_output(param, trans_name, Value(1))
        else:
            param = str(resp_typ)
            if not self._net.has_place(param):
                self._net.add_place(Place(param))
            self._net.add_output(param, trans_name, Value(1))

    def _add_copy_transitions(self):
        places = self._net.place()
        for place in places:
            trans_name = place.name + "_clone"
            self._net.add_transition(Transition(trans_name))
            self._net.add_input(place.name, trans_name, Value(1))
            self._net.add_output(place.name, trans_name, Value(2))

    def _add_initial_vars(self):
        """Create our initial vars."""
        # Where we'll store decision variables for if a transition fires.
        # The number of tokens at time i + 1 is after transitions at time i have been fired.
        self._fires = gp.tupledict()

        # Create variables tracking tokens at each place at each time.
        places = range(len(self._place_names))
        self._tokens = self._model.addVars(
            ((p, 0) for p in places),
            name='tokens',
            vtype=GRB.INTEGER)

    def _add_initial_constrs(self, typs):
        """Create our initial constraints."""
        # We can't have non-negative tokens
        self._model.addConstrs(
            (self._tokens[pi] >= 0 for pi in self._tokens),
            name='tokens_nonneg')

        # Initial marking
        places = range(len(self._place_names))
        self._model.addConstrs(
            (self._tokens[(p, 0)] == typs.get(self._place_names[p], 0) for p in places),
            name='init_marking')

    def _reset_finals(self, t):
        if self._cf:
            self._model.remove(self._cf)

        if self._finals and len(self._finals) >= 0:
            places = range(len(self._place_names))
            self._cf = self._model.addConstrs(
                (self._tokens[(p, t)] == self._finals.get(self._place_names[p], 0) for p in places),
                name='final_marking')

    def set_final(self, typs):
        # Final marking
        # Will be removed and re-added on each increment of ck.
        # Note: if we don't want to care about "void" here, just avoid adding a
        # constraint enforcing the final val of void.
        self._finals = typs
        self._reset_finals(self._path_len)

