import re
from snakes.nets import *
import time
import subprocess
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
        self._env.setParam('PoolSearchMode', 1)
        self._env.setParam('PoolSolutions', SOLS_PER_SOLVE)
        self._model = gp.Model(env=self._env)

        self._cf = None
        self._soln_ix = None
        self._finals = None
        # testing
        self._block = []

    @TimeStats(key=STATS_ENCODE)
    def init(self, typs):
        self._model.reset()
        self._path_len = 0

        # variables and constraints
        self._add_copy_transitions()
        self._add_initial_vars()
        self._add_initial_constrs(typs)
        self._run_approximation(typs)
    
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
        self.init(inputs)
        while self._path_len < path_len:
            self.increment()
        self.set_final(outputs)

        return self.solve()

    def solve(self):
        # previous run failed; assume everything's been and incremented rerun the solver
        if self._soln_ix is None:
            # run the solver
            self._soln_ix = 0
            self._model.setParam(GRB.Param.SolutionNumber, 0)
            start = time.time()
            self._model.optimize()
            print("running solver | sols:", self._model.solCount, "| len:", self._path_len, "| solve time:", time.time() - start)
        # uncomment for batch/tiled blocking
        # elif self._soln_ix >= SOLS_PER_SOLVE:
        #     # run the solver
        #     self._soln_ix = 0
        #     self._model.setParam(GRB.Param.SolutionNumber, 0)
        #     self._block = []
        #     start = time.time()
        #     self._model.optimize()
        #     print("post-block | sols:", self._model.solCount, "| len:", self._path_len, "| solve time:", time.time() - start)

        # if we've found all available solns from prev run, give up :(
        if self._soln_ix >= self._model.solCount:
            self._soln_ix = None
            return None

        # at this point, we know the solver has been run. if we can't find a
        if self._model.status == GRB.OPTIMAL:
            s = self._get_sol()
            self._block.append(self._model.addConstr(gp.quicksum(self._fires.sum(x, '*') for x in s) <= len(s) - 1, name='block'))
            return s
        else:
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
            for t in self._net.transition():
                if self._fires[(t.name, i)].xn >= 0.0001:
                    res.append(t.name)
                    continue
        # print("get sol in:", time.time() - start)
        return res

    @TimeStats(key=STATS_ENCODE)
    def increment(self):
        start = time.time()
        self._path_len += 1
        self._add_variables(self._path_len)
        self._fire_transitions(self._path_len - 1)
        self._reset_finals(self._path_len)

        self._model.remove(self._block)
        self._block = []
        # print("time to add vars and fire transitions:", time.time() - start)

    def _run_approximation(self, inputs):
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
                null_places.append(e.response.type.name)
                self._reachables.add(trans)

        reachables = self._approx.approx_reachability(
            input_places + null_places, set(), set()
        )
        self._reachables = self._reachables.union(reachables)
        # print("/users.lookupByEmail_GET" in self._reachables)
        # print("projection(/users.lookupByEmail_GET_response, user)_" in self._reachables)
        # print("projection(objs_user, id)_" in self._reachables)
        # print("/conversations.open_POST" in self._reachables)
        # print("projection(/conversations.open_POST_response, channel)_" in self._reachables)
        # print("projection(objs_conversation, id)_" in self._reachables)
        # print("/chat.postMessage_POST" in self._reachables)
        # print("projection(/chat.postMessage_POST_response, message)_" in self._reachables)
        # print("after approximation:", len(self._reachables))

    def _add_variables(self, ck):
        places = self._net.place()
        for p in places:
            self._tokens[(p.name, ck)] = self._model.addVar(name=f'tokens[{p.name},{ck}]', vtype=GRB.INTEGER)

    def _fire_transitions(self, ck):
        places = self._net.place()
        trans = self._net.transition()

        # token_map records lower and upper bounds for each token as we iterate
        # through each of the transitions.
        # we only want to impose upper and lower bounds on the token values
        # after we've collected them for all transitions.
        bounds = {}
        
        # Next, add new vars for firing transitions at the current time.
        for t in trans:
            entry = self._entries.get(t.name)

            # Add var for this transition
            self._fires[(t.name, ck)] = self._model.addVar(name=f'fires[{t.name},{ck}]', vtype=GRB.BINARY)

            # This transition can be fired some non-negative number of times.
            self._model.addConstr(self._fires[(t.name, ck)] >= 0, name=f'fires_nonneg[{t.name},{ck}]')

            tokens = {}
            # Inputs
            inputs = t.input()
            for p, _ in inputs:
                # count required and optional arguments
                required = 0
                optional = 0

                if entry is None:
                    required = 1
                else:
                    for param in entry.parameters:
                        required += int(str(param.type) == p.name and param.is_required)
                        optional += int(str(param.type) == p.name and not param.is_required)

                self._model.addConstr(required * self._fires[(t.name, ck)] <= self._tokens[(p.name, ck)], name='enough_tokens')
                tokens[p.name] = required, optional, 0

            # Outputs
            outputs = t.output()
            # If we have optional outputs, we need to produce more outputs than we
            # consume.
            output_changes = None
            for p, _ in outputs:
                req_in, opt_in, _ = tokens.get(p.name, (0, 0, 0))
                # output number is always 1 for each type
                if len(outputs) > 1: # optional outputs
                    tokens[p.name] = (req_in, opt_in, 1)

                    if re.search(r"filter\(.*, .*\)", t.name):
                        self._model.addConstr(self._tokens[(p.name, ck + 1)] * self._fires[(t.name, ck)] == self._tokens[(p.name, ck)] * self._fires[(t.name, ck)], name='idk_lol')
                        
                        if output_changes is None:
                            output_changes = self._tokens[(p.name, ck + 1)]
                        else:
                            output_changes += self._tokens[(p.name, ck + 1)]
                    else: # FIXME: changes separate for filters and non-filters
                        if output_changes is None:
                            output_changes = self._tokens[(p.name, ck + 1)] - self._tokens[(p.name, ck + 1)]
                        else:
                            output_changes += self._tokens[(p.name, ck + 1)] - self._tokens[(p.name, ck + 1)]
                else: # required outputs
                    if entry is None:
                        tokens[p.name] = (req_in - 2, opt_in, 0)
                    else:
                        tokens[p.name] = (req_in - 1, opt_in, 0)

            if output_changes is not None:
                self._model.addConstr(output_changes >= 1 * self._fires[(t.name, ck)], name='output_changes')

            # handle deltas
            for p, (required, opt_in, opt_out) in tokens.items():
                # maximum token bound: cur - required + out_out
                # i.e. max token bound: cur - (required - opt_out)
                # we can't use less than required - optional outs.
                upper = (opt_out - required) * self._fires[(t.name, ck)]
                # self._model.addConstr(self._tokens[(p, ck + 1)] <= self._tokens[(p, ck)] - (required - opt_out) * self._fires[(t.name, ck)], name='max_next_tok')
                # minimum token bound: cur - required - opt_in
                # i.e. min token bound: cur - (required + opt_in)
                # we can't use more than "required + opt_in" tokens.
                lower = (-opt_in - required) * self._fires[(t.name, ck)]
                # self._model.addConstr(self._tokens[(p, ck + 1)] >= self._tokens[(p, ck)] - (required + opt_in) * self._fires[(t.name, ck)], name='min_next_tok')
                if p not in bounds:
                    bounds[p] = (lower, upper)
                else:
                    bounds[p] = (bounds[p][0] + lower, bounds[p][1] + upper)

        # todo
        # some transitions can just spontaneously create things from nothing - they
        # take only optional arguments
        # which means they will always fire
        # add bounds for deltas
        for p in places:
            p = p.name
            lower, upper = bounds.get(p, (0, 0))
            # max token bound
            self._model.addConstr(self._tokens[(p, ck + 1)] <= self._tokens[(p, ck)] + upper, name='max_next_tok')
            # min token bound
            self._model.addConstr(self._tokens[(p, ck + 1)] >= self._tokens[(p, ck)] + lower, name='min_next_tok')

        # Only one transition fires at each time
        self._model.addConstr(self._fires.sum('*', ck) == 1, name='one_fires[{ck}]')

    def _add_transition(self, entry):
        trans_name = make_entry_name(entry.endpoint, entry.method)
        # print(trans_name)
        self._entries[trans_name] = entry
        self._net.add_transition(Transition(trans_name))

        params = group_params(entry.parameters)
        for param, token in params.items():
            if not self._net.has_place(param):
                self._net.add_place(Place(param))    
            self._net.add_input(param, trans_name, Value(token))

        resp_typ = entry.response.type
        if isinstance(resp_typ, list):
            for t in resp_typ:
                param = t.name
                if not self._net.has_place(param):
                    self._net.add_place(Place(param))
                self._net.add_output(param, trans_name, Value(1))
        else:
            param = entry.response.type.name
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
        places = [x.name for x in self._net.place()]
        self._tokens = self._model.addVars(((p, 0) for p in places), name='tokens', vtype=GRB.INTEGER)

    def _add_initial_constrs(self, typs):
        """Create our initial constraints."""
        # We can't have non-negative tokens
        self._model.addConstrs((self._tokens[pi] >= 0 for pi in self._tokens), name='tokens_nonneg')

        # Initial marking
        places = [x.name for x in self._net.place()]
        self._model.addConstrs((self._tokens[(p, 0)] == typs.get(p, 0) for p in places), name='init_marking')

    def _reset_finals(self, t):
        if self._cf:
            self._model.remove(self._cf)

        if self._finals and len(self._finals) >= 0:
            places = [p.name for p in self._net.place()]
            self._cf = self._model.addConstrs((self._tokens[(p, t)] == self._finals.get(p, 0) for p in places), name='final_marking')

    def set_final(self, typs):
        # Final marking
        # Will be removed and re-added on each increment of ck.
        # Note: if we don't want to care about "void" here, just avoid adding a
        # constraint enforcing the final val of void.
        self._finals = typs
        self._reset_finals(self._path_len)

