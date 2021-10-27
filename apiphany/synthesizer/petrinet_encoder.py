import z3
import re
from z3 import Int, Solver
from snakes.nets import *
import time
import subprocess

from stats.time_stats import TimeStats, STATS_ENCODE, STATS_SEARCH
from synthesizer.utils import group_params, make_entry_name
from synthesizer.underapprox import Approximation
import consts

# preprocess the spec file and canonicalize the parameters and responses
class PetriNetEncoder:
    def __init__(self, path_entries):
        self._entries = path_entries
        self._net = PetriNet("net")
        self._place_to_variable = {}
        self._trans_to_variable = {}
        self._variable_to_trans = []
        self._path_len = 0
        self._solver = Solver()
        # self._solver.set(unsat_core=True)
        self._prev_result = []
        self._approx = Approximation(self._net)
        self._constraints = {
            "permanent": [],
            "temporary": [],
        }
        # self.create_petrinet()

    @TimeStats(key=STATS_ENCODE)
    def init(self, inputs, outputs):
        self._solver.reset()
        self._path_len = 0
        self._prev_result = []

        # variables and constraints
        self._run_approximation(inputs, outputs)
        self._add_variables(self._path_len)
        self._set_initial(inputs)
        self._add_copy_transitions()

    @TimeStats(key=STATS_ENCODE)
    def increment(self):
        start = time.time()
        self._path_len += 1
        self._add_variables(self._path_len)
        self._fire_transitions(self._path_len - 1)
        self._no_transition_fire(self._path_len - 1)
        # print("current len", self._path_len, flush=True)
        # reset the temporary constraint when path length changes
        self._constraints["temporary"] = []
        print("time to add vars and fire transitions:", time.time() - start)

    def _run_approximation(self, inputs, output):
        print("before approximation:", len(self._net.transition()))
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
                null_places.append(str(e.response.type))
                self._reachables.add(trans)

        reachables = self._approx.approx_reachability(
            input_places + null_places, output
        )
        self._reachables = self._reachables.union(reachables)

        for trans in self._net.transition():
            if trans.name not in self._reachables:
                self._net.remove_transition(trans.name)
            else:
                trans_idx = len(self._trans_to_variable)
                self._trans_to_variable[trans.name] = trans_idx
                self._variable_to_trans.append(trans.name)

        projection_cnt = 0
        filter_cnt = 0
        clone_cnt = 0
        for t in self._reachables:
            if "projection" in t:
                projection_cnt += 1
            elif "filter" in t:
                filter_cnt += 1
            elif "clone" in t:
                clone_cnt += 1

        print("after approximation:", len(self._reachables))
        print("projection number", projection_cnt)
        print("filter number", filter_cnt)
        print("clone number", clone_cnt)

    def check_constraints_binding(self):
        # constraints
        for c in self._constraints["permanent"]:
            self._solver.add(c)

        for c in self._constraints["temporary"]:
            self._solver.add(c)

        result = self._solver.check()
        if result == z3.sat:
            result = "sat"
            path = []
            m = self._solver.model()
            for t in range(self._path_len):
                path.append(m[Int(f"t{t}")].as_long())
        else:
            result = "unsat"
            path = None

        return result, path

    def check_constraints_cmd(self):
        query = ""
        for t in range(self._path_len):
            query += f"(declare-fun t{t} () Int) "

        for i in range(len(self._place_to_variable)):
            query += f"(declare-fun k!{i} () Int) "

        # constraints
        for c in self._constraints["permanent"]:
            query += f"(assert {c.sexpr()}) "

        for c in self._constraints["temporary"]:
            query += f"(assert {c.sexpr()}) "
            
        query += "(check-sat) "
        
        # get values
        for t in range(self._path_len):
            query += f"(get-value (t{t})) "

        query += "\n"
        # f.flush()

        try:
            output = subprocess.check_output(["z3", "-in"], input=query.encode())
            results = output.decode('utf-8').split('\n')
            # print(results)
            sat_result = results[0]
            path_results = results[1:]

            # if len(path_results) != self._path_len:
            #     raise Exception("Mismatched path length")
            
            path = []
            for t, r in enumerate(path_results):
                if r:
                    path_idx = re.search(f"\(\(t{t} (\d+)\)\)", r).group(1)
                    path.append(int(path_idx))

            print("found prog")

            return sat_result, path
        except subprocess.CalledProcessError as grepexc:                                                                                                   
            print("error code", grepexc.returncode, grepexc.output)
            print("---")
            return "unsat", None

    @TimeStats(key=STATS_SEARCH)
    def solve(self, mode="cmd"):
        print("adding new prog, len:", self._path_len)
        start = time.time()
        if mode == "cmd":
            result, path = self.check_constraints_cmd()
        else:
            result, path = self.check_constraints_binding()

        print("Check time:", time.time() - start, flush=True)
        start = time.time()
        if self._path_len > 0 and result == "sat":
            results = []
            for tr in path:
                self._prev_result.append(tr)
                results.append(self._variable_to_trans[tr])
            print("Model time:", time.time() - start, flush=True)
            print()
            return results
        else:
            self._targets = []
            results = None

        self._solver.reset()
        return results

    # Blocks the solver from finding the previously found solution again, so that
    # we find new solutions
    def block_prev(self, indices):
        for permutation in indices:
            transitions = [self._prev_result[i] for i in permutation]
            blocks = []
            for i in range(self._path_len):
                blocks.append(Int(f"t{i}") == transitions[i])
            self._constraints["temporary"].append(z3.Not(z3.And(blocks)))

        # print(z3.Not(z3.And(self._prev_result)))
        self._prev_result = []

    def get_length_of(self, path_len, inputs, outputs):
        start = time.time()
        
        self.init(inputs, outputs)
        for _ in range(path_len):
            self.increment()
        self.set_final(outputs)
        # self.add_all_constraints()

        # print("Finish encoding in", time.time() - start, "seconds")
        # print("Searching at len:", self._path_len, flush=True)
        
        start = time.time()
        path = self.solve()
        # result, path = self.check_constraints_cmd()

        # self._solver.add(z3.And(self._targets))
        # with open("constraints.smt", "w") as f:
        #     f.write(self._solver.to_smt2())

        # raise Exception
        
        return path

    def _add_landmarks(self, landmarks):
        for landmark in landmarks:
            idx = self._trans_to_variable.get(landmark)
            fires = [Int(f"t{i}") == idx for i in range(self._path_len)]
            self._constraints["temporary"].append(
                z3.Or(fires)
            )

    def _add_variables(self, t):
        places = self._net.place()
        for place in places:
            key = (place.name, t)
            if key not in self._place_to_variable:
                # if t==0: print(key)
                i = len(self._place_to_variable)
                self._place_to_variable[key] = i
                self._constraints["permanent"].append(Int(i) >= 0)

    def _fire_transitions(self, t):
        transitions = self._net.transition()
        for trans in transitions:
            entry = self._entries.get(trans.name)
            tr_idx = self._trans_to_variable.get(trans.name)

            if self._reachables and trans.name not in self._reachables:
                self._constraints["permanent"].append(
                    z3.Not(Int(f"t{t}") == tr_idx)
                )
                continue

            # precondition: enough tokens in input places
            pre = []
            # postcondition: token number changes
            post = []

            # maps from place name to a triple (required cnts, optional in, optional out)
            tokens = {}
            inputs = trans.input()

            if entry is not None:
                param_map = {}
                for param in entry.parameters:
                    param_str = str(param.type.ignore_array())
                    if param_str not in param_map:
                        param_map[param_str] = []

                    param_map[param_str].append(param)

            for place, _ in inputs:
                place_name = place.name
                # count required and optional arguments
                required = 0
                optional = 0

                if entry is None:
                    required = 1
                else:
                    for param in param_map[place_name]:
                        if param.is_required:
                            required += 1
                        else:
                            optional += 1

                cur = self._place_to_variable.get((place_name, t))
                pre.append(Int(cur) >= required)
                tokens[place_name] = required, optional, 0 # in_req, in_opt, out_opt

            outputs = trans.output()
            output_changes = None
            for place, _ in outputs:
                place_name = place.name
                req_in, opt_in, _ = tokens.get(place_name, (0, 0, 0))
                # output number is always 1 for each type
                if len(outputs) > 1: # optional outputs
                    tokens[place_name] = (req_in, opt_in, 1)
                    cur = self._place_to_variable.get((place_name, t))
                    nxt = self._place_to_variable.get((place_name, t+1))

                    if re.search(r"filter\(.*, .*\)", trans.name):                    
                        # tokens at end > 0 -> nxt = cur
                        # nxt <= cur

                        # if end > 0 (i.e. if fired?): nxt == cur
                        post.append(z3.Implies(Int(nxt) > 0, Int(nxt) == Int(cur)))
                        post.append(Int(nxt) - Int(cur) <= 0)
                        
                        if output_changes is None:
                            output_changes = Int(nxt)
                        else:
                            output_changes += Int(nxt)
                    else: # FIXME: changes separate for filters and non-filters
                        if output_changes is None:
                            output_changes = Int(nxt) - Int(cur)
                        else:
                            output_changes += Int(nxt) - Int(cur)
                else: # required outputs
                    if entry is None:
                        tokens[place_name] = (req_in - 2, opt_in, 0)
                    else:
                        tokens[place_name] = (req_in - 1, opt_in, 0)

            if output_changes is not None:
                post.append(output_changes > 0)

            for place, (required, opt_in, opt_out) in tokens.items():
                cur = self._place_to_variable.get((place, t))
                nxt = self._place_to_variable.get((place, t+1))
                # maximum token bound: cur - required + out_out
                # i.e. max token bound: cur - (required - opt_out)
                # we can't use less than required - optional outs.
                post.append(Int(nxt) <= Int(cur) - required + opt_out)
                # minimum token bound: cur - required - opt_in
                # i.e. min token bound: cur - (required + opt_in)
                # we can't use more than "required + opt_in" tokens.
                post.append(Int(nxt) >= Int(cur) - required - opt_in)

            self._constraints["permanent"].append(
                z3.Implies(Int(f"t{t}") == tr_idx, z3.And(pre + post))
            )

    def _no_transition_fire(self, t):
        places = self._net.place()
        for place in places:
            cur = self._place_to_variable.get((place.name, t))
            nxt = self._place_to_variable.get((place.name, t+1))
            pre = self._net.pre(place.name)
            post = self._net.post(place.name)
            trans_ind = [self._trans_to_variable.get(trans) 
                for trans in pre.union(post)]
            trans_fire = [Int(f"t{t}") == i for i in trans_ind]
            if trans_fire != []:
                self._constraints["permanent"].append(
                    z3.Implies(z3.Not(z3.Or(trans_fire)), Int(cur) == Int(nxt)))

    def _add_copy_transitions(self):
        places = self._net.place()
        for place in places:
            trans_name = consts.PREFIX_CLONE + place.name
            trans_idx = len(self._trans_to_variable)
            self._trans_to_variable[trans_name] = trans_idx
            self._variable_to_trans.append(trans_name)
            self._net.add_transition(Transition(trans_name))
            self._net.add_input(place.name, trans_name, Value(1))
            self._net.add_output(place.name, trans_name, Value(2))

    def _set_initial(self, typs):
        for t, c in typs.items():
            tv = self._place_to_variable.get((t, 0))
            self._constraints["permanent"].append(Int(tv) == c)
            # print(tv)

        for (k, t), v in self._place_to_variable.items():
            if t == 0 and k not in typs:
                self._constraints["permanent"].append(Int(v) == 0)

    def set_final(self, typs):
        for t, c in typs.items():
            tv = self._place_to_variable.get((t, self._path_len))
            self._constraints["temporary"].append(Int(tv) == c)
            # print(tv)

        for (k, t), v in self._place_to_variable.items():
            if t == self._path_len and k not in typs:
                self._constraints["temporary"].append(Int(v) == 0)

        for t in range(self._path_len):
            self._constraints["temporary"].append(
                Int(f"t{t}") >= 0
            )
            self._constraints["temporary"].append(
                Int(f"t{t}") < len(self._trans_to_variable)
            )

    def add_transition(self, trans_name, entry):
        # trans_name = make_entry_name(entry.endpoint, entry.method)
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
