import z3
from z3 import Int, Solver
from snakes.nets import *
from synthesizer.utils import group_params, make_entry_name
from stats.time_stats import TimeStats, STATS_ENCODE, STATS_SEARCH

# preprocess the spec file and canonicalize the parameters and responses
class Encoder:
    def __init__(self, path_entries):
        self._entries = path_entries
        self._net = PetriNet('net')
        self._place_to_variable = {}
        self._trans_to_variable = {}
        self._variable_to_trans = []
        self._path_len = 0
        self._solver = Solver()
        self._solver.set(unsat_core=True)
        self._targets = []
        self._prev_result = []

        self.create_petrinet()

    @TimeStats(key=STATS_ENCODE)
    def init(self, landmarks, inputs, outputs):
        self._solver.reset()
        self._path_len = 0
        self._targets = []
        self._prev_result = []
        # variables
        # for t in range(self._path_len):
        self._add_variables(self._path_len)

        # constraints
        # for t in range(self._path_len):
        #     self._fire_transitions(t)
        #     self._no_transition_fire(t)
        self._add_landmarks(landmarks)
        self._set_initial(inputs)
        self._set_final(outputs)

    @TimeStats(key=STATS_ENCODE)
    def increment(self, landmarks, outputs):
        self._path_len += 1
        self._add_variables(self._path_len)
        self._fire_transitions(self._path_len - 1)
        self._no_transition_fire(self._path_len - 1)
        self._add_landmarks(landmarks)
        self._set_final(outputs)

        print("Current len:", self._path_len)

    @TimeStats(key=STATS_SEARCH)
    def solve(self):
        # print(self._targets)
        result = self._solver.check(self._targets)
        if self._path_len > 0 and result == z3.sat:
            m = self._solver.model()
            # print(m)
            # print(m[Int(31)]) # 0
            # print(m[Int(37)]) # 0
            # print(m[Int(1007)]) # 1
            # print(m[Int(1983)]) # 0
            # print(m[Int(1013)]) # 0
            # print(m[Int(1989)]) # 1
            results = []
            for i in range(self._path_len):
                tr = m[Int(f"t{i}")].as_long()
                self._prev_result.append(Int(f"t{i}") == tr)
                results.append(self._variable_to_trans[tr])
            return results
        else:
            self._targets = []
            return None

    def block_prev(self):
        self._targets.append(
            z3.Not(z3.And(self._prev_result))
        )
        # print(z3.Not(z3.And(self._prev_result)))
        self._prev_result = []

    def _add_landmarks(self, landmarks):
        for landmark in landmarks:
            idx = self._trans_to_variable.get(landmark)
            fires = [Int(f"t{i}") == idx for i in range(self._path_len)]
            self._targets.append(
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
                self._solver.add(Int(i) >= 0)

    def _fire_transitions(self, t):
        transitions = self._net.transition()
        for trans in transitions:
            entry = self._entries.get(trans.name)
            tr_idx = self._trans_to_variable.get(trans.name)
            
            # precondition: enough tokens in input places
            pre = []
            # postcondition: token number changes
            post = []

            # maps from place name to a triple (required cnts, optional in, optional out)
            tokens = {}
            inputs = trans.input()
            for place, _ in inputs:
                # count required and optional arguments
                required = 0
                optional = 0
                for param in entry.parameters:
                    required += int(str(param.type) == place.name and param.is_required)
                    optional += int(str(param.type) == place.name and not param.is_required)

                cur = self._place_to_variable.get((place.name, t))
                pre.append(Int(cur) >= required)
                tokens[place.name] = (required, optional)

            outputs = trans.output()
            for place, _ in outputs:
                input_req, input_opt = tokens.get(place.name, (0, 0))
                # output number is always 1
                tokens[place.name] = (input_req - 1, input_opt)

            for place, (required, opt_in) in tokens.items():
                cur = self._place_to_variable.get((place, t))
                nxt = self._place_to_variable.get((place, t+1))
                post.append(Int(nxt) <= Int(cur) - required)
                post.append(Int(nxt) >= Int(cur) - required - opt_in)

            self._solver.add(
                z3.Implies(Int(f"t{t}") == tr_idx, z3.And(pre + post)))

            # if trans.name == "projection(objs_conversation, last_read):":
            #     print(trans.name)
            #     print(inputs)
            #     print(outputs)
            #     print(z3.Implies(Int(f"t{t}") == tr_idx, z3.And(pre + post)))

            # if trans.name == "projection(objs_conversation.last_read, user):":
            #     print(trans.name)
            #     print(inputs)
            #     print(outputs)
            #     print(z3.Implies(Int(f"t{t}") == tr_idx, z3.And(pre + post)))

            # if trans.name == "/users.info:GET":
            #     print(trans.name)
            #     print(inputs)
            #     print(outputs)
            #     print(z3.Implies(Int(f"t{t}") == tr_idx, z3.And(pre + post)))

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
                self._solver.add(
                    z3.Implies(z3.Not(z3.Or(trans_fire)), Int(cur) == Int(nxt)))

    def _set_initial(self, typs):
        for t, c in typs.items():
            tv = self._place_to_variable.get((t, 0))
            self._solver.add(Int(tv) == c)
            # print(tv)

        for (k, t), v in self._place_to_variable.items():
            if t == 0 and k not in typs:
                self._solver.add(Int(v) == 0)

    def _set_final(self, typs):
        for t, c in typs.items():
            tv = self._place_to_variable.get((t, self._path_len))
            self._targets.append(Int(tv) == c)
            # print(tv)

        for (k, t), v in self._place_to_variable.items():
            if t == self._path_len and k not in typs:
                self._targets.append(Int(v) == 0)

        for t in range(self._path_len):
            self._targets.append(Int(f"t{t}") >= 0)
            self._targets.append(Int(f"t{t}") < len(self._trans_to_variable))

    def add_transition(self, entry):
        trans_name = make_entry_name(entry.endpoint, entry.method)
        self._entries[trans_name] = entry
        trans_idx = len(self._trans_to_variable)
        self._trans_to_variable[trans_name] = trans_idx
        self._variable_to_trans.append(trans_name)
        self._net.add_transition(Transition(trans_name))

        params = group_params(entry.parameters)
        for param, token in params.items():
            if not self._net.has_place(param):
                self._net.add_place(Place(param))    
            self._net.add_input(param, trans_name, Value(token))

        param = entry.response.type.name
        if not self._net.has_place(param):
            self._net.add_place(Place(param))
        self._net.add_output(param, trans_name, Value(1))

    def create_petrinet(self):
        for entry in self._entries:
            self.add_transition(entry)
            