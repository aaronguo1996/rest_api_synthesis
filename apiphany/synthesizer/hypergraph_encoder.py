import z3
import re
from z3 import Bool, Int, Solver
from snakes.nets import *

from stats.time_stats import TimeStats, STATS_ENCODE, STATS_SEARCH
from synthesizer.utils import group_params, make_entry_name

class HyperGraphEncoder:
    def __init__(self, path_entries):
        self._entries = path_entries
        self._place_to_variable = {}
        self._trans_to_variable = {}
        self._variable_to_trans = []
        self._path_len = 0
        self._solver = Solver()
        self._solver.set(unsat_core=True)
        self._targets = []
        self._prev_result = []
        self._net = PetriNet('net')

    @TimeStats(key=STATS_ENCODE)
    def init(self, landmarks, inputs, outputs):
        self._solver.reset()
        self._path_len = 0
        self._targets = []
        self._prev_result = []

        # variables
        self._add_variables(self._path_len)

        # constraints
        self._add_landmarks(landmarks)
        self._set_initial(inputs)
        self._set_final(outputs)
        self._add_landmarks(landmarks)

    @TimeStats(key=STATS_ENCODE)
    def increment(self, landmarks, outputs):
        self._path_len += 1
        self._add_variables(self._path_len)
        self._fire_transitions(self._path_len - 1)
        self._no_transition_fire(self._path_len - 1)
        self._add_landmarks(landmarks)
        self._set_final(outputs)
        print("Current len:", self._path_len, flush=True)

    @TimeStats(key=STATS_SEARCH)
    def solve(self):
        result = self._solver.check(self._targets)
        if self._path_len > 0 and result == z3.sat:
            m = self._solver.model()
            results = []
            for i in range(self._path_len):
                tr = m[Int(f"t{i}")].as_long()
                self._prev_result.append(tr)
                results.append(self._variable_to_trans[tr])
            return results
        else:
            self._targets = []
            return None

    def get_length_of(self, path_len, val_lock, landmarks, inputs, outputs):
        # @path_len@ and @result_queue@ are shared between different processes
        pl = path_len.value
        with val_lock:
            path_len.value += 1

        self.init(landmarks, inputs, outputs)
        for _ in range(pl):
            self.increment(landmarks, outputs)

        return self.solve()

    def block_prev(self, indices):
        for permutation in indices:
            transitions = [self._prev_result[i] for i in permutation]
            blocks = []
            for i in range(self._path_len):
                blocks.append(Int(f"t{i}") == transitions[i])
            self._targets.append(z3.Not(z3.And(blocks)))

        # print(z3.Not(z3.And(self._prev_result)))
        self._prev_result = []

    def _add_landmarks(self, landmarks):
        for landmark in landmarks:
            idx = self._trans_to_variable.get(landmark)
            fires = [Int(f"t{i}") == idx for i in range(self._path_len)]
            self._targets.append(z3.Or(fires))

    def _add_variables(self, t):
        places = self._net.place()
        for place in places:
            key = (place.name, t)
            if key not in self._place_to_variable:
                i = len(self._place_to_variable)
                self._place_to_variable[key] = i

    def _fire_transitions(self, t):
        transitions = self._net.transition()
        for trans in transitions:
            entry = self._entries.get(trans.name)
            tr_idx = self._trans_to_variable.get(trans.name)
            
            pre = []
            post = []

            inputs = trans.input()
            for place, _ in inputs:
                for param in entry.parameters:
                    if param.type.name == place.name and param.is_required:
                        cur = self._place_to_variable.get((place.name, t))
                        pre.append(Bool(cur))

            outputs = trans.output()
            output_vars = []
            for place, _ in outputs:
                cur = self._place_to_variable.get((place.name, t))
                nxt = self._place_to_variable.get((place.name, t+1))
                output_vars.append(Bool(nxt))
                # add dependency constraint
                if re.search(r"filter\(.*, .*\)", trans.name):
                    post.append(z3.Implies(Bool(nxt), Bool(cur)))

            post.append(z3.Or(output_vars))

            

            self._solver.add(
                z3.Implies(Int(f"t{t}") == tr_idx, z3.And(pre + post))
            )

            # lst = ['/users.list:GET', 'projection(/users.list_response, members):', '/users.conversations:GET', 'projection(/users.conversations_response, channels):', 'filter(objs_conversation_9, objs_conversation.name):', 'projection(objs_user_0, profile):', 'projection(objs_user.profile, email):']
            # lst = ['projection(objs_user_profile_3, email):', 'filter(objs_conversation_11, objs_conversation.latest.name):', 'filter(objs_user_profile_3, objs_user_profile.email):',]
            # lst = ['/users.conversations:GET', 'projection(/users.conversations_response, channels):', 'filter(objs_conversation_9, objs_conversation.name):', 'filter(objs_conversation_9, objs_conversation.creator):', 'projection(objs_conversation_9, creator):', '/users.info:GET', 'projection(/users.info_response, user):', 'projection(objs_user_0, profile):', 'projection(objs_user.profile, email):']
            # if trans.name in lst:
            #     print(trans.name)
            #     print(z3.Implies(Int(f"t{t}") == tr_idx, z3.And(pre + post)), flush=True)

    def _no_transition_fire(self, t):
        places = self._net.place()
        for place in places:
            cur = self._place_to_variable.get((place.name, t))
            nxt = self._place_to_variable.get((place.name, t+1))
            pre = self._net.pre(place.name)
            post = self._net.post(place.name)

            trans_ind = []
            for trans in pre.union(post):
                entry = self._entries.get(trans)
                is_opt_in = None
                for param in entry.parameters:
                    if param.type.name == place.name: 
                        if not param.is_required and is_opt_in is None:
                            is_opt_in = True
                        elif param.is_required:
                            is_opt_in = False

                if not is_opt_in:                        
                    trans_ind.append(self._trans_to_variable.get(trans))

            # trans_ind = [self._trans_to_variable.get(trans) 
            #     for trans in pre.union(post)]
            trans_fire = [Int(f"t{t}") == i for i in trans_ind]
            if trans_fire != []:
                self._solver.add(
                    z3.Implies(z3.Not(z3.Or(trans_fire)), Bool(cur) == Bool(nxt))
                )

    def _set_initial(self, typs):
        for t, _ in typs.items():
            tv = self._place_to_variable.get((t, 0))
            self._solver.add(Bool(tv))

        for (k, t), v in self._place_to_variable.items():
            if t == 0 and k not in typs:
                self._solver.add(z3.Not(Bool(v)))

    def _set_final(self, typs):
        for t, _ in typs.items():
            tv = self._place_to_variable.get((t, self._path_len))
            self._targets.append(Bool(tv))

        for (k, t), v in self._place_to_variable.items():
            if t == self._path_len and k not in typs:
                self._targets.append(z3.Not(Bool(v)))

        for t in range(self._path_len):
            self._targets.append(Int(f"t{t}") >= 0)
            self._targets.append(Int(f"t{t}") < len(self._trans_to_variable))

    def _add_transition(self, entry):
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