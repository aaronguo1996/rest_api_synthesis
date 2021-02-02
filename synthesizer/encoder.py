import z3
from z3 import Int, Bool, Solver
from snakes.nets import *

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
        self._targets = []

        self.create_petrinet()

    def init(self, inputs, outputs):
        for t in range(self._path_len):
            self._fire_transitions(t)
            self._no_transition_fire(t)

        self._set_initial(inputs)
        self._set_final(outputs)

    def solve(self):
        result = self._solver.check(self._targets)
        if result == z3.sat:
            m = self._solver.model()
            for i in range(self._path_len):
                tr = m[z3.Int(i)]
                print(self._variable_to_trans[tr])
        else:
            self._path_len += 1
            self._targets = []

    def _fire_transitions(self, t):
        transitions = self._net.transition()
        for trans in transitions:
            tr_idx = self._trans_to_variable(trans.name)
            
            # precondition: enough tokens in input places
            pre = []
            # postcondition: token number changes
            post = []
            inputs = trans.input()
            for place, token in inputs:
                cur = self._place_to_variable.get((place.name, t))
                nxt = self._place_to_variable.get((place.name, t+1))
                pre.append(Int(cur) >= token)
                post.append(Int(nxt) == Int(cur) - token)

            outputs = trans.output()
            for place, token in outputs:
                cur = self._place_to_variable.get((place.name, t))
                nxt = self._place_to_variable.get((place.name, t+1))
                post.append(Int(nxt) == Int(cur) + token)

            self._solver.add(z3.Implies(Int(t) == tr_idx, z3.And(pre + post)))

    def _no_transition_fire(self, t):
        places = self._net.place()
        for place in places:
            cur = self._place_to_variable.get((place.name, t))
            nxt = self._place_to_variable.get((place.name, t+1))
            pre = self._net.pre(place.name)
            trans_ind = [self._trans_to_variable(trans) for trans in pre]
            trans_fire = [Int(t) == i for i in trans_ind]
            self._solver.add(
                z3.Implies(z3.Not(z3.Or(trans_fire)), Int(cur) == Int(nxt)))

    def _set_initial(self, typs):
        for t, c in typs.items():
            tv = self._place_to_variable.get((t, 0))
            self._solver.add(tv == c)

    def _set_final(self, typs):
        for t, c in typs.items():
            tv = self._place_to_variable.get((t, self._path_len))
            self._targets.append(tv == c)

    def add_transition(self, entry):
        self._entries.append(entry)
        trans_name = entry.endpoint + ":" + entry.method
        trans_idx = len(self._trans_to_variable)
        self._trans_to_variable[trans_name] = trans_idx
        self._variable_to_trans[trans_idx] = trans_name
        self._net.add_transition(Transition(trans_name))
        for param in entry.parameters:
            place = str(param.type)
            if place not in self._place_to_variable:
                self._net.add_place(Place(place))
                self._place_to_variable[place] = len(self._place_to_variable)
            self._net.add_input(place, trans_name)

        for param in entry.responses:
            place = str(param.type)
            if place not in self._place_to_variable:
                self._net.add_place(Place(place))
                self._place_to_variable[place] = len(self._place_to_variable)
            self._net.add_output(place, trans_name)

    def create_petrinet(self):
        for entry in self._entries:
            self.add_transition(entry)
            