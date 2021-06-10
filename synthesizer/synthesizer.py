from collections import defaultdict
import itertools
import pickle
import time
import os

from program.generator import ProgramGenerator
from program.program import ProgramGraph, all_topological_sorts
from stats.time_stats import TimeStats, STATS_GRAPH
from synthesizer.hypergraph_encoder import HyperGraphEncoder
from synthesizer.petrinet_encoder import PetriNetEncoder
from synthesizer.ilp_encoder import ILPetriEncoder
import consts


class Synthesizer:
    def __init__(self, config, entries, exp_dir):
        self._config = config
        self._groups = {}
        self._group_names = {}
        self._landmarks = []
        self._unique_entries = {}
        self._entries = entries
        self._program_generator = ProgramGenerator({})
        # flags
        self._expand_group = config[consts.KEY_SYNTHESIS][consts.KEY_EXPAND_GROUP]
        self._block_perms = config[consts.KEY_SYNTHESIS][consts.KEY_BLOCK_PERM]
        self._exp_dir = exp_dir

    @TimeStats(key=STATS_GRAPH)
    def init(self):
        TimeStats.reset()
        self._add_transitions()

    def run(self, landmarks, inputs, outputs):
        results = self.run_n(landmarks, inputs, outputs, 1)
        return results[0]

    def _write_solution(self, idx, t, p):
        result_path = os.path.join(self._exp_dir, f"results_{idx}.txt")
        with open(result_path, "a+") as f:
            f.write(f"time: {t: .2f}")
            f.write("\n")
            f.write(f"time breakdown:\n{TimeStats._timing}\n")
            f.write(str(p))
            f.write("\n")
            f.write(p.pretty(0))
            f.write("\n")

    def _serialize_solutions(self, idx, progs):
        solution_path = os.path.join(self._exp_dir, f"solutions_{idx}.pkl")
        if os.path.exists(solution_path):
            with open(solution_path, "rb") as f:
                solutions = pickle.load(f)
        else:
            solutions = []

        solutions += progs
        with open(solution_path, "wb") as f:
            pickle.dump(solutions, f)

    def _expand_groups(self, result):
        groups = []
        for name in result:
            if "_clone" in name:
                continue

            if self._expand_group:
                e = self._entries.get(name)
                if e is None:
                    raise Exception("Unknown transition", name)

                param_typs = [str(p.type) for p in e.parameters]
                if isinstance(e.response.type, list):
                    response_typ = [str(t) for t in e.response.type]
                else:
                    response_typ = [str(e.response.type)]
                key = (tuple(param_typs), tuple(response_typ))
                group = self._groups.get(key, [name])
                groups.append(group)
            else:
                groups.append([name])

        return groups

    def _get_topo_sorts(self, p):
        perms = []
        pgraph = ProgramGraph()
        p.to_program_graph(graph=pgraph, var_to_trans={})
        all_topological_sorts(perms, pgraph, [], {})
        return perms

    def _generate_solutions(self, i, inputs, outputs, result, time):
        programs = []
        groups = self._expand_groups(result) 
        for r in itertools.product(*groups):
            programs += self._program_generator.generate_program(
                r, inputs, outputs[0]
            )

        # print(len(programs), flush=True)

        all_perms = []
        for p in programs:
            # print(p.to_expression({}))
            # write solutions to file
            self._write_solution(i, time, p)

            # generate all topological sorts for blocking
            if self._block_perms:
                perms = self._get_topo_sorts(p)
                all_perms += perms

        # convert permutations into indices
        perm_indices = []
        if self._block_perms:
            for perms in all_perms:
                indices = []
                for tr in perms:
                    for idx, r in enumerate(result):
                        if tr == r[:len(tr)]:
                            indices.append(idx)
                            break

                if len(indices) == len(result):
                    perm_indices.append(indices)
                

        # print("Get perms", perm_indices, flush=True)
        if not perm_indices:
            perm_indices = [list(range(len(result)))]

        self._serialize_solutions(i, programs)

        return programs, perm_indices

    def _create_encoder(self):
        solver = self._config[consts.KEY_SYNTHESIS][consts.KEY_SOLVER_TYPE]
        if solver == consts.SOLVER_PN_SMT:
            self._encoder = PetriNetEncoder({})
        elif solver == consts.SOLVER_HYPER:
            self._encoder = HyperGraphEncoder({})
        elif solver == consts.SOLVER_PN_ILP:
            self._encoder = ILPetriEncoder({})
        else:
            raise Exception("Unknown solver type in config")

        for name, e in self._unique_entries.items():
            self._encoder.add_transition(name, e)

    def run_n(self, landmarks, inputs, outputs, n):
        """Single process version of synthesis

        Args:
            landmarks ([type]): [description]
            inputs ([type]): [description]
            outputs ([type]): [description]
            n ([type]): [description]

        Returns:
            [type]: [description]
        """

        # create an encoder
        self._create_encoder()

        solutions = set()
        input_map = defaultdict(int)
        for _, typ in inputs.items():
            typ_name = str(typ.ignore_array())
            input_map[typ_name] += 1

        output_map = defaultdict(int)
        for typ in outputs:
            typ_name = str(typ.ignore_array())
            output_map[typ_name] += 1

        start = time.time()
        self._encoder.init(input_map, output_map)
        self._encoder.set_final(output_map)
        # self._encoder.add_all_constraints()

        while len(solutions) < n:
            result = self._encoder.solve()
            while result is not None:
                print("Find path", result, flush=True)
                programs, perms = self._generate_solutions(
                    0, inputs, outputs, result, 
                    time.time() - start
                )
                print("get programs", len(programs), flush=True)
                # print(programs[:3])
                solutions = solutions.union(set(programs))
                print("get solutions", len(solutions), flush=True)
                if len(solutions) >= n:
                    break

                self._encoder.block_prev(perms)
                result = self._encoder.solve()

            if self._encoder._path_len > consts.DEFAULT_LENGTH_LIMIT:
                print("Exceeding the default length limit")
                break

            if len(solutions) >= n:
                break

            print("No path found, incrementing the path length", flush=True)
            self._encoder.increment()
            self._encoder.set_final(output_map)
            # self._encoder.add_all_constraints()

        # write solutions
        with open("data/solutions.pkl", "wb") as f:
            pickle.dump(solutions, f)

        # write petri net data
        encoder_path = os.path.join(self._exp_dir, "encoder.txt")
        with open(encoder_path, "w") as f:
            f.write(str(len(self._encoder._net.place())))
            f.write("\n")
            f.write(str(len(self._encoder._net.transition())))

        # # write annotated entries
        # with open("data/annotated_entries.pkl", "wb") as f:
        #     pickle.dump(self._entries, f)

        return solutions

    def _add_transitions(self):
        unique_entries = self._group_transitions(self._entries)
        lst = [
            # "/v1/subscriptions_POST",
            # "/v1/prices_GET",
            # # "projection({'data': [price], 'has_more': boolean, 'object': string, 'url': string}, data)_",
            # "projection(price, id)_",
            # "/v1/products_POST",
            # "/v1/prices_POST",
            # "/v1/invoiceitems_POST",
            # 'projection(product, active)_',
            # "/v1/invoices_GET",
            # "/v1/charges/{charge}_GET",
            # "projection(invoice, charge)_",
            # "projection(price, unit_amount)_",
            # "/v1/refunds_POST",
            # "/v1/subscriptions/{subscription_exposed_id}_GET",
            # "/v1/subscriptions/{subscription_exposed_id}_POST",
            # 'projection(subscription, latest_invoice)_',
            # "/v1/invoices/{invoice}_GET",
            # "projection(card, last4)_",
            # "projection(payment_source, last4)_",
            # "/v1/invoices/{invoice}/send_POST"
            # "/v1/customers/{customer}/sources_GET",
            # 'filter(status_transitions, status_transitions.returned)_',

            # "/conversations.list_GET",
            # "/users.profile.get_GET",
            # "/conversations.members_GET",
            # "/users.lookupByEmail_GET",
            # "/conversations.open_POST",
            # "/chat.postMessage_POST",
            # "projection(objs_conversation, id)_",
            # "projection(objs_conversation, name)_",
            # '/conversations.create_POST',
            # "filter(objs_conversation, objs_conversation.name)_",
            # 'filter(objs_conversation, objs_conversation.latest.bot_profile.name)_',
            # "projection({'ok': defs_ok_true, 'profile': objs_user_profile}, profile)_",
            # "/conversations.history_GET",
            # "projection(objs_conversation, last_read)_",
            # "/users.conversations_GET",

            # "projection(ListInvoicesResponse, invoices)_",
            # "projection(Invoice, id)_",
            # "filter(Invoice, Invoice.id)_",
            # "filter(Invoice, Invoice.location_id)_",
            # "projection(Invoice, location_id)_",
            # "projection(Transaction, order_id)_",
            # "/v2/locations/{location_id}/transactions_GET",
            # "/v2/payments_GET",
            # "projection(ListPaymentsResponse, payments)_",
            # "projection(Payment, note)_",
            # "/v2/orders/{order_id}_PUT",
            # "/v2/orders/batch-retrieve_POST",
            # "projection(BatchRetrieveOrdersResponse, orders)_",
            # "projection(Order, line_items)_",
            # "projection(OrderLineItem, name)_",
            # "projection(Order, fulfillments)_",
        ]

        for name in lst:
            e = self._entries.get(name)
            print('-----')
            print(name)
            print([(p.arg_name, p.type, p.is_required) for p in e.parameters])
            print(e.response.type, flush=True)
            print("group members:", self._group_names.get(name, []))

        for name, e in self._entries.items():
            self._program_generator.add_signature(name, e)

        self._unique_entries = unique_entries

    def _group_transitions(self, transitions):
        # group projections with the same input and output
        results = {}
        for proj, e in transitions.items():
            param_typs = [str(p.type.ignore_array()) for p in e.parameters]
            if isinstance(e.response.type, list):
                response_typ = [str(t.ignore_array()) for t in e.response.type]
            else:
                response_typ = [str(e.response.type.ignore_array())]
            key = (tuple(param_typs), tuple(response_typ))
            if key not in self._groups:
                results[proj] = e
                self._groups[key] = [proj]
                self._group_names[proj] = [proj]
            else:
                rep = self._groups[key][0]
                self._groups[key].append(proj)
                self._group_names[rep].append(proj)

        return results