import unittest
from synthesizer.petrinet_encoder import *
from analyzer.entry import TraceEntry, Parameter
from schemas.schema_type import SchemaType

class EncoderTestCase(unittest.TestCase):
    def setUp(self):
        self._encoder = PetriNetEncoder({})
        self._entries = [
            TraceEntry("/users.list", "GET", [], 
                Parameter(
                    "GET", "users", "/users.list", 
                    [], True, 1, SchemaType("user", None), [])
            ),
            TraceEntry("/conversations.members", "GET", [
                    Parameter(
                        "GET", "channel", "/conversations.members", [], 
                        True, None, SchemaType("channel.id", None), None)
                ], 
                Parameter(
                    "GET", "members", "/conversations.members", 
                    [], True, 1, SchemaType("user.id", None), [])
            ),
            TraceEntry("/conversations.info", "GET", [
                    Parameter(
                        "GET", "channel", "/conversations.info", [],
                        True, None, SchemaType("channel.id", None), None)
                ],
                Parameter(
                    "GET", "channel", "/conversations.info", 
                    [], True, 0, SchemaType("channel", None), [])
            ),
            TraceEntry("/conversations.list", "GET", [],
                Parameter(
                    "GET", "channel", "/conversations.list", 
                    [], True, 1, SchemaType("channel", None), [])
            ),
            TraceEntry("/users.lookupByEmail", "GET", [
                    Parameter(
                        "GET", "email", "/users.lookupByEmail", [],
                        True, None, SchemaType("user.profile.email", None), None)
                ], 
                Parameter(
                    "GET", "user", "/users.lookupByEmail", 
                    [], True, 0, SchemaType("user", None), None)
            ),
            TraceEntry("/users.info", "GET", [
                    Parameter(
                        "GET", "user", "/users.info", [],
                        True, None, SchemaType("user.id", None), None)
                ],
                Parameter(
                    "GET", "user", "/users.info", 
                    [], True, 0, SchemaType("user", None), [])
            ),
            TraceEntry("projection_channel_id", "", [
                    Parameter(
                        "", "", "projection_channel_id", [],
                        True, None, SchemaType("channel", None), None)
                ],
                Parameter(
                    "", "", "projection_channel_id", 
                    [], True, 0, SchemaType("channel.id", None), None)
            ),
            TraceEntry("projection_user_email", "", [
                    Parameter(
                        "", "", "projection_user_email", [],
                        True, None, SchemaType("user", None), None)
                ],
                Parameter(
                    "", "", "projection_user_email", 
                    [], True, 0, SchemaType("user.profile.email", None), None)
            ),
            TraceEntry("join_1_1", "", [ # this works like clone transitions, but allow produce tokens to be leaked
                    Parameter(
                        "", "", "join_1", [],
                        True, None, SchemaType("channel.name", None), None),
                    Parameter(
                        "", "", "join_1", [],
                        True, None, SchemaType("channel", None), None),
                ],
                Parameter(
                    "", "", "join_1", [], 
                    True, 1, SchemaType("channel", None), None),
            ),
            TraceEntry("join_1_2", "", [ # this works like clone transitions, but allow produce tokens to be leaked
                    Parameter(
                        "", "", "join_1", [],
                        True, None, SchemaType("channel.name", None), None),
                    Parameter(
                        "", "", "join_1", [],
                        True, SchemaType("channel", None), None),
                ],
                Parameter(
                    "", "", "join_1", 
                    [], True, 1, SchemaType("channel.name", None), None),
            ),
            TraceEntry("join_2_1", "", [ # this works like clone transitions, but allow produce tokens to be leaked
                    Parameter(
                        "", "", "join_2", [],
                        True, None, SchemaType("user.id", None), None),
                    Parameter(
                        "", "", "join_2", [],
                        True, None, SchemaType("user", None), None),
                ],
                Parameter(
                    "", "", "join_2", [], 
                    True, 1, SchemaType("user.id", None), None),
            ),
            TraceEntry("join_2_2", "", [ # this works like clone transitions, but allow produce tokens to be leaked
                    Parameter(
                        "", "", "join_2", [],
                        True, None, SchemaType("user.id", None), None),
                    Parameter(
                        "", "", "join_2", [],
                        True, None, SchemaType("user", None), None),
                ],
                Parameter(
                    "", "", "join_2", [], 
                    True, 1, SchemaType("user", None), None),
            ),
            TraceEntry("/conversations.history", "GET", [
                    Parameter(
                        "GET", "channel", "/conversations.history", [],
                        True, None, SchemaType("channel.id", None), None),
                    Parameter(
                        "GET", "last_read", "/conversations.history", [],
                        False, None, SchemaType("ts", None), None)
                ],
                Parameter(
                    "GET", "messages", "/conversations.history", 
                    [], True, 1, SchemaType("message", None), [])
            ),
        ]

    def test_add_transition_users_list(self):
        entry = self._entries[0]
        self._encoder.add_transition(entry)
        # check results
        self.assertEqual([p.name for p in self._encoder._net.place()],
            ["user"])
        self.assertEqual([tr.name for tr in self._encoder._net.transition()],
            ["/users.list:GET"])
        self.assertEqual([(p.name, t.value)
            for (p, t) in self._encoder._net.transition("/users.list:GET").output()],
            [("user", 1)])
        self.assertEqual(self._encoder._net.transition("/users.list:GET").input(), [])

    def test_add_transition_conversations_members(self):
        entry = self._entries[1]
        self._encoder.add_transition(entry)
        # check results
        self.assertEqual([p.name for p in self._encoder._net.place()],
            ["channel.id", "user.id"])
        self.assertEqual([tr.name for tr in self._encoder._net.transition()],
            ["/conversations.members:GET"])
        self.assertEqual([(p.name, t.value)
            for (p, t) in self._encoder._net.transition("/conversations.members:GET").input()],
            [("channel.id", 1)])
        self.assertEqual([(p.name, t.value)
            for (p, t) in self._encoder._net.transition("/conversations.members:GET").output()],
            [("user.id", 1)])

    def test_petrinet_creation(self):
        for entry in self._entries:
            self._encoder.add_transition(entry)

        # check places
        real_places = sorted([p.name for p in self._encoder._net.place()])
        expected_places = sorted(
            [
                "channel.id", 
                "user.id", 
                "user", 
                "channel", 
                "user.profile.email",
                "channel.name",
                "ts",
                "message",
            ])
        self.assertEqual(real_places, expected_places)
        
        # check transitions
        real_transitions = sorted(
            [tr.name for tr in self._encoder._net.transition()])
        expected_transitions = sorted(
            [
                "/users.list:GET",
                "/conversations.list:GET",
                "/conversations.members:GET",
                "/conversations.info:GET",
                "/users.lookupByEmail:GET",
                "/users.info:GET",
                "projection_user_email:",
                "projection_channel_id:",
                "join_1_1:",
                "join_1_2:",
                "join_2_1:",
                "join_2_2:",
                "/conversations.history:GET",
            ]
        )
        self.assertEqual(real_transitions, expected_transitions)
        
        # check flows
        real_inputs = sorted([(p.name, t.value) for (p, t) in 
            self._encoder._net.transition("/conversations.members:GET").input()])
        expected_inputs = sorted(
            [
                ("channel.id", 1),
            ])
        self.assertEqual(real_inputs, expected_inputs)

        real_outputs = sorted([(p.name, t.value) for (p, t) in 
            self._encoder._net.transition("/conversations.members:GET").output()])
        expected_outputs = sorted(
            [
                ("user.id", 1),
            ]
        )
        self.assertEqual(real_outputs, expected_outputs)

        real_post = self._encoder._net.post("channel.id")
        expected_post = set(
            [
                "/conversations.members:GET",
                "/conversations.info:GET",
                "/conversations.history:GET",
            ]
        )
        self.assertEqual(real_post, expected_post)

        real_pre = self._encoder._net.pre("user")
        expected_pre = set(
            [
                "/users.list:GET",
                "/users.lookupByEmail:GET",
                "/users.info:GET",
                "join_2_2:",
            ]
        )
        self.assertEqual(real_pre, expected_pre)

    def test_set_initial(self):
        self._encoder.add_transition(self._entries[4])
        self._encoder._set_initial({"user.profile.email": 1})
        self._encoder._solver.check()
        m = self._encoder._solver.model()
        i = self._encoder._place_to_variable.get(("user.profile.email", 0))
        self.assertEqual(m[Int(i)], 1)

    def test_set_final(self):
        self._encoder.add_transition(self._entries[4])
        self._encoder._path_len = 3
        self._encoder._set_initial({"user.profile.email": 2})
        self._encoder._solver.check()
        m = self._encoder._solver.model()
        i = self._encoder._place_to_variable.get(("user.profile.email", 3))
        self.assertEqual(m[Int(i)], 2)

    def test_solve_single_transition(self):
        self._encoder.add_transition(self._entries[4])
        self._encoder.init(
            [], 
            {"user.profile.email": 1}, 
            {"user": 1}
        )

        result = self._encoder.solve()
        while result is None:
            if self._encoder._path_len > 1:
                break

            self._encoder.increment([], {"user": 1})
            # print(self._encoder._solver.assertions())
            result = self._encoder.solve()

        self.assertEqual(result, ["/users.lookupByEmail:GET"])

    def test_solve_transition_chain(self):
        for entry in self._entries:
            self._encoder.add_transition(entry)

        inputs = {
            "channel.name": 1,
        }
        outputs = {
            "user.profile.email": 1,
        }
        self._encoder.init([], inputs, outputs)
        
        result = self._encoder.solve()
        while result is None:
            if self._encoder._path_len >= 10:
                break

            self._encoder.increment([], outputs)
            # print(self._encoder._solver.assertions())
            result = self._encoder.solve()
            # print(self._encoder._solver.unsat_core())

        self.assertEqual(result, [
            "/conversations.list:GET",
            "join_1_1:",
            "projection_channel_id:",
            "/conversations.members:GET",
            "/users.info:GET",
            "projection_user_email:",
        ])

    def test_optional_args(self):
        self._encoder.add_transition(self._entries[-1])

        # case I: optional argument is not provided
        inputs = {
            "channel.id": 1,
        }
        outputs = {
            "message": 1,
        }
        self._encoder.init([], inputs, outputs)
        
        result = self._encoder.solve()
        while result is None:
            if self._encoder._path_len >= 1:
                break

            self._encoder.increment([], outputs)
            # print(self._encoder._solver.assertions())
            result = self._encoder.solve()
            # print(self._encoder._solver.unsat_core())

        self.assertEqual(result, [
            "/conversations.history:GET",
        ])

        # case II: optional argument is provided
        inputs["ts"] = 1
        self._encoder.init([], inputs, outputs)
        
        result = self._encoder.solve()
        while result is None:
            if self._encoder._path_len >= 1:
                break

            self._encoder.increment([], outputs)
            # print(self._encoder._solver.assertions())
            result = self._encoder.solve()
            # print(self._encoder._solver.unsat_core())

        self.assertEqual(result, [
            "/conversations.history:GET",
        ])

def encoder_suite():
    suite = unittest.TestSuite()
    suite.addTest(EncoderTestCase('test_add_transition_users_list'))
    suite.addTest(EncoderTestCase('test_add_transition_conversations_members'))
    suite.addTest(EncoderTestCase('test_petrinet_creation'))
    suite.addTest(EncoderTestCase('test_set_initial'))
    suite.addTest(EncoderTestCase('test_solve_single_transition'))
    suite.addTest(EncoderTestCase('test_solve_transition_chain'))
    suite.addTest(EncoderTestCase('test_optional_args'))
    return suite