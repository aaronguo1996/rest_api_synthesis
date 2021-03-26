import unittest
from synthesizer.synthesizer import *
# from analyzer.entry import DocEntry, RequestParameter, ResponseParameter

class SynthesizerTestCase(unittest.TestCase):
    @staticmethod
    def _setUp(doc, config, analyzer):
        SynthesizerTestCase._doc = doc
        SynthesizerTestCase._config = config
        SynthesizerTestCase._analyzer = analyzer

    def setUp(self):
        self._synthesizer = Synthesizer(
            SynthesizerTestCase._doc,
            SynthesizerTestCase._config,
            SynthesizerTestCase._analyzer,
        )
        self.maxDiff = None

    def test_create_projection(self):
        projections = self._synthesizer._create_projection("user", {
            "properties": {
                "id": {
                    "type": "string",
                },
                "name": {
                    "type": "string",
                },
                "profile": {
                    "type": "object",
                    "properties": {
                        "email": {
                            "type": "string",
                        },
                    },
                },
            }
        })
        self.assertEqual(projections, {
            "projection(user, id)": DocEntry(
                "projection(user, id)", "", [
                    RequestParameter(
                        "", "", "projection(user, id)", 
                        True, None, None
                    )
                ], [
                    ResponseParameter(
                        "", "", "projection(user, id)", 
                        [], True, 0, None, None
                    )
                ]
            ),
            "projection(user, name)": DocEntry(
                "projection(user, name)", "", [
                    RequestParameter(
                        "", "", "projection(user, name)", 
                        True, None, None
                    )
                ], [
                    ResponseParameter(
                        "", "", "projection(user, name)", 
                        [], True, 0, None, None
                    )
                ]
            ),
            "projection(user, profile)": DocEntry(
                "projection(user, profile)", "", [
                    RequestParameter(
                        "", "", "projection(user, profile)", 
                        True, None, None
                    )
                ], [
                    ResponseParameter(
                        "", "", "projection(user, profile)", 
                        [], True, 0, None, None
                    )
                ]
            ),
            "projection(user.profile, email)": DocEntry(
                "projection(user.profile, email)", "", [
                    RequestParameter(
                        "", "", "projection(user.profile, email)", 
                        True, None, None
                    )
                ], [
                    ResponseParameter(
                        "", "", "projection(user.profile, email)", 
                        [], True, 0, None, None
                    )
                ]
            ),
        })

    def test_create_filter(self):
        filters = self._synthesizer._create_filter("user", "user", {
            "properties": {
                "id": {
                    "type": "string",
                },
                "name": {
                    "type": "string",
                },
                "profile": {
                    "type": "object",
                    "properties": {
                        "email": {
                            "type": "string",
                        },
                    },
                },
            }
        })
        self.assertEqual(filters, {
            "filter(user, user.id)": DocEntry(
                "filter(user, user.id)", "", [
                    RequestParameter(
                        "", "", "filter(user, user.id)", 
                        True, None, None
                    ),
                    RequestParameter(
                        "", "", "filter(user, user.id)", 
                        True, None, None
                    ),
                ], [
                    ResponseParameter(
                        "", "", "filter(user, user.id)", 
                        [], True, 1, None, None
                    ),
                ]
            ),
            "filter(user, user.name)": DocEntry(
                "filter(user, user.name)", "", [
                    RequestParameter(
                        "", "", "filter(user, user.name)", 
                        True, None, None
                    ),
                    RequestParameter(
                        "", "", "filter(user, user.name)", 
                        True, None, None
                    ),
                ], [
                    ResponseParameter(
                        "", "", "filter(user, user.name)", 
                        [], True, 1, None, None
                    ),
                ]
            ),
            "filter(user, user.profile.email)": DocEntry(
                "filter(user, user.profile.email)", "", [
                    RequestParameter(
                        "", "", "filter(user, user.profile.email)", 
                        True, None, None
                    ),
                    RequestParameter(
                        "", "", "filter(user, user.profile.email)", 
                        True, None, None
                    ),
                ], [
                    ResponseParameter(
                        "", "", "filter(user, user.profile.email)", 
                        [], True, 1, None, None
                    ),
                ]
            ),
        })

    def test_single_transition(self):
        self._synthesizer.init()

        result = self._synthesizer.run(
            {"defs_user_id": 1}, 
            {"objs_user": 1}
        )
        self.assertEqual(result, [
            "/users.info:get",
        ])

        result = self._synthesizer.run(
            {"objs_user": 1}, 
            {"defs_user_id": 1}
        )
        self.assertEqual(result, [
            "projection(objs_user, id):",
        ])

    def test_two_transitions(self):
        self._synthesizer.init()
        
        result = self._synthesizer.run(
            {"defs_user_id": 1}, 
            {"objs_user.name": 1}
        )
        self.assertEqual(result, [
            "/users.info:get",
            "projection(objs_user, real_name):",
        ])

        result = self._synthesizer.run(
            {"defs_user_id": 1},
            {"objs_user.profile.email": 1}
        )
        self.assertEqual(result,
            [
                "/users.info:get", 
                "projection(objs_user, profile):",
                "projection(objs_user.profile, email):"
            ],
        )

    def test_nullary(self):
        self._synthesizer.init()
        result = self._synthesizer.run_all(
            [],
            {}, 
            {"defs_group_id": 1}
        )
        self.assertEqual(result, ["/conversations.list:get"])

    def test_example_b(self):
        self._synthesizer.init()

        result = self._synthesizer.run_n(
            # ["/conversations.members:GET"],
            [],
            {
                # "channel_name": SchemaType("objs_conversation.name", None)
                "channel_name": SchemaType("objs_message.name", None)
            },
            [
                SchemaType("objs_user.profile.email", None)
            ],
            30
        )
        print(result)
        self.assertIn([
            "/conversations.list:GET",
            "filter(objs_conversation, objs_conversation.name):",
            "projection(objs_conversation, id):",
            "/conversations.members:GET",
            "/users.info:GET",
            "projection(objs_user, profile):",
            "projection(objs_user.profile, email):"
        ], result)
        # self.assertEqual(result, [])

    def test_example_b_short(self):
        self._synthesizer.init()

        result = self._synthesizer.run_n(
            # ["/conversations.members:GET"],
            [],
            {
                "channel_name": SchemaType("objs_message.name", None)
            },
            [
                SchemaType("objs_user.profile.email", None)
            ],
            50
        )
        self.assertIn([
            "/conversations.list:GET",
            "filter(objs_conversation, objs_conversation.name):",
            "projection(objs_conversation, id):",
            "/conversations.members:GET",
            "/users.info:GET",
            "projection(objs_user, profile):",
            "projection(objs_user.profile, email):"
        ], result)
        # result = self._synthesizer.run_n(
        #     [],
        #     {
        #         "channel_id": SchemaType("defs_group_id", None)
        #     },
        #     [
        #         SchemaType("/conversations.members_response", None)
        #     ],
        #     1
        # )
        print(result)

    def test_example_a(self):
        self._synthesizer.init()

        result = self._synthesizer.run_n(
            # ["/conversations.members:get"],
            [],
            {
                "email": SchemaType("objs_user.profile.email", None)
            }, 
            [
                SchemaType("objs_message", None), 
                # SchemaType("defs_group_id", None),
                # SchemaType("defs_ts", None),
            ],
            25
        )

        # self.assertIn([
        #     "/users.lookupByEmail:get",
        #     "projection(objs_user, id)",
        #     "/conversations.open:post",
        #     "projection(objs_conversation, id)",
        #     "/chat.postMessage:post",
        # ], result)

def synthesizer_suite(doc, config, analyzer):
    SynthesizerTestCase._setUp(doc, config, analyzer)
    suite = unittest.TestSuite()
    # suite.addTest(SynthesizerTestCase('test_create_projection'))
    # suite.addTest(SynthesizerTestCase('test_create_filter'))
    # suite.addTest(SynthesizerTestCase('test_single_transition'))
    # suite.addTest(SynthesizerTestCase('test_two_transitions'))
    # suite.addTest(SynthesizerTestCase('test_nullary'))
    # suite.addTest(SynthesizerTestCase('test_example_a'))
    suite.addTest(SynthesizerTestCase('test_example_b'))
    # suite.addTest(SynthesizerTestCase('test_example_b_short'))
    return suite