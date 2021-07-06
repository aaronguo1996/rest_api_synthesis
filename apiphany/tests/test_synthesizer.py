import unittest
from synthesizer.synthesizer import *
from analyzer.entry import TraceEntry, Parameter

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
            "projection(user, id):": TraceEntry(
                "projection(user, id)", "", None, [
                    Parameter(
                        "", "obj", "projection(user, id)", [],
                        True, None, None, None
                    )
                ],
                Parameter(
                    "", "field", "projection(user, id)", 
                    [], True, 0, None, None
                )
            ),
            "projection(user, name):": TraceEntry(
                "projection(user, name)", "", None, [
                    Parameter(
                        "", "obj", "projection(user, name)", [],
                        True, None, None, None
                    )
                ],
                Parameter(
                    "", "field", "projection(user, name)", 
                    [], True, 0, None, None
                )
            ),
            "projection(user, profile):": TraceEntry(
                "projection(user, profile)", "", None, [
                    Parameter(
                        "", "obj", "projection(user, profile)", [],
                        True, None, None, None,
                    )
                ],
                Parameter(
                    "", "field", "projection(user, profile)", 
                    [], True, 0, None, None
                )
            ),
            "projection(user.profile, email):": TraceEntry(
                "projection(user.profile, email)", "", None, [
                    Parameter(
                        "", "obj", "projection(user.profile, email)", [],
                        True, None, None, None,
                    )
                ],
                Parameter(
                    "", "field", "projection(user.profile, email)", 
                    [], True, 0, None, None
                )
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
            "filter(user, user.id):": TraceEntry(
                "filter(user, user.id)", "", None, [
                    Parameter(
                        "", "obj", "filter(user, user.id)", [],
                        True, None, None, None
                    ),
                    Parameter(
                        "", "field", "filter(user, user.id)", [],
                        True, None, None, None
                    ),
                ],
                Parameter(
                    "", "obj", "filter(user, user.id)",
                    [], True, 1, None, None
                )
            ),
            "filter(user, user.name):": TraceEntry(
                "filter(user, user.name)", "", None, [
                    Parameter(
                        "", "obj", "filter(user, user.name)", [],
                        True, None, None, None,
                    ),
                    Parameter(
                        "", "field", "filter(user, user.name)", [],
                        True, None, None, None
                    ),
                ],
                Parameter(
                    "", "obj", "filter(user, user.name)", 
                    [], True, 1, None, None
                )
            ),
            "filter(user, user.profile.email):": TraceEntry(
                "filter(user, user.profile.email)", "", None, [
                    Parameter(
                        "", "obj", "filter(user, user.profile.email)", [],
                        True, None, None, None
                    ),
                    Parameter(
                        "", "field", "filter(user, user.profile.email)", [],
                        True, None, None, None
                    ),
                ],
                Parameter(
                    "", "obj", "filter(user, user.profile.email)", 
                    [], True, 1, None, None
                )
            ),
        })

    def test_single_transition(self):
        self._synthesizer.init()

        result = self._synthesizer.run(
            [],
            {
                "user": SchemaType("defs_user_id", None)
            }, 
            [
                SchemaType("objs_user", None)
            ],
        )
        self.assertEqual(result, [
            "/users.info:GET",
            'projection(/users.info_response, user):',
        ])

        result = self._synthesizer.run(
            [],
            {
                "user_id": SchemaType("objs_user", None)
            }, 
            [
                SchemaType("defs_user_id", None)
            ],
        )
        self.assertEqual(result, [
            "projection(objs_user, id):",
        ])

    def test_two_transitions(self):
        self._synthesizer.init()
        
        result = self._synthesizer.run(
            [],
            {
                "user_id": SchemaType("defs_user_id", None)
            }, 
            [
                SchemaType("objs_user.name", None)
            ],
        )
        self.assertEqual(result, [
            "/users.info:GET",
            'projection(/users.info_response, user):',
            "projection(objs_user, name):",
        ])

        result = self._synthesizer.run(
            [],
            {
                "user_id": SchemaType("defs_user_id", None)
            }, 
            [
                SchemaType("objs_user.profile.email", None)
            ],
        )
        self.assertEqual(result,
            [
                "/users.info:GET",
                'projection(/users.info_response, user):',
                "projection(objs_user, profile):",
                "projection(objs_user.profile, email):"
            ],
        )

    def test_nullary(self):
        self._synthesizer.init()
        result = self._synthesizer.run(
            [],
            {}, 
            [
                SchemaType("defs_dm_id", None)
            ],
        )
        self.assertEqual(result, [
            "/conversations.list:GET",
            "projection(/conversations.list_response, channels):",
            "projection(objs_conversation, id):",
        ])

    def test_example_b(self):
        self._synthesizer.init()

        result = self._synthesizer.run_n(
            # ["/conversations.members:GET"],
            [],
            {
                # "channel_name": SchemaType("objs_message.name", None)
                "channel_name": SchemaType("objs_conversation.name", None)
            },
            [
                SchemaType("objs_user.profile.email", None)
            ],
            10
        )
        print(result)
        # self.assertIn([
        #     "/conversations.list:GET",
        #     "filter(objs_conversation, objs_conversation.name):",
        #     "projection(objs_conversation, id):",
        #     "/conversations.members:GET",
        #     "/users.info:GET",
        #     "projection(objs_user, profile):",
        #     "projection(objs_user.profile, email):"
        # ], result)
        # self.assertEqual(result, [])

    def test_example_a(self):
        self._synthesizer.init()

        self._synthesizer.run_n(
            # ["/conversations.members:get"],
            [],
            {
                "email": SchemaType("objs_user.profile.email", None)
            }, 
            [
                SchemaType("objs_message", None),
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
    return suite
