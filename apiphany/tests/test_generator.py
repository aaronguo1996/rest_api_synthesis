import unittest

from apiphany.program.generator import *
from apiphany.analyzer.entry import TraceEntry, Parameter
from apiphany.schemas.schema_type import SchemaType

class GeneratorTestCase(unittest.TestCase):
    def setUp(self):
        self.maxDiff = None
        self._generator = ProgramGenerator({})

    def test_generate_projection(self):
        sig = TraceEntry("projection(user, id)", "", None,
            [
                Parameter(
                    "", "id", "projection(user, id)", [],
                    True, None, SchemaType("user", None), None
                ),
            ],
            Parameter(
                "", "user.id", "projection(user, id)",
                [], True, 0, SchemaType("user.id", None), None
            ),
        )
        subst = {
            "user": [(VarExpr("x0"), 0)],
        }
        self._generator.add_signature("projection(user, id)", sig)
        self._generator._generate_projection(subst, sig)
        self.assertEqual(subst, {
            "user": [
                (VarExpr("x0"), 0)
            ],
            "user.id": [
                (ProjectionExpr(VarExpr("x0"), "id"), 0)
            ],
        })

    def test_generate_filter(self):
        sig = TraceEntry("filter(user, user.id)", "", None,
            [
                Parameter(
                    "", "id", "filter(user, user.id)", [], 
                    True, None, SchemaType("user", None), None
                ),
                Parameter(
                    "", "user.id", "filter(user, user.id)", [],
                    True, None, SchemaType("user.id", None), None
                ),
            ],
            Parameter(
                "", "user.id", "filter(user, user.id)",
                [], True, 0, SchemaType("user", None), None
            ),
            )
        subst = {
            "user": [
                (VarExpr("x1"), 0)
            ],
            "user.id": [
                (VarExpr("x2"), 0)
            ]
        }
        self._generator.add_signature("filter(user, user.id)", sig)
        self._generator._generate_filter(subst, sig)
        self.assertEqual(subst, {
            "user": [
                (VarExpr("x1"), 0), 
                (FilterExpr(VarExpr("x1"), "id", VarExpr("x2"), False), 1)
            ],
            "user.id": [
                (VarExpr("x2"), 0)
            ],
        })

    def test_generate_let(self):
        sig = TraceEntry("/users.lookupByEmail", "", None,
            [
                Parameter(
                    "get", "email", "/users.lookupByEmail", [], 
                    True, None, SchemaType("user.profile.email", None), None
                ),
            ],
            Parameter(
                "get", "user", "/users.lookupByEmail",
                ["user"], True, 0, SchemaType("user", None), None
            ),
        )
        subst = {
            "user.profile.email": [
                (VarExpr("email"), 0)
            ],
        }
        self._generator.add_signature("/users.lookupByEmail", sig)
        self._generator._generate_let(subst, sig)
        self.assertEqual(subst, {
            "user": [
                (AppExpr("/users.lookupByEmail", [("email", VarExpr("email"))]), 0)
            ],
            "user.profile.email": [
                (VarExpr("email"), 0)
            ],
        })

    def test_generate_program(self):
        sigs = {
            "/conversations.list:get": 
                TraceEntry("/conversations.list", "", None,
                    [],
                    Parameter(
                        "get", "channels", "/conversations.list",
                        ["channels"], True, 1,
                        SchemaType("objs_conversation", None), None
                    ),
                ),
            "/conversations.members:get":
                TraceEntry("/conversations.members", "get", None,
                    [
                        Parameter(
                            "get", "channel", "/conversations.members", [],
                            True, None, SchemaType("objs_channel.id", None), None
                        ),
                    ],
                    Parameter(
                        "get", "users", "/conversations.members",
                        ["users"], True, 1,
                        SchemaType("defs_user_id", None), None
                    )
                ),
            "/users.info:get":
                TraceEntry("/users.info", "get", None,
                    [
                        Parameter(
                            "get", "user", "/users.info", [],
                            True, None, SchemaType("defs_user_id", None), None
                        ),
                    ],
                    Parameter(
                        "get", "user", "/users.info",
                        ["user"], True, 1,
                        SchemaType("objs_user", None), None
                    ),
                ),
            "filter(objs_conversation, objs_conversation.name):":
                TraceEntry("filter(objs_conversation, objs_conversation.name)", 
                    "", None,
                    [
                        Parameter(
                            "", "", 
                            "filter(objs_conversation, objs_conversation.name)", 
                            [], True, None,
                            SchemaType("objs_conversation", None), None
                        ),
                        Parameter(
                            "", "", 
                            "filter(objs_conversation, objs_conversation.name)",
                            [], True, None,
                            SchemaType("objs_conversation.name", None), None
                        ),
                    ],
                    Parameter(
                        "", "", 
                        "filter(objs_conversation, objs_conversation.name)",
                        [], True, 1,
                        SchemaType("objs_conversation", None), None
                    ),
                ),
            "projection(objs_conversation, id):":
                TraceEntry("projection(objs_conversation, id)", "", None,
                    [
                        Parameter(
                            "", "", "projection(objs_conversation, id)", [],
                            True, None,
                            SchemaType("objs_conversation", None), None
                        ),
                    ],
                    Parameter(
                        "", "", "projection(objs_conversation, id)",
                        [], True, 0,
                        SchemaType("objs_channel.id", None), None
                    )
                ),
            "projection(objs_user, profile):":
                TraceEntry("projection(objs_user, profile)", "", None,
                    [
                        Parameter(
                            "", "", "projection(objs_user, profile)", [],
                            True, None, SchemaType("objs_user", None), None
                        ),
                    ],
                    Parameter(
                        "", "", "projection(objs_user, profile)",
                        [], True, 0,
                        SchemaType("objs_user.profile", None), None
                    )
                ),
            "projection(objs_user.profile, email):":
                TraceEntry("projection(objs_user.profile, email)", "", None,
                    [
                        Parameter(
                            "", "", "projection(objs_user.profile, email)", [],
                            True, None, 
                            SchemaType("objs_user.profile", None), None
                        ),
                    ],
                    Parameter(
                        "", "", "projection(objs_user.profile, email)",
                        [], True, 0,
                        SchemaType("objs_user.profile.email", None), None
                    )
                ),
        }

        inputs = {
            "channel_name": SchemaType("objs_conversation.name", None),
        }

        for name, sig in sigs.items():
            self._generator.add_signature(name, sig)
        
        results = self._generator.generate_program([
                "/conversations.list:get",
                "filter(objs_conversation, objs_conversation.name):",
                "projection(objs_conversation, id):",
                "/conversations.members:get",
                "/users.info:get",
                "projection(objs_user, profile):",
                "projection(objs_user.profile, email):",
            ], 
            inputs, 
            SchemaType("objs_user.profile.email", None)
        )

        target = Program(
            [
                "channel_name"
            ],
            [
                MapExpr(
                    MapExpr(
                        MapExpr(
                            MapExpr(
                                MapExpr(
                                    FilterExpr(
                                        AppExpr("/conversations.list", []), 
                                        "name", 
                                        VarExpr("channel_name"), 
                                        False
                                    ), 
                                    Program(
                                        ["x0"],
                                        [ProjectionExpr(VarExpr("x0"), "id")]
                                    )
                                ),
                                Program(
                                    ["x1"],
                                    [AppExpr("/conversations.members", [("channel", VarExpr("x1"))])]
                                ),
                            ),
                            Program(
                                ["x2"],
                                [AppExpr("/users.info", [("user", VarExpr("x2"))])]
                            )
                        ),
                        Program(
                            ["x3"],
                            [ProjectionExpr(VarExpr("x3"), "profile")]
                        )
                    ), 
                    Program(
                        ["x4"],
                        [ProjectionExpr(VarExpr("x4"), "email")]
                    )
                ),
            ]
        )

        self.assertEqual(results, [target.to_multiline({"x": 5})])

def generator_suite():
    suite = unittest.TestSuite()
    suite.addTest(GeneratorTestCase('test_generate_projection'))
    suite.addTest(GeneratorTestCase('test_generate_filter'))
    suite.addTest(GeneratorTestCase('test_generate_let'))
    suite.addTest(GeneratorTestCase('test_generate_program'))
    return suite