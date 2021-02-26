import unittest
from program.generator import *
from analyzer.entry import TraceEntry, RequestParameter, ResponseParameter
from schemas.schema_type import SchemaType

class GeneratorTestCase(unittest.TestCase):
    def setUp(self):
        self.maxDiff = None
        self._generator = ProgramGenerator({})

    def test_generate_projection(self):
        sig = TraceEntry("projection(user, id)", "", 
            [
                RequestParameter(
                    "", "id", "projection(user, id)", 
                    True, SchemaType("user", None), None
                ),
            ],
            ResponseParameter(
                "", "user.id", "projection(user, id)",
                [], True, 0, SchemaType("user.id", None), None
            ),
            )
        subst = {
            "user": [VarExpr("x1")],
        }
        self._generator.add_signature("projection(user, id)", sig)
        results = self._generator._generate_projection(subst, sig)
        self.assertEqual(results, [])
        self.assertEqual(subst, {
            "user": [VarExpr("x1")],
            "user.id": [ProjectionExpr(VarExpr("x1"), "id")],
        })

    def test_generate_filter(self):
        sig = TraceEntry("filter(user, user.id)", "", 
            [
                RequestParameter(
                    "", "id", "filter(user, user.id)", 
                    True, SchemaType("user", None), None
                ),
                RequestParameter(
                    "", "user.id", "filter(user, user.id)",
                    True, SchemaType("user.id", None), None
                ),
            ],
            ResponseParameter(
                "", "user.id", "filter(user, user.id)",
                [], True, 0, SchemaType("user", None), None
            ),
            )
        subst = {
            "user": [VarExpr("x1")],
            "user.id": [VarExpr("x2")]
        }
        self._generator.add_signature("filter(user, user.id)", sig)
        results = self._generator._generate_filter(subst, sig)
        self.assertEqual(results, [
            AssignExpr("x0", FilterExpr(VarExpr("x1"), "id", VarExpr("x2"))),
        ])
        self.assertEqual(subst, {
            "user": [VarExpr("x1"), VarExpr("x0")],
            "user.id": [VarExpr("x2")],
        })

    def test_generate_let(self):
        sig = TraceEntry("/users.lookupByEmail", "", 
            [
                RequestParameter(
                    "get", "email", "/users.lookupByEmail", 
                    True, SchemaType("user.profile.email", None), None
                ),
            ],
            ResponseParameter(
                "get", "user", "/users.lookupByEmail",
                ["user"], True, 0, SchemaType("user", None), None
            ),
            )
        subst = {
            "user.profile.email": [VarExpr("email")],
        }
        self._generator.add_signature("/users.lookupByEmail", sig)
        results = self._generator._generate_let(subst, sig)
        self.assertEqual(results, [
            AssignExpr(
                "x0", 
                AppExpr("/users.lookupByEmail", [VarExpr("email")])
            ),
        ])
        self.assertEqual(subst, {
            "user": [VarExpr("x0")],
            "user.profile.email": [VarExpr("email")],
        })

    def test_generate_program(self):
        sigs = {
            "/conversations.list:get": 
                TraceEntry("/conversations.list", "", 
                    [],
                    ResponseParameter(
                        "get", "channels", "/conversations.list",
                        ["channels"], True, 1,
                        SchemaType("objs_conversation", None), None
                    ),
                ),
            "/conversations.members:get":
                TraceEntry("/conversations.members", "get",
                    [
                        RequestParameter(
                            "get", "channel", "/conversations.members",
                            True, SchemaType("objs_channel.id", None), None
                        ),
                    ],
                    ResponseParameter(
                        "get", "users", "/conversations.members",
                        ["users"], True, 1,
                        SchemaType("defs_user_id", None), None
                    )
                ),
            "/users.info:get":
                TraceEntry("/users.info", "get",
                    [
                        RequestParameter(
                            "get", "user", "/users.info",
                            True, SchemaType("defs_user_id", None), None
                        ),
                    ],
                    ResponseParameter(
                        "get", "user", "/users.info",
                        ["user"], True, 1,
                        SchemaType("objs_user", None), None
                    ),
                ),
            "filter(objs_conversation, objs_channel.name):":
                TraceEntry("filter(objs_conversation, objs_channel.name)", "",
                    [
                        RequestParameter(
                            "", "", "filter(objs_conversation, objs_channel.name)",
                            True, SchemaType("objs_conversation", None), None
                        ),
                        RequestParameter(
                            "", "", "filter(objs_conversation, objs_channel.name)",
                            True, SchemaType("objs_channel.name", None), None
                        ),
                    ],
                    ResponseParameter(
                        "", "", "filter(objs_conversation, objs_channel.name)",
                        [], True, 1,
                        SchemaType("objs_conversation", None), None
                    ),
                ),
            "projection(objs_conversation, id):":
                TraceEntry("projection(objs_conversation, id)", "",
                    [
                        RequestParameter(
                            "", "", "projection(objs_conversation, id)",
                            True, SchemaType("objs_conversation", None), None
                        ),
                    ],
                    ResponseParameter(
                        "", "", "projection(objs_conversation, id)",
                        [], True, 0,
                        SchemaType("objs_channel.id", None), None
                    )
                ),
            "projection(objs_user, profile):":
                TraceEntry("projection(objs_user, profile)", "",
                    [
                        RequestParameter(
                            "", "", "projection(objs_user, profile)",
                            True, SchemaType("objs_user", None), None
                        ),
                    ],
                    ResponseParameter(
                        "", "", "projection(objs_user, profile)",
                        [], True, 0,
                        SchemaType("objs_user.profile", None), None
                    )
                ),
            "projection(objs_user.profile, email):":
                TraceEntry("projection(objs_user.profile, email)", "",
                    [
                        RequestParameter(
                            "", "", "projection(objs_user.profile, email)",
                            True, SchemaType("objs_user.profile", None), None
                        ),
                    ],
                    ResponseParameter(
                        "", "", "projection(objs_user.profile, email)",
                        [], True, 0,
                        SchemaType("objs_user.profile.email", None), None
                    )
                ),
        }

        inputs = {
            "channel_name": SchemaType("objs_channel.name", None),
        }

        for name, sig in sigs.items():
            self._generator.add_signature(name, sig)
        
        results = self._generator.generate_program([
                "/conversations.list:get",
                "filter(objs_conversation, objs_channel.name):",
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
                AssignExpr(
                    "x0", 
                    AppExpr("/conversations.list", [])
                ),
                AssignExpr(
                    "x1",
                    FilterExpr(VarExpr("x0"), "name", VarExpr("channel_name"))
                ),
                AssignExpr(
                    "x2",
                    AppExpr("/conversations.members", [
                            ProjectionExpr(VarExpr("x1"), "id")
                        ]
                    ),
                ),
                AssignExpr(
                    "x3",
                    AppExpr("/users.info", [VarExpr("x2")])
                ),
                ProjectionExpr(
                    ProjectionExpr(VarExpr("x3"), "profile"), 
                    "email"
                ),
            ]
        )

        self.assertEqual(results, [target])

def generator_suite():
    suite = unittest.TestSuite()
    suite.addTest(GeneratorTestCase('test_generate_projection'))
    suite.addTest(GeneratorTestCase('test_generate_filter'))
    suite.addTest(GeneratorTestCase('test_generate_let'))
    suite.addTest(GeneratorTestCase('test_generate_program'))
    return suite