import unittest
from analyzer.analyzer import *
# from analyzer.entry import DocEntry, RequestParameter, ResponseParameter

class AnalyzerTestCase(unittest.TestCase):
    @staticmethod
    def _setUp(analyzer):
        AnalyzerTestCase._analyzer = analyzer

    def setUp(self):
        self._analyzer = AnalyzerTestCase._analyzer
        self.maxDiff = None

    def test_find_same_type(self):
        typ = SchemaType("objs_user.id", None)
        param = ResponseParameter(
            "", "", "projection(objs_user, id)", 
            [], True, 0, typ, None)
        param = self._analyzer.find_same_type(param)
        self.assertNotEqual(param.type, None)
        self.assertEqual(param.type.name, "defs_user_id")
        self.assertNotEqual(param.type.schema, None)

        typ = SchemaType("objs_user.profile.email", None)
        param = ResponseParameter(
            "", "", "projection(objs_user.profile, email)", 
            [], True, 0, typ, None)
        param = self._analyzer.find_same_type(param)
        self.assertNotEqual(param.type, None)
        self.assertEqual(param.type.name, "objs_user.profile.email")
        self.assertNotEqual(param.type.schema, None)

        typ = SchemaType("objs_conversation.creator", None)
        param = ResponseParameter(
            "", "", "projection(objs_conversation, creator)", 
            [], True, 0, typ, None)
        param = self._analyzer.find_same_type(param)
        self.assertNotEqual(param.type, None)
        self.assertEqual(param.type.name, "defs_user_id")
        self.assertNotEqual(param.type.schema, None)

        typ = SchemaType("objs_conversation.id", None)
        param = ResponseParameter(
            "", "", "projection(objs_conversation, id)", 
            [], True, 0, typ, None)
        param = self._analyzer.find_same_type(param)
        self.assertNotEqual(param.type, None)
        self.assertEqual(param.type.name, "defs_dm_id")
        self.assertNotEqual(param.type.schema, None)

        typ = SchemaType("objs_conversation.priority", None)
        param = ResponseParameter(
            "", "", "projection(objs_conversation, priority)", 
            [], True, 0, typ, None)
        param = self._analyzer.find_same_type(param)
        self.assertNotEqual(param.type, None)
        self.assertEqual(param.type.name, "objs_conversation.priority")
        self.assertNotEqual(param.type.schema, None)

        typ = SchemaType("objs_user.profile.fields", None)
        param = ResponseParameter(
            "", "", "projection(objs_user.profile, fields)", 
            [], True, 0, typ, None)
        param = self._analyzer.find_same_type(param)
        self.assertNotEqual(param.type, None)
        self.assertEqual(param.type.name, "objs_user.profile.fields")
        self.assertEqual(param.type.schema, None)

    def test_set_type(self):
        # case I: the parameter is the same as that in the graph
        param = RequestParameter(
            "GET", "user", "/users.info", 
            True, None, None)
        self._analyzer.set_type(param)
        self.assertNotEqual(param.type, None)
        self.assertEqual(param.type.name, "defs_user_id")

        # case II: the parameter is an object
        param = ResponseParameter(
            "GET", "user", "/users.info", 
            ["user"], True, 1, None, None)
        self._analyzer.set_type(param)
        self.assertNotEqual(param.type, None)
        self.assertEqual(param.type.name, "objs_user")

        # case III: the parameter is not in the graph
        param = ResponseParameter(
            "GET", "user", "/users.members", 
            ["user"], True, 1, None, None)
        self._analyzer.set_type(param)
        self.assertNotEqual(param.type, None)
        self.assertEqual(param.type.name, str(param))

        param = ResponseParameter(
            "GET", "response_metadata", "/conversations.list", 
            ["response_metadata"], False, 0, None, None)
        self._analyzer.set_type(param)
        self.assertEqual(param.type.name, "objs_response_metadata")

def analyzer_suite(analyzer):
    AnalyzerTestCase._setUp(analyzer)
    suite = unittest.TestSuite()
    suite.addTest(AnalyzerTestCase('test_find_same_type'))
    suite.addTest(AnalyzerTestCase('test_set_type'))
    return suite