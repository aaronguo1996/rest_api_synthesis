import unittest

from traces import parser, log

class ParserTestCase(unittest.TestCase):
    def test_hostname_sanitization_prepend(self):
        hostname = "api.slack.com"
        p = parser.LogParser(None, hostname, 'slack_web_openapi_v2.json')
        p.sanitize_hostname()
        self.assertEqual(p.hostname, "https://api.slack.com",
                        "Should prepend 'https' to the hostname")

    def test_hostname_sanitization_strip(self):
        hostname = "https://api.slack.com/"
        p = parser.LogParser(None, hostname, 'slack_web_openapi_v2.json')
        p.sanitize_hostname()
        self.assertEqual(p.hostname, "https://api.slack.com",
                        "Should remove backslash from the hostname")

class ResponseParameterTestCase(unittest.TestCase):
    def test_response_flatten_simple(self):
        param = log.ResponseParameter("GET", "result", "func", ["result"], {
            "a": "abc",
            "b": "abc"
        })
        params = param.flatten("#/components/schemas", [])
        self.assertEqual(params, [
            log.ResponseParameter("GET", "a", "func", ["result", "a"], "abc"),
            log.ResponseParameter("GET", "b", "func", ["result", "b"], "abc")
        ])

    def test_response_flatten_nested(self):
        param = log.ResponseParameter("GET", "result", "func", ["result"], {
            "a": {
                "c": "abc",
                "d": "abc"
            },
            "b": "abc"
        })
        params = param.flatten("#/components/schemas", [])
        self.assertEqual(params, [
            log.ResponseParameter("GET", "c", "func", ["result", "a", "c"], "abc"),
            log.ResponseParameter("GET", "d", "func", ["result", "a", "d"], "abc"),
            log.ResponseParameter("GET", "b", "func", ["result", "b"], "abc")
        ])

def param_suite():
    suite = unittest.TestSuite()
    suite.addTest(ResponseParameterTestCase('test_response_flatten_simple'))
    suite.addTest(ResponseParameterTestCase('test_response_flatten_nested'))
    return suite

def parser_suite():
    suite = unittest.TestSuite()
    suite.addTest(ParserTestCase('test_hostname_sanitization_prepend'))
    suite.addTest(ParserTestCase('test_hostname_sanitization_strip'))
    return suite