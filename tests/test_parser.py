import unittest

from traces import parser

class ParserTestCase(unittest.TestCase):
    def test_hostname_sanitization(self):
        hostname = "api.slack.com"
        p = parser.LogParser(None, hostname)
        p.sanitize_hostname()
        self.assertEqual(p.hostname, "https://api.slack.com",
                        "Should prepend 'https' to the hostname")

        p.hostname = "https://api.slack.com/"
        p.sanitize_hostname()
        self.assertEqual(p.hostname, "https://api.slack.com",
                        "Should remove backslash from the hostname")

def suite():
    suite = unittest.TestSuite()
    suite.addTest(ParserTestCase('test_hostname_sanitization'))
    return suite