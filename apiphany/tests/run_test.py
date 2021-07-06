from tests.test_generator import generator_suite
from tests.test_analyzer import analyzer_suite
from tests.test_synthesizer import synthesizer_suite
import unittest
from tests.test_analyzer import analyzer_suite
from tests.test_encoder import encoder_suite
from tests.test_synthesizer import synthesizer_suite
from tests.test_generator import generator_suite

ENCODER_SUITE = "encoder"
SYNTHESIZER_SUITE = "synthesizer"
ANALYZER_SUITE = "analyzer"
GENERATOR_SUITE = "generator"

def run_test(suites, doc, config, analyzer):
    runner = unittest.TextTestRunner(verbosity=2)
    
    if ENCODER_SUITE in suites:
        runner.run(encoder_suite())

    if SYNTHESIZER_SUITE in suites:
        runner.run(synthesizer_suite(doc, config, analyzer))

    if ANALYZER_SUITE in suites:
        runner.run(analyzer_suite(analyzer))

    if GENERATOR_SUITE in suites:
        runner.run(generator_suite())