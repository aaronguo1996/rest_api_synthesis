import unittest
from tests.test_encoder import encoder_suite

if __name__ == '__main__':
    runner = unittest.TextTestRunner(verbosity=2)
    runner.run(encoder_suite())