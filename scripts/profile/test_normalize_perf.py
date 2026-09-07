import unittest
from scripts.profile.normalize_perf import normalize


class NormalizeTests(unittest.TestCase):
    def fixture(self):
        return {'meta': {}, 'threads': [{'samples': {'time': [0.0, 1.25, 3.5]}}]}

    def test_exact_offset(self):
        p = self.fixture()
        result = normalize(p, '1/1 123.000000000: cycles:\n1/1 123.001250000: cycles:\n1/1 123.003500000: cycles:\n')
        self.assertEqual(result['residual_ns'], 0)
        self.assertEqual(p['threads'][0]['samples']['time'], [123000, 123001.25, 123003.5])

    def test_drift_rejected(self):
        with self.assertRaisesRegex(ValueError, 'disagree'):
            normalize(self.fixture(), '1/1 123.0:\n1/1 123.00125:\n1/1 123.0045:\n')

    def test_missing_samples_rejected(self):
        with self.assertRaisesRegex(ValueError, 'counts'):
            normalize(self.fixture(), '1/1 123.0:\n')


if __name__ == '__main__':
    unittest.main()
