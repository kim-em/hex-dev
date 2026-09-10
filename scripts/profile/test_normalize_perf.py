import copy
import unittest
from scripts.profile.normalize_perf import normalize


class NormalizeTests(unittest.TestCase):
    def fixture(self):
        return {'meta': {'startTime': 0}, 'threads': [{'samples': {'time': [0.0, 1.25, 3.5]}}]}

    anchor = {'wall_ns_at_spawn': 1000 * 10**9, 'mono_ns_at_spawn': 120 * 10**9}

    def test_exact_offset(self):
        p = self.fixture()
        result = normalize(p, '1/1 123.000000000: cycles:\n1/1 123.001250000: cycles:\n1/1 123.003500000: cycles:\n', self.anchor)
        self.assertEqual(result['residual_ns'], 0)
        self.assertEqual(p['meta']['startTime'], 1003000)
        self.assertEqual(p['threads'][0]['samples']['time'], [0.0, 1.25, 3.5])

    def test_preserves_all_relative_timestamps(self):
        profile = self.fixture()
        profile['threads'][0].update(registerTime=0, unregisterTime=4,
            processStartupTime=-2, processShutdownTime=5,
            markers={'startTime': [1], 'endTime': [2]})
        profile['counters'] = [{'samples': {'time': [0, 2]}}]
        before = copy.deepcopy(profile)
        normalize(profile, '1/1 123.0:\n1/1 123.00125:\n1/1 123.0035:\n', self.anchor)
        self.assertEqual(profile['threads'], before['threads'])
        self.assertEqual(profile['counters'], before['counters'])

    def test_drift_rejected(self):
        with self.assertRaisesRegex(ValueError, 'disagree'):
            normalize(self.fixture(), '1/1 123.0:\n1/1 123.00125:\n1/1 123.0045:\n', self.anchor)

    def test_missing_samples_rejected(self):
        with self.assertRaisesRegex(ValueError, 'counts'):
            normalize(self.fixture(), '1/1 123.0:\n', self.anchor)


if __name__ == '__main__':
    unittest.main()
