"""Reject misleading nested coefficient-trace subjects."""
import copy
import json
from pathlib import Path
import tempfile
import unittest
from scripts.bench.sign_det_nested_trace import validate


class NestedTraceTest(unittest.TestCase):
    def setUp(self):
        source = Path(__file__).resolve().parents[2] / 'reports/bench-results/sign-det-nested-trace/observations.jsonl'
        self.rows = [json.loads(line) for line in source.read_text().splitlines()]
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.path = Path(self.temp.name) / 'records.jsonl'

    def check(self, rows):
        self.path.write_text('\n'.join(map(json.dumps, rows)))
        return validate(self.path)

    def test_retained(self):
        self.assertEqual(len(self.check(self.rows)), 4)

    def test_reject_changed_subjects(self):
        for key, value in [('head', [[1,1]]), ('queryPolynomials', []),
                           ('coefficient', {'num': [], 'den': [[1,1]]}),
                           ('entries', [[[1]*4,2]]), ('entries', [[[True]*4,1]]),
                           ('context', 0), ('standardReplayAccepted', False)]:
            with self.subTest(key=key), self.assertRaises(ValueError):
                rows = copy.deepcopy(self.rows)
                rows[0]['result'][key] = value
                self.check(rows)

    def test_reject_missing_observations(self):
        for key in ('coefficientCalls','maxNormalizedRatBits','maxRationalSlots'):
            for value in (0, True, 1.0):
                with self.subTest(key=key,value=value), self.assertRaises(ValueError):
                    rows = copy.deepcopy(self.rows)
                    rows[0][key] = value
                    self.check(rows)
        with self.assertRaises(ValueError):
            self.check(self.rows[:-1])
