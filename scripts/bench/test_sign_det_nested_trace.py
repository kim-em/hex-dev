"""Reject misleading nested coefficient-trace subjects."""
import copy
import json
import hashlib
from pathlib import Path
import tempfile
import unittest
from scripts.bench.sign_det_nested_trace import validate, check_retained


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
                           ('context', 0), ('lower', 'finite'), ('upper', 'negInf'),
                           ('standardReplayAccepted', False)]:
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

    def test_depth_two_and_operand_floor(self):
        rows = copy.deepcopy(self.rows)
        rows[2]['result']['coefficient'] = rows[0]['result']['coefficient']
        with self.assertRaises(ValueError):
            self.check(rows)
        rows = copy.deepcopy(self.rows)
        rows[2]['maxRationalSlots'] = 1
        with self.assertRaisesRegex(ValueError, 'omits'):
            self.check(rows)

    def test_retained_hashes(self):
        source = Path(__file__).resolve().parents[2] / 'reports/bench-results/sign-det-nested-trace/observations.jsonl'
        check_retained(source)
        initial = source.parent / 'initial/observations.jsonl'
        check_retained(initial)
        old = [json.loads(line) for line in initial.read_text().splitlines()]
        for a,b in zip(old,self.rows,strict=True):
            for key in ('coefficientCalls','maxNormalizedRatBits','maxRationalSlots'):
                self.assertEqual(a[key],b[key])
        changed = copy.deepcopy(self.rows)
        changed[0]['coefficientCalls'] += 1
        self.check(changed)
        meta = json.loads(source.with_name('metadata.json').read_text())
        self.path.with_name('source.patch').write_bytes(source.with_name('source.patch').read_bytes())
        self.path.with_name('metadata.json').write_text(json.dumps(meta))
        with self.assertRaisesRegex(ValueError, 'output hash'):
            check_retained(self.path)
        meta['observationsSha256'] = hashlib.sha256(self.path.read_bytes()).hexdigest()
        meta['sourceSha256'][next(iter(meta['sourceSha256']))] = '0'*64
        self.path.with_name('metadata.json').write_text(json.dumps(meta))
        with self.assertRaisesRegex(ValueError, 'source hash'):
            check_retained(self.path)
