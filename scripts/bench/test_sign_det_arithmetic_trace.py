"""Reject changed trace subjects independently of the Lean checks."""
import copy
import json
import hashlib
from pathlib import Path
import tempfile
import unittest
from scripts.bench.sign_det_arithmetic_trace import validate, check_retained


class ArithmeticTraceTest(unittest.TestCase):
    def setUp(self):
        source = Path(__file__).resolve().parents[2] / 'reports/bench-results/sign-det-arithmetic-trace/observations.jsonl'
        self.rows = [json.loads(line) for line in source.read_text().splitlines()]
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.path = Path(self.temp.name) / 'records.jsonl'

    def check(self, rows):
        self.path.write_text('\n'.join(map(json.dumps, rows)))
        return validate(self.path)

    def test_retained(self):
        self.assertEqual(len(self.check(self.rows)), 3)

    def test_reject_changed_root_subject(self):
        for key, value in [('left', [[-3, 1], [0, 1], [1, 1]]),
                           ('factor', [[1, 1]]), ('commonHead', [[1, 1]]),
                           ('leftInterval', [[-2, 1], [0, 1]]),
                           ('sameInterval', [[0, 1], [1, 1]]),
                           ('sameInterval', [[0, 1], [4, 1]]),
                           ('strictCommonHead', [[1,1]]), ('strictFactor', [[1,1]]),
                           ('lastInterval', [[2, 1], [3, 1]]),
                           ('strictOrder', 'gt'), ('context', 0),
                           ('standardReplayAccepted', False)]:
            with self.subTest(key=key), self.assertRaises(ValueError):
                rows = copy.deepcopy(self.rows)
                rows[0]['result'][key] = value
                self.check(rows)

    def test_reject_missing_observations(self):
        for key, value in [('coefficientCalls', 0), ('coefficientCalls', True),
                           ('maxNormalizedBits', 0), ('maxNormalizedBits', True),
                           ('temporaryBitBound', 1), ('operationCalls', [1]*8)]:
            with self.subTest(key=key), self.assertRaises(ValueError):
                rows = copy.deepcopy(self.rows)
                rows[0][key] = value
                self.check(rows)
        with self.assertRaises(ValueError):
            self.check(self.rows[:-1])

    def test_retained_hashes(self):
        source = Path(__file__).resolve().parents[2] / 'reports/bench-results/sign-det-arithmetic-trace/observations.jsonl'
        check_retained(source)
        initial = source.parent / 'initial/observations.jsonl'
        check_retained(initial)
        old = [json.loads(line) for line in initial.read_text().splitlines()]
        for a,b in zip(old,self.rows,strict=True):
            for key in ('coefficientCalls','maxNormalizedBits','temporaryBitBound'):
                self.assertEqual(a[key],b[key])
        changed = copy.deepcopy(self.rows)
        changed[0]['coefficientCalls'] += 1
        changed[0]['operationCalls'][0] += 1
        self.check(changed)
        meta = json.loads(source.with_name('metadata.json').read_text())
        self.path.with_name('source.patch').write_bytes(source.with_name('source.patch').read_bytes())
        self.path.with_name('metadata.json').write_text(json.dumps(meta))
        with self.assertRaisesRegex(ValueError, 'output hash'):
            check_retained(self.path)
        meta['observationsSha256'] = hashlib.sha256(self.path.read_bytes()).hexdigest()
        first = next(iter(meta['sourceSha256']))
        meta['sourceSha256'][first] = '0'*64
        self.path.with_name('metadata.json').write_text(json.dumps(meta))
        with self.assertRaisesRegex(ValueError, 'source hash'):
            check_retained(self.path)

    def test_archive_patch_and_base(self):
        source = Path(__file__).resolve().parents[2] / 'reports/bench-results/sign-det-arithmetic-trace/observations.jsonl'
        self.path.write_bytes(source.read_bytes())
        patch = source.with_name('source.patch').read_bytes()
        meta = json.loads(source.with_name('metadata.json').read_text())
        self.path.with_name('source.patch').write_bytes(patch + b'changed')
        self.path.with_name('metadata.json').write_text(json.dumps(meta))
        with self.assertRaisesRegex(ValueError, 'patch hash'):
            check_retained(self.path)
        changed = patch.replace(b'+private def bits (q : Rat)', b'+private def bitsChanged (q : Rat)',1)
        self.assertNotEqual(changed,patch)
        self.path.with_name('source.patch').write_bytes(changed)
        meta['sourcePatch']['sha256'] = hashlib.sha256(changed).hexdigest()
        self.path.with_name('metadata.json').write_text(json.dumps(meta))
        with self.assertRaisesRegex(ValueError, 'source hash'):
            check_retained(self.path)
        self.path.with_name('source.patch').write_bytes(patch)
        meta = json.loads(source.with_name('metadata.json').read_text())
        meta['sourcePatch']['file'] = '../source.patch'
        self.path.with_name('metadata.json').write_text(json.dumps(meta))
        with self.assertRaisesRegex(ValueError, 'archive path'):
            check_retained(self.path)
        meta['sourcePatch']['file'] = 'source.patch'
        for base in ['HEAD',meta['sourceRevision']]:
            meta['baseRevision'] = base
            self.path.with_name('metadata.json').write_text(json.dumps(meta))
            with self.assertRaisesRegex(ValueError, 'main'):
                check_retained(self.path)
