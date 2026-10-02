"""Exact polynomial second-pass and checker protocol regression tests."""
import json
from pathlib import Path
import subprocess
import sys
import unittest


class Stages(unittest.TestCase):
    def replies(self, requests):
        result = subprocess.run([sys.executable, str(Path(__file__).with_name('rank_bench.py'))],
            input='\n'.join(map(json.dumps, requests)) + '\n', text=True,
            capture_output=True, check=True, timeout=30)
        return [json.loads(line) for line in result.stdout.splitlines()]

    def test_identities_and_reset(self):
        for kind, x, one, zero, extra in [
            ('polymatrix', {'num': [0, 1], 'den': [1, 1]},
             {'num': [1], 'den': [1]}, {'num': [], 'den': []}, {'field': {'type': 'Rat'}}),
            ('mvpolymatrix', [[[1, 0], 1]], [[[0, 0], 1]], [], {'arity': 2}),
        ]:
            record = {'kind': kind, 'rows': 2, 'cols': 2, 'entries': [[x, zero], [x, zero]], **extra}
            cert = {'rank': 1, 'rows': [0], 'cols': [0], 'adj': [[one]], 'denom': x}
            requests = [{'op': 'second'}, {'op': 'check'},
                {'op': 'prepare', 'record': record, 'certificate': cert},
                {'op': 'second'}, {'op': 'check'}, {'op': 'second'}, {'op': 'check'},
                {'op': 'prepare', 'record': record, 'certificate': {**cert, 'adj': [[zero]]}},
                {'op': 'check'},
                {'op': 'prepare', 'record': record}, {'op': 'rank'}, {'op': 'check'},
                {'op': 'prepare', 'record': record, 'certificate': {**cert, 'rows': [5]}},
                {'op': 'rank'}, {'op': 'second'}, {'op': 'check'}]
            replies = self.replies(requests)
            self.assertEqual([r['ok'] for r in replies],
                             [False, False, True, True, True, True, True, True,
                              True, True, True, False, False, False, False, False])
            self.assertEqual([replies[i]['result'] for i in (3, 4, 5, 6, 8, 10)],
                             [1, True, 1, True, False, 1])

    def test_certificate_encoding(self):
        record = {'kind': 'polymatrix', 'field': {'type': 'Rat'}, 'rows': 1, 'cols': 1,
                  'entries': [[{'num': [1], 'den': [1]}]]}
        for bad in ({'num': [1, 2], 'den': [1]}, {'num': [1], 'den': [0]}):
            cert = {'rank': 1, 'rows': [0], 'cols': [0], 'adj': [[bad]],
                    'denom': {'num': [1], 'den': [1]}}
            self.assertFalse(self.replies([{'op': 'prepare', 'record': record, 'certificate': cert}])[0]['ok'])
