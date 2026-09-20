"""Persistent rank protocol and exact-domain regression checks."""
import json
from pathlib import Path
import subprocess
import sys
import unittest


class RankProtocol(unittest.TestCase):
    def test_persistent_domains_and_errors(self):
        driver = Path(__file__).with_name('rank_bench.py')
        records = [
            ({'kind': 'matrix', 'rows': [[1, 2], [2, 4]]}, 1),
            ({'kind': 'ratmatrix', 'rows': [[[1, 2], [1, 3]], [[3, 2], [1, 1]]]}, 1),
            # Generic rank over QQ[x] is not rank after evaluating at zero.
            ({'kind': 'polymatrix', 'field': {'type': 'Rat'}, 'rows': 1, 'cols': 1,
              'entries': [[{'num': [0, 1], 'den': [1, 2]}]]}, 1),
            ({'kind': 'mvpolymatrix', 'arity': 2, 'rows': 2, 'cols': 2,
              'entries': [[[[[1, 0], 1]], [[[0, 1], 1]]],
                          [[[[2, 0], 1]], [[[1, 1], 1]]]]}, 1),
            ({'kind': 'matrix', 'rows': [[1, 0], [0, 1]]}, 2),
        ]
        requests = [{'op': 'rank'}]
        expected = [{'ok': False}]
        for record, rank in records:
            requests += [{'op': 'prepare', 'record': record}, {'op': 'rank'}, {'op': 'rank'}]
            expected += [{'ok': True, 'result': True}, {'ok': True, 'result': rank}, {'ok': True, 'result': rank}]
        malformed = [
            {'kind': 'matrix', 'rows': [[1], [2, 3]]},
            {'kind': 'polymatrix', 'field': {'type': 'Rat'}, 'rows': 1, 'cols': 1,
             'entries': [[{'num': [1, 2], 'den': [1]}]]},
            {'kind': 'polymatrix', 'field': {'type': 'Rat'}, 'rows': 1, 'cols': 1,
             'entries': [[{'num': [1], 'den': [0]}]]},
            {'kind': 'mvpolymatrix', 'arity': 2, 'rows': 1, 'cols': 1,
             'entries': [[[[[1], 2]]]]},
        ]
        for record in malformed:
            requests += [{'op': 'prepare', 'record': record}, {'op': 'rank'}]
            expected += [{'ok': False}, {'ok': False}]
        requests += [{'op': 'overhead'}]
        expected += [{'ok': True, 'result': 0}]
        payload = '\n'.join(json.dumps(x) for x in requests) + '\n'
        result = subprocess.run([sys.executable, str(driver)], input=payload,
                                text=True, capture_output=True, check=True, timeout=30)
        replies = [json.loads(line) for line in result.stdout.splitlines()]
        self.assertEqual(len(replies), len(expected))
        for reply, want in zip(replies, expected):
            self.assertEqual(reply['ok'], want['ok'], reply)
            if want['ok']:
                self.assertEqual(reply['result'], want['result'])
            else:
                self.assertTrue(reply['error'])


if __name__ == '__main__':
    unittest.main()
