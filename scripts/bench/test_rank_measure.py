"""Fail closed on lost or incorrect measurements without aborting a schedule."""
import json
from pathlib import Path
import tempfile
import unittest
from scripts.bench.rank_measure import output_errors


class ExportValidation(unittest.TestCase):
    def check(self, content):
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / 'export.json'
            if content is not None:
                path.write_text(content)
            return output_errors(path)

    def test_malformed_exports(self):
        for content in (None, '{', '{}', '{"results": []}', '{"results": [{}]}'):
            self.assertTrue(self.check(content), content)

    def test_parametric_output(self):
        measurement = {'function': 'Hex.RankBench.runCheckRankDense', 'kind': 'parametric',
                       'points': [{'param': 16, 'status': 'ok', 'result_hash': '0xb'}]}
        self.assertFalse(self.check(json.dumps({'results': [measurement]})))
        measurement['points'].append({'param': 16, 'status': 'ok', 'result_hash': '0x0'})
        self.assertTrue(self.check(json.dumps({'results': [measurement]})))

    def test_rank_varies_with_dimension(self):
        measurement = {'function': 'Hex.RankBench.Second.deficientHalf', 'kind': 'parametric',
                       'points': [{'param': n, 'status': 'ok', 'result_hash': hex(n // 2)}
                                  for n in (16, 32, 64)]}
        self.assertFalse(self.check(json.dumps({'results': [measurement]})))

    def test_fixed_failure(self):
        measurement = {'function': 'fixed', 'kind': 'fixed', 'hashes_agree': True,
                       'expected_hash_check': {'status': 'mismatch'},
                       'points': [{'status': 'ok'}]}
        self.assertTrue(self.check(json.dumps({'results': [measurement]})))
