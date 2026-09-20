"""Check pairing, protocol adjustment and incomplete-reference budget handling."""
import json
from pathlib import Path
import tempfile
import unittest
from scripts.bench.rank_analyze import curve, budgets


class Analysis(unittest.TestCase):
    def test_pairing(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            journal = []
            for block in range(6):
                label = f'{block}-compareIntDense16'
                journal.append({'label': label, 'exit_code': 0, 'output_errors': []})
                measurements = [
                    {'function': 'Hex.RankBench.Comparison.Int.Dense.native16', 'median_nanos': 100},
                    {'function': 'Hex.RankBench.Comparison.Int.Dense.external16', 'median_nanos': 40}]
                for measurement in measurements:
                    measurement.update(hashes_agree=True, expected_hash_check={'status': 'match'})
                if block % 2:
                    measurements.reverse()
                (root / (label + '.json')).write_text(json.dumps({'results': measurements}))
            (root / 'commands.jsonl').write_text('\n'.join(map(json.dumps, journal)) + '\n')
            result = curve(root, 10)['curves'][0]
            self.assertTrue(result['complete'])
            self.assertTrue(result['eligible'])
            self.assertEqual(result['raw_ratio'], 2.5)
            self.assertAlmostEqual(result['adjusted_ratio'], 100 / 30)
            (root / 'commands.jsonl').write_text(json.dumps(journal[0]) + '\n')
            self.assertFalse(curve(root, 10)['curves'][0]['complete'])

    def test_budget_requires_all_references(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            (root / 'commands.jsonl').write_text(json.dumps({'label': 'case', 'exit_code': 0}) + '\n')
            (root / 'case.json').write_text(json.dumps({'results': [{
                'function': 'Hex.RankBench.runMvCert4', 'median_nanos': 100,
                'hashes_agree': True, 'expected_hash_check': {'status': 'match'}}]}))
            policy = {'margin': 2, 'operation_reference': {'Cert': ['rank', 'second']}}
            refs = {'curves': [{'blocks': [{'external_case': 'Hex.RankBench.Comparison.Mv.Full.external4'}],
                'complete': True, 'external_ns': 30, 'label': 'rank'}]}
            stages = {'curves': []}
            self.assertEqual(budgets(refs, stages, root, policy)[0]['verdict'], 'pending references')
            stages['curves'].append({'blocks': [{'external_case': 'Hex.RankBench.Comparison.Mv.Full.second4'}],
                'complete': True, 'external_ns': 30, 'label': 'second'})
            result = budgets(refs, stages, root, policy)[0]
            self.assertEqual(result['budget_ns'], 120)
            self.assertEqual(result['verdict'], 'pass')
            stages['curves'][0]['external_ns'] = 10
            self.assertEqual(budgets(refs, stages, root, policy)[0]['verdict'], 'fail')
