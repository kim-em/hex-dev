"""Reject altered normalization traces even when their selected sign stays positive."""
import copy
import unittest
import json
from pathlib import Path
from scripts.oracle.real_closure_normalization import verify


class TraceTests(unittest.TestCase):
    def setUp(self):
        fixture = Path(__file__).resolve().parents[2] / 'conformance-fixtures/HexRealClosure/normalization.jsonl'
        self.row = json.loads(fixture.read_text().splitlines()[0])

    def test_exact_trace(self):
        self.assertTrue(verify(self.row)['checked'])

    def test_positive_mutations(self):
        failures = dict(constant='stored polynomial does not match', working='different defining polynomial',
            degree='wrong stored degree', fraction='noncanonical rational', equality='selected values or signs',
            sign='selected values or signs', flag='distinct normalization policies',
            head='different defining polynomial', steps='wrong trace parameter', prefix='stored prefix')
        for change, message in failures.items():
            with self.subTest(change=change):
                row = copy.deepcopy(self.row)
                if change == 'constant': row['eager']['coefficients'][0] = [21,4]
                elif change == 'working': row['working_head'][0] = [-1,1]
                elif change == 'degree': row['clean']['degree'] = 3
                elif change == 'fraction': row['eager']['coefficients'][0] = [34,8]
                elif change == 'equality': row['equal_at_root'] = False
                elif change == 'sign': row['eager']['sign'] = -1
                elif change == 'flag': row['eager']['clean'] = True
                elif change == 'head': row['head'][-1] = [3,1]
                elif change == 'steps': row['steps'] = 3
                else: row['prefixes'][1]['clean']['coefficients'][0] = [2,1]
                with self.assertRaisesRegex(ValueError, message): verify(row)


if __name__ == '__main__': unittest.main()
