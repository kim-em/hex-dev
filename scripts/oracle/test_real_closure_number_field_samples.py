"""Original embeddings, coefficient conversion, cells and multiplicity mutations."""
import copy
from pathlib import Path
import unittest

from scripts.oracle.real_closure_number_field_samples import parse_record, verify


class SampleTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        path = Path(__file__).resolve().parents[2]/'conformance-fixtures/HexRealClosure/number-field-samples.jsonl'
        cls.rows = [parse_record(line) for line in path.read_text().splitlines()]

    def test_actual_native_samples(self):
        self.assertEqual(verify(self.rows),4)

    def test_original_and_native_mutations(self):
        mutations = [
            lambda d:d.pop(),
            lambda d:d.reverse(),
            lambda d:d[0]['generator_head'].__setitem__(0,-3),
            lambda d:d[1].update(generator_lower=[1,1],generator_upper=[2,1]),
            lambda d:d[2]['inputs'][0][1].__setitem__(0,-8),
            lambda d:d[0]['packed_inputs'][0].__setitem__(1,-1),
            lambda d:d[0]['original_polynomials'][0][0][1].__setitem__(0,-2),
            lambda d:d[0]['polynomials'][0].append([]),
            lambda d:d[0]['context'].__setitem__(1,1),
            lambda d:d[1]['context'][2][0][4].append(99),
            lambda d:d[0]['sections'].pop(),
            lambda d:d[2]['sectors'].reverse(),
            lambda d:d[0]['sections'][0].update(member=False),
            lambda d:d[0]['sections'][0]['signs'].__setitem__(0,1),
            lambda d:d[0]['sections'][0].update(value=[]),
            lambda d:d[0]['sectors'][0]['cell'].update(lower=[2]),
            lambda d:d[0]['sectors'][1]['polynomials'][0].append([]),
            lambda d:d[3]['sectors'][0]['signs'].__setitem__(2,1),
            lambda d:d[2]['repeated_roots'][0].update(multiplicity=1),
            lambda d:d[1]['repeated_roots'].reverse(),
        ]
        for index,mutate in enumerate(mutations):
            with self.subTest(mutation=index):
                rows = copy.deepcopy(self.rows)
                mutate(rows)
                with self.assertRaises((ValueError,ArithmeticError)):
                    verify(rows)

    def test_duplicate_json_keys(self):
        with self.assertRaises(ValueError):
            parse_record('{"case":"cubic field","case":"middle cubic field"}')


if __name__ == '__main__':
    unittest.main()
