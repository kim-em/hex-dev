"""Exact input, embedding, multiplicity and selected-root regression checks."""
import copy
import json
from pathlib import Path
import unittest
from scripts.oracle.real_closure_metitarski_scaling import check,DEGREES

ROOT = Path(__file__).resolve().parents[2]


class MetitarskiScalingTests(unittest.TestCase):
    def rows(self):
        return [json.loads(line) for line in
                (ROOT/'conformance-fixtures/HexRealClosure/metitarski-scaling.jsonl').read_text().splitlines()]

    def test_original_ladder(self):
        rows = self.rows()
        self.assertEqual([r['degree'] for r in rows],list(DEGREES))
        for row in rows:
            self.assertEqual(check(row)['real_roots'],1)

    def test_semantic_mutations(self):
        mutations = [
            lambda r: r.__setitem__('degree',7),
            lambda r: r['first_coefficients'][0].__setitem__(0,592705),
            lambda r: r.__setitem__('multiplicity',2),
            lambda r: r.__setitem__('equation_sign',1),
            lambda r: r.__setitem__('root_replay',False),
            lambda r: r['first'].__setitem__(0,[1]),
            lambda r: r['first'][1][0].__setitem__(1,2745),
            lambda r: r['first'].__setitem__(2,[2]),
            lambda r: r['head'][0].__setitem__(1,-1),
            lambda r: r['head'].__setitem__(-1,[]),
            lambda r: r['root'].__setitem__(0,[1]),
            lambda r: r['root'].__setitem__(2,[2]),
            lambda r: r['root'].__setitem__(4,[0]),
            lambda r: (r['root'].__setitem__(4,[1]),r['root'].__setitem__(5,[-1])),
        ]
        for mutate in mutations:
            with self.subTest(mutation=mutate):
                row = copy.deepcopy(self.rows()[-1])
                mutate(row)
                with self.assertRaises(ValueError):check(row)


if __name__ == '__main__':unittest.main()
