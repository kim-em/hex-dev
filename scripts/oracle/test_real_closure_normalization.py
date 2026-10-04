"""Reject altered normalization traces even when their selected sign stays positive."""
import copy
import unittest
from scripts.oracle.real_closure_normalization import verify


class TraceTests(unittest.TestCase):
    def setUp(self):
        self.row = dict(degree=2, steps=4, head=[[-1,1],[0,1],[2,1]],
            working_head=[[-1,2],[0,1],[1,1]], equal_at_root=True,
            clean=dict(coefficients=[[1,1],[4,1],[6,1],[4,1],[1,1]],
                       degree=4, clean=True, sign=1),
            eager=dict(coefficients=[[17,4],[6,1]], degree=1, clean=False, sign=1))

    def test_exact_trace(self):
        self.assertTrue(verify(self.row)['checked'])

    def test_positive_mutations(self):
        for change in ('constant', 'working', 'degree', 'fraction', 'equality'):
            with self.subTest(change=change):
                row = copy.deepcopy(self.row)
                if change == 'constant': row['eager']['coefficients'][0] = [21,4]
                elif change == 'working': row['working_head'][0] = [-1,1]
                elif change == 'degree': row['clean']['degree'] = 3
                elif change == 'fraction': row['eager']['coefficients'][0] = [34,8]
                else: row['equal_at_root'] = False
                with self.assertRaises(ValueError): verify(row)


if __name__ == '__main__': unittest.main()
