"""Reject corrupt corpus identities and skipped earlier prime candidates."""
import copy
import json
from pathlib import Path
import unittest

from scripts.bench.primality_factor_corpus import candidate, composite_witness, validate


class CorpusTests(unittest.TestCase):
    def setUp(self):
        source = Path(__file__).resolve().parents[2] / 'reports/primality/factor-policy/corpus-v3.json'
        self.corpus = copy.deepcopy(json.loads(source.read_text()))
        self.corpus['count_per_size'] = 4
        self.corpus['cases'] = [x for x in self.corpus['cases'] if x['index'] < 4]
        for x in self.corpus['cases']:
            x['split'] = 'tuning' if x['index'] == 0 else 'validation'
            x['id'] = f"{x['split']}-{x['bits']}-{x['index']}"

    def test_small_reproduction(self):
        validate(self.corpus)

    def test_corrupt_subject_and_split(self):
        for field, value in [('subject', self.corpus['cases'][0]['subject'] + 2),
                             ('split', 'validation')]:
            corpus = copy.deepcopy(self.corpus)
            corpus['cases'][0][field] = value
            with self.assertRaises(AssertionError):
                validate(corpus)

    def test_cannot_skip_a_prime(self):
        case = self.corpus['cases'][0]
        counter = case['counter'] + 1
        while True:
            n = candidate(case['bits'], case['index'], counter)
            if not any(composite_witness(n, a) for a in [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37]):
                break
            counter += 1
        case.update(counter=counter, subject=n)
        # The previous accepted prime is now an earlier candidate. Its absence
        # of a compositeness witness must reject this otherwise consistent row.
        with self.assertRaises(AssertionError):
            validate(self.corpus)


if __name__ == '__main__':
    unittest.main()
