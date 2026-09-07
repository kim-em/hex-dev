#!/usr/bin/env python3
"""Protocol conversion regressions, without requiring FLINT or SymPy."""

import unittest
from unittest.mock import patch

from scripts.bench.rationalfn_flint import ROOT, decode, encode, git_state, integer_pair


class RationalFnProtocolTests(unittest.TestCase):
    def test_checkout_provenance(self):
        with patch("scripts.bench.rationalfn_flint.subprocess.check_output",
                   side_effect=["abc123\n", " M changed\n"]) as run:
            self.assertEqual(git_state(), {"commit": "abc123", "git_dirty": True})
            self.assertTrue(all(call.kwargs["cwd"] == ROOT for call in run.call_args_list))

    def test_shared_denominator(self):
        pair = {"num": [[-1, 2], [2, 3]], "den": [[3, 4], [1, 1]]}
        self.assertEqual(integer_pair(pair), [[-6, 8], [9, 12]])
        self.assertEqual(encode(pair), "2 -6 8 2 9 12")
        result, seconds, sizes = decode("pair 0.125 2 -6 8 2 9 12")
        self.assertEqual(result, pair)
        self.assertEqual(seconds, 0.125)
        self.assertEqual(sizes["flint_bits"], [4, 4])
        self.assertEqual(sizes["hex_bits"], [2, 3])

    def test_negative_leading_coefficient(self):
        result, _, _ = decode("pair 0 1 3 2 2 -4")
        self.assertEqual(result, {"num": [[-3, 4]], "den": [[-1, 2], [1, 1]]})

    def test_zero(self):
        pair = {"num": [], "den": [[1, 1]]}
        self.assertEqual(integer_pair(pair), [[], [1]])
        result, _, sizes = decode("pair 0 0 1 1")
        self.assertEqual(result, pair)
        self.assertEqual(sizes["flint_lengths"], [0, 1])
        self.assertEqual(sizes["flint_bits"], [0, 1])

    def test_scalar_results(self):
        self.assertEqual(decode("bool 0.1 0"), (False, 0.1, None))
        self.assertEqual(decode("bool 0.1 1"), (True, 0.1, None))
        self.assertEqual(decode("value 0.1 -2 3"), ([-2, 3], 0.1, None))
        self.assertEqual(decode("none 0.1"), (None, 0.1, None))
        self.assertEqual(decode("rejected 0"), (None, None, None))

    def test_reject_trailing_output(self):
        for line in ("bool 0 1 junk", "none 0 junk", "pair 0 0 1 1 junk"):
            with self.subTest(line=line), self.assertRaises(ValueError):
                decode(line)

    def test_reject_unknown_response(self):
        with self.assertRaises(ValueError):
            decode("unknown 0")


if __name__ == "__main__":
    unittest.main()
