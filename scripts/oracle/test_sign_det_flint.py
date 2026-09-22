"""Adversarial checks of the independent sign-table oracle itself."""
import copy
import tempfile
import unittest
from pathlib import Path

from scripts.oracle import sign_det_flint as oracle
from scripts.oracle.common import OracleMismatch


def poly(*coefficients):
    return [[c, 1] for c in coefficients]


def case(head=None, queries=None, lower="-inf", upper="+inf"):
    return {"schema": 1, "head": head if head is not None else poly(-1, 0, 1),
            "queries": queries if queries is not None else [poly(0, 1)],
            "lower": lower, "upper": upper}


def output(table):
    return {"status": "ok", "replay": True, "table": table}


def row(signs, count=1):
    return {"signs": signs, "count": count}


class ExactSigns(unittest.TestCase):
    def test_empty_zero_duplicate_and_shared_queries(self):
        self.assertEqual(oracle.expected_table(case(queries=[])), [row([], 2)])
        queries = [poly(), poly(1), poly(0, 1), poly(0, 1), poly(-1, 0, 1)]
        self.assertEqual(oracle.expected_table(case(queries=queries)),
                         [row([0, 1, -1, -1, 0]), row([0, 1, 1, 1, 0])])
        self.assertEqual(oracle.expected_table(case(head=poly(0, 1))), [row([0])])

    def test_irrational_roots_exactly(self):
        queries = [poly(0, 1), poly(-2, 0, 1), poly(-3, 0, 1), poly(-1, 1)]
        expected = [row([-1, 0, -1, -1]), row([1, 0, -1, 1])]
        self.assertEqual(oracle.expected_table(case(head=poly(-2, 0, 1), queries=queries)), expected)
        self.assertEqual(oracle.expected_table(case(head=poly(2, 0, -1), queries=queries)), expected)

    def test_rational_scaling_and_open_interval(self):
        data = case(head=[[-1, 6], [0, 1], [1, 6]], queries=[[[0, 1], [-1, 10]]], lower=[0, 1])
        self.assertEqual(oracle.expected_table(data), [row([-1])])
        data["upper"] = [1, 1]
        self.assertIsNone(oracle.expected_table(data))

    def test_root_free_and_constant(self):
        for head in (poly(1, 0, 1), poly(3), poly(-2)):
            for queries in ([], [poly(), poly(0, 1)]):
                self.assertEqual(oracle.expected_table(case(head=head, queries=queries)), [])

    def test_invalid_domains_before_shortcuts(self):
        for head in (poly(), poly(0, 0), poly(1, -2, 1)):
            self.assertIsNone(oracle.expected_table(case(head=head, queries=[])))
        for lo, hi in (("-inf", "-inf"), ("+inf", "+inf"), ("+inf", "-inf"),
                       ([0, 1], "-inf"), ("+inf", [0, 1]), ([0, 1], [0, 1]),
                       ([2, 1], [-2, 1]), ([-1, 1], "+inf"), ("-inf", [1, 1])):
            self.assertIsNone(oracle.expected_table(case(queries=[], lower=lo, upper=hi)))

    def test_sparse_completeness_not_just_total(self):
        expected = oracle.expected_table(case())
        oracle.check_output(output([row([-1]), row([1])]), expected, 1)
        for table in ([row([1], 2)], [], [row([-1], 2)], [row([-1]), row([-1])],
                      [row([1]), row([-1])], [row([-1]), row([0], 0), row([1])],
                      [row([-1], -1), row([1], 3)], [row([-1], True), row([1])],
                      [row([False]), row([1])], [row([-1, 0]), row([1])]):
            with self.subTest(table=table), self.assertRaises(OracleMismatch):
                oracle.check_output(output(table), expected, 1)

    def test_result_modes_and_replay_are_all_checked(self):
        data = case()
        good = output([row([-1]), row([1])])
        data.update(reduced=good, direct=good, reference=good, algebraic=good["table"])
        record = {"kind": "result", "lib": "HexSignDet", "case": "test", "op": "table", "value": data}
        oracle.check_record(record)
        for mode in ("reduced", "direct", "reference"):
            bad = copy.deepcopy(record)
            bad["value"][mode]["table"] = [row([1], 2)]
            with self.subTest(mode=mode), self.assertRaises(OracleMismatch):
                oracle.check_record(bad)
        bad = copy.deepcopy(record)
        bad["value"]["algebraic"][0]["count"] = True
        with self.assertRaises(OracleMismatch):
            oracle.check_record(bad)
        bad = copy.deepcopy(record)
        del bad["value"]["reference"]
        with self.assertRaises(OracleMismatch):
            oracle.check_record(bad)
        for replacement in ({"status": "error"}, {"status": "invalid-domain"},
                            {**good, "replay": False}):
            with self.subTest(result=replacement), self.assertRaises(OracleMismatch):
                oracle.check_output(replacement, [row([-1]), row([1])], 1)

    def test_empty_stream_is_failure(self):
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / "empty.jsonl"
            path.write_text("")
            with self.assertRaises(OracleMismatch):
                oracle.check(path, Path(directory) / "failures", "ci", 10377)


if __name__ == "__main__":
    unittest.main()
