"""Adversarial checks of the independent sign-table oracle itself."""
import copy
import json
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
        with self.assertRaisesRegex(OracleMismatch, "serialization order"):
            oracle.check_output(output([row([1]), row([-1])]), expected, 1)
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

    def fixture_record(self, name):
        with oracle.DEFAULT_FIXTURE.open() as stream:
            return next(record for line in stream if (record := json.loads(line))["case"] ==
                        name)

    def test_descriptor_order_and_selected_signs(self):
        for name in ("cubic-left", "cubic-center", "negative-cubic", "irrational", "singleton-empty"):
            with self.subTest(name=name):
                record = self.fixture_record("descriptor/" + name)
                oracle.check_record(record)
                for key in ("completion", "selected"):
                    bad = copy.deepcopy(record)
                    signs = bad["value"]["validation"][key]["signs"]
                    signs[0] = 1 if signs[0] != 1 else -1
                    with self.assertRaises(OracleMismatch):
                        oracle.check_record(bad)
        record = self.fixture_record("descriptor/" + "cubic-left")
        roots = record["value"]["roots"]["roots"]
        self.assertEqual([r["signs"] for r in roots], [[1, -1, 1], [-1, 0, 1], [1, 1, 1]])
        record["value"]["roots"]["roots"] = sorted(roots, key=lambda r: r["signs"])
        with self.assertRaisesRegex(OracleMismatch, "increasing FLINT roots"):
            oracle.check_record(record)

    def test_descriptor_diagnostics_and_missing_roots(self):
        for name in ("absent", "ambiguous", "unrealized-full", "root-endpoint", "stale-context"):
            record = self.fixture_record("descriptor/" + name)
            oracle.check_record(record)
            record["value"]["validation"] = {"status": "ok", "replay": True}
            with self.subTest(name=name), self.assertRaises(OracleMismatch):
                oracle.check_record(record)
        record = self.fixture_record("descriptor/" + "positive-root")
        record["value"]["roots"]["roots"].pop(0)
        with self.assertRaises(OracleMismatch):
            oracle.check_record(record)

    def test_zero_head_is_a_domain_failure(self):
        record = self.fixture_record("descriptor/zero-head")
        self.assertEqual(record["value"]["validation"]["reason"], "domain")
        oracle.check_record(record)
        record["value"]["validation"]["reason"] = "malformed"
        with self.assertRaises(OracleMismatch):
            oracle.check_record(record)

    def test_descriptor_literals_are_strict(self):
        for path in (("roots", "roots", 0, "indices", 0),
                     ("validation", "completion", "signs", 1),
                     ("validation", "selected", "signs", 0),
                     ("validation", "completion", "replay"),
                     ("validation", "selected", "replay")):
            record = self.fixture_record("descriptor/" + "positive-root")
            target = record["value"]
            for field in path[:-1]:
                target = target[field]
            target[path[-1]] = 1 if path[-1] == "replay" else True
            with self.subTest(path=path), self.assertRaises(OracleMismatch):
                oracle.check_record(record)

    def test_comparison_order_and_common_head(self):
        for name in ("equal-linear-vectors", "shared-irrational", "foreign-endpoint", "negative-head"):
            record = self.fixture_record("compare/" + name)
            oracle.check_record(record)
            bad = copy.deepcopy(record)
            result = bad["value"]["result"]
            result["order"] = "eq" if result["order"] != "eq" else "lt"
            with self.subTest(name=name), self.assertRaises(OracleMismatch):
                oracle.check_record(bad)
        record = self.fixture_record("compare/equal-linear-vectors")
        record["value"]["result"]["commonHead"] = poly(-1, 1)
        with self.assertRaisesRegex(OracleMismatch, "root union"):
            oracle.check_record(record)
        record = self.fixture_record("compare/shared-irrational")
        # The unreduced product retains all roots but has repeated factors.
        record["value"]["result"]["commonHead"] = poly(-12, 4, 12, -4, -3, 1)
        with self.assertRaisesRegex(OracleMismatch, "root union"):
            oracle.check_record(record)

    def test_comparison_encodings_and_replay(self):
        for field in ("leftSigns", "rightSigns", "commonReplay", "leftReplay", "rightReplay"):
            record = self.fixture_record("compare/foreign-endpoint")
            result = record["value"]["result"]
            if field.endswith("Signs"):
                result[field] = [0] * len(result[field])
            else:
                result[field] = False
            with self.subTest(field=field), self.assertRaises(OracleMismatch):
                oracle.check_record(record)

    def test_reencoding_identity_and_absence(self):
        for name in ("shared-irrational", "foreign-endpoints"):
            record = self.fixture_record("reencode/" + name)
            oracle.check_record(record)
            record["value"]["result"]["signs"][0] *= -1
            with self.subTest(name=name), self.assertRaises(OracleMismatch):
                oracle.check_record(record)
        for name in ("outside-target", "missing-root", "invalid-target"):
            record = self.fixture_record("reencode/" + name)
            oracle.check_record(record)
            record["value"]["result"] = {"status": "ok", "signs": [1], "indices": [1], "replay": True}
            with self.subTest(name=name), self.assertRaises(OracleMismatch):
                oracle.check_record(record)

    def test_descriptor_context_is_an_integer_literal(self):
        record = self.fixture_record("descriptor/positive-root")
        record["value"]["context"] = 10377.0
        with self.assertRaises(OracleMismatch):
            oracle.check_record(record)

    def test_empty_stream_is_failure(self):
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / "empty.jsonl"
            path.write_text("")
            with self.assertRaises(OracleMismatch):
                oracle.check(path, Path(directory) / "failures", "ci", 10377)


if __name__ == "__main__":
    unittest.main()
