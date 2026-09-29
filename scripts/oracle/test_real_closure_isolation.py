"""Rejection tests for the exact capped-isolation completion oracle."""
import copy
import json
from pathlib import Path
import unittest
from scripts.oracle.real_closure_isolation import verify

FIXTURE = Path(__file__).resolve().parents[2] / "conformance-fixtures/HexRealClosure/isolation.jsonl"


class IsolationTests(unittest.TestCase):
    def setUp(self):
        self.rows = [json.loads(line) for line in FIXTURE.read_text().splitlines()]

    def rejects(self, mutate, message=None):
        rows = copy.deepcopy(self.rows)
        mutate(rows)
        context = (self.assertRaisesRegex((ValueError, AssertionError), message)
                   if message else self.assertRaises((ValueError, AssertionError)))
        with context:
            verify(rows)

    def test_valid(self):
        verify(self.rows)

    def test_missing_case(self):
        self.rejects(lambda rows: rows.pop())

    def test_missing_root(self):
        self.rejects(lambda rows: rows[4]["output"]["descriptors"].pop())

    def test_duplicate_root(self):
        self.rejects(lambda rows: rows[4]["output"]["descriptors"].append(rows[4]["output"]["descriptors"][0]))

    def test_lost_cut_point(self):
        self.rejects(lambda rows: rows[5]["output"]["points"].clear())

    def test_lost_scalar(self):
        self.rejects(lambda rows: rows[5]["output"]["route"].update(head=[[-2, 1], [0, 1], [1, 1]]))

    def test_wrong_count(self):
        self.rejects(lambda rows: rows[4]["output"]["route"]["cells"][0].update(count=99))

    def test_wrong_bound(self):
        self.rejects(lambda rows: rows[4]["output"]["route"].update(bound=[100, 1]))

    def test_exceeded_cap(self):
        self.rejects(lambda rows: rows[9]["output"]["route"].update(nodes=100))

    def test_wrong_fallback(self):
        self.rejects(lambda rows: rows[8]["output"]["route"].update(kind="bounded"))

    def test_stale_descriptor_head(self):
        self.rejects(lambda rows: rows[4]["output"]["descriptors"][0].update(head=[[-3, 1], [0, 1], [1, 1]]))

    def test_false_thom_word(self):
        self.rejects(lambda rows: rows[9]["output"]["descriptors"][0].update(signs=[-1, -1]),
                     "descriptor does not select exactly one root")

    def test_boolean_slot(self):
        self.rejects(lambda rows: rows[8]["output"]["descriptors"][0].update(indices=[True]))

    def test_stale_interval(self):
        self.rejects(lambda rows: rows[4]["output"]["descriptors"][0].update(lower=[1, [-100, 1]]))

    def test_null_valid_output(self):
        self.rejects(lambda rows: rows[4].update(output=None))

    def test_diagnostic_valid_output(self):
        self.rejects(lambda rows: rows[4].update(output={"error": "system"}))

    def test_empty_valid_output(self):
        def empty(rows):
            rows[4]["output"]["points"].clear()
            rows[4]["output"]["descriptors"].clear()
        self.rejects(empty)

    def test_overlapping_cells(self):
        self.rejects(lambda rows: rows[4]["output"]["route"]["cells"].append(
            rows[4]["output"]["route"]["cells"][0]))

    def test_root_at_cell_endpoint(self):
        self.rejects(lambda rows: rows[9]["output"]["route"]["cells"][0].update(lower={
            "num": [[0, 1], [1, 1]], "den": [[1, 1]]}, count=1),
                     "invalid retained cell")

    def test_foreign_descriptor_context(self):
        self.rejects(lambda rows: rows[4]["output"]["descriptors"][0].update(context=10377))

    def test_zero_accepted(self):
        self.rejects(lambda rows: rows[0].update(output=rows[1]["output"]))

    def test_repeated_accepted(self):
        self.rejects(lambda rows: rows[2].update(output=rows[4]["output"]))


if __name__ == "__main__":
    unittest.main()
