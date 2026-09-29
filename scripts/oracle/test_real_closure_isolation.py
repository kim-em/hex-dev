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

    def test_assembly_missing_root(self):
        self.rejects(lambda rows: rows[13]["output"]["entries"].pop())

    def test_assembly_duplicate_root(self):
        self.rejects(lambda rows: rows[13]["output"]["entries"].append(
            rows[13]["output"]["entries"][1]))

    def test_assembly_wrong_multiplicity(self):
        self.rejects(lambda rows: rows[13]["output"]["entries"][1].update(multiplicity=4),
                     "wrong assembled root multiplicity")

    def test_nonzero_cut_point_value(self):
        self.rejects(lambda rows: next(entry for entry in rows[18]["output"]["entries"]
                                      if entry["root"]["kind"] == "point")["root"].update(
            value=[3, 2]), "nonzero cut-point fixture")

    def test_nonzero_cut_point_replaced_by_descriptor(self):
        selected = {"kind": "selected", "context": 10378,
                    "head": [[-1, 1], [1, 1]], "lower": [1, [0, 1]],
                    "upper": [1, [3, 2]], "indices": [], "signs": []}
        self.rejects(lambda rows: next(entry for entry in rows[18]["output"]["entries"]
                                      if entry["root"]["kind"] == "point").update(
            root=selected), "nonzero cut-point fixture")

    def test_nonzero_cut_point_multiplicity(self):
        self.rejects(lambda rows: next(entry for entry in rows[18]["output"]["entries"]
                                      if entry["root"]["kind"] == "point").update(
            multiplicity=1), "wrong assembled root multiplicity")

    def test_assembly_missing_zero(self):
        self.rejects(lambda rows: rows[12]["output"]["entries"].clear())

    def test_assembly_false_selected_interval(self):
        self.rejects(lambda rows: rows[13]["output"]["entries"][1]["root"].update(
            lower=[1, [0, 1]]), "assembled descriptor does not select one root")

    def test_assembly_impossible_infinite_endpoint(self):
        self.rejects(lambda rows: rows[13]["output"]["entries"][2]["root"].update(
            lower=[2]), "assembled descriptor does not select one root")

    def test_assembly_boolean_derivative_slot(self):
        self.rejects(lambda rows: rows[13]["output"]["entries"][1]["root"].update(
            indices=[True, 2]), "wrong assembled derivative slots")

    def test_assembly_false_all(self):
        self.rejects(lambda rows: rows[11].update(output={"kind": "all"}))

    def test_nested_wrong_predecessor_value(self):
        self.rejects(lambda rows: rows[16]["head"][0].__setitem__(1, [1, 1]),
                     "wrong nested algebraic input")

    def test_nested_missing_root(self):
        self.rejects(lambda rows: rows[16]["output"]["descriptors"].pop(),
                     "nested roots missing or duplicated")

    def test_nested_stale_descriptor(self):
        self.rejects(lambda rows: rows[16]["output"]["descriptors"][0].update(context=10378),
                     "stale nested descriptor")

    def test_nested_wrong_first_definition(self):
        self.rejects(lambda rows: rows[16]["base"].update(
            head=[[9, 1], [-3, 1], [-3, 1], [1, 1]]),
            "wrong first-level definition")

    def test_nested_wrong_first_interval(self):
        self.rejects(lambda rows: rows[16]["base"].update(lower=[1, [0, 1]]),
                     "wrong first-level interval")

    def test_nested_wrong_bound(self):
        self.rejects(lambda rows: rows[16]["output"]["route"].update(bound=[[8, 1]]),
                     "incorrect nested bounded route")

    def test_nested_wrong_cell_count(self):
        self.rejects(lambda rows: rows[16]["output"]["route"]["cells"][0].update(count=2),
                     "wrong nested cell count")

    def test_nested_noncanonical_zero(self):
        self.rejects(lambda rows: rows[16]["head"].__setitem__(1,
            [[-2, 1], [0, 1], [1, 1]]), "noncanonical nested zero")

    def test_nested_assembly_wrong_multiplicity(self):
        self.rejects(lambda rows: rows[17]["output"]["entries"][1].update(multiplicity=3),
                     "wrong nested root multiplicity")

    def test_nested_assembly_missing_root(self):
        self.rejects(lambda rows: rows[17]["output"]["entries"].pop(),
                     "nested assembly roots missing or duplicated")

    def test_nested_assembly_foreign_coefficient(self):
        self.rejects(lambda rows: rows[17]["head"][0].__setitem__(2, [-2, 1]),
                     "wrong nested assembly input")

    def test_nested_assembly_stale_base(self):
        self.rejects(lambda rows: rows[17]["base"].update(context=10379),
                     "malformed nested assembly row")

    def test_nested_assembly_ambiguous_descriptor(self):
        self.rejects(lambda rows: rows[17]["output"]["entries"][1]["root"].update(
            upper=[1, [[4, 1]]]), "nested assembly descriptor is ambiguous")


if __name__ == "__main__":
    unittest.main()
