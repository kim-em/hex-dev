"""Rejection checks for exact RootSet policy conformance."""
import copy
from pathlib import Path
import unittest
from scripts.oracle.real_closure_policies import parse_record, verify

FIXTURE = Path(__file__).resolve().parents[2]/"conformance-fixtures/HexRealClosure/policies.jsonl"

class PolicyTests(unittest.TestCase):
    def setUp(self):
        self.rows = [parse_record(s) for s in FIXTURE.read_text().splitlines()]

    def rejects(self, mutate):
        rows = copy.deepcopy(self.rows)
        mutate(rows)
        with self.assertRaises((ValueError, AssertionError)):
            verify(rows)

    def test_valid(self):
        verify(self.rows)

    def test_missing_case(self):
        self.rejects(lambda rows: rows.pop())

    def test_wrong_policy(self):
        self.rejects(lambda rows: rows[11].update(policy=rows[0]["policy"]))

    def test_missing_root(self):
        self.rejects(lambda rows: rows[14]["result"]["output"]["entries"].pop())

    def test_duplicate_root(self):
        self.rejects(lambda rows: rows[29]["result"]["output"]["entries"].append(
            rows[29]["result"]["output"]["entries"][0]))

    def test_wrong_label(self):
        self.rejects(lambda rows: rows[24]["result"]["output"]["entries"][0].update(multiplicity=99))

    def test_missing_all_case(self):
        self.rejects(lambda rows: rows[22]["result"].update(output={"kind":"finite","entries":[]}))

    def test_wrong_input(self):
        self.rejects(lambda rows: rows[25]["result"]["head"].__setitem__(6, [-7,1]))

    def test_reordered_close_roots(self):
        self.rejects(lambda rows: rows[31]["result"]["output"]["entries"].reverse())

    def test_whole_finite_bounds(self):
        self.rejects(lambda rows: rows[31]["result"]["output"]["entries"][0]["root"].update(
            lower=rows[9]["result"]["output"]["entries"][0]["root"]["lower"]))

    def test_missing_derivative_selection(self):
        self.rejects(lambda rows: rows[31]["result"]["output"]["entries"][0]["root"].update(
            indices=[], signs=[]))

    def test_bounded_lost_bounds(self):
        self.rejects(lambda rows: rows[14]["result"]["output"]["entries"][0]["root"].update(lower=[0]))

    def test_bounded_asymmetric_cell(self):
        rows = copy.deepcopy(self.rows)
        rows[14]["result"]["output"]["entries"][-1]["root"]["lower"] = [1, [0, 1]]
        with self.assertRaisesRegex(AssertionError, "subdivided its symmetric initial cell"):
            verify(rows)

    def test_bounded_subdivided_factor(self):
        rows = copy.deepcopy(self.rows)
        rows[14]["result"]["output"]["entries"][2]["root"].update(
            lower=[1, [-2, 1]], upper=[1, [2, 1]])
        with self.assertRaisesRegex(AssertionError, "subdivided one squarefree factor"):
            verify(rows)

    def test_bounded_inverse_fallback(self):
        rows = copy.deepcopy(self.rows)
        rows[19]["result"]["output"]["entries"][0]["root"]["lower"] = [1, {"num": [], "den": [[1, 1]]}]
        with self.assertRaisesRegex(AssertionError, "did not use the whole-line fallback"):
            verify(rows)

    def test_bounded_wrong_bound_for_entire_factor(self):
        rows = copy.deepcopy(self.rows)
        for index in (0, 2):
            rows[14]["result"]["output"]["entries"][index]["root"].update(
                lower=[1, [-2, 1]], upper=[1, [2, 1]])
        with self.assertRaisesRegex(AssertionError, "first accepted Cauchy bound"):
            verify(rows)
