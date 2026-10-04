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
        self.rejects(lambda rows: rows[9].update(policy=rows[0]["policy"]))

    def test_missing_root(self):
        self.rejects(lambda rows: rows[12]["result"]["output"]["entries"].pop())

    def test_duplicate_root(self):
        self.rejects(lambda rows: rows[25]["result"]["output"]["entries"].append(
            rows[25]["result"]["output"]["entries"][0]))

    def test_wrong_label(self):
        self.rejects(lambda rows: rows[21]["result"]["output"]["entries"][0].update(multiplicity=99))

    def test_missing_all_case(self):
        self.rejects(lambda rows: rows[18]["result"].update(output={"kind":"finite","entries":[]}))

    def test_wrong_input(self):
        self.rejects(lambda rows: rows[20]["result"]["head"].__setitem__(6, [-7,1]))
