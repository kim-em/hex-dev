import copy
import json
from pathlib import Path
import unittest

from scripts.oracle.real_closure_samples import verify


class SampleTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        path = Path(__file__).resolve().parents[2] / "conformance-fixtures/HexRealClosure/samples.jsonl"
        cls.rows = [json.loads(line) for line in path.read_text().splitlines() if line]

    def rejects(self, mutation, message):
        rows = copy.deepcopy(self.rows)
        mutation(rows)
        with self.assertRaisesRegex(AssertionError, message):
            verify(rows)

    def test_valid(self):
        verify(self.rows)

    def test_missing_family(self):
        self.rejects(lambda rows: rows.pop(), "sample cases")

    def test_duplicate_section(self):
        self.rejects(lambda rows: rows[0]["sections"].append(rows[0]["sections"][0]), "sections incomplete")

    def test_missing_sector(self):
        self.rejects(lambda rows: rows[1]["sectors"].pop(), "sectors incomplete")

    def test_reordered_sections(self):
        self.rejects(lambda rows: rows[0]["sections"].reverse(), "section boundary differs")

    def test_reordered_sectors(self):
        self.rejects(lambda rows: rows[1]["sectors"].reverse(), "sector boundaries differ")

    def test_stale_sample_base(self):
        self.rejects(lambda rows: rows[0]["sections"][0]["context"].__setitem__(1, 1), "context stages")

    def test_false_predecessor_tag(self):
        self.rejects(lambda rows: rows[0]["sections"][0]["context"][2][0].__setitem__(0, [False]),
                     "root frame")

    def test_false_cached_sign(self):
        self.rejects(lambda rows: rows[0]["sections"][0]["value"].__setitem__(1, 1), "cached sign differs")

    def test_false_native_member(self):
        self.rejects(lambda rows: rows[0]["sectors"][1].__setitem__("member", False), "membership rejected")

    def test_section_point_not_root(self):
        def mutate(rows):
            rows[0]["sections"][0]["value"][0][0] = [0, 1, 1]
        self.rejects(mutate, "section point differs")

    def test_bounded_point_on_endpoint(self):
        def mutate(rows):
            sample = rows[0]["sectors"][1]
            sample["value"] = copy.deepcopy(sample["cell"]["lower"][1])
        self.rejects(mutate, "outside sector")

    def test_false_transported_coefficient(self):
        def mutate(rows):
            rows[0]["sections"][0]["polynomials"][0][0] = [[[0, -1, 1]], -1]
        self.rejects(mutate, "coefficient conversion changed")

    def test_false_computed_sign(self):
        self.rejects(lambda rows: rows[0]["sectors"][1]["signs"].__setitem__(0, 1), "computed signs differ")

    def test_boolean_sign(self):
        self.rejects(lambda rows: rows[0]["sectors"][0]["signs"].__setitem__(0, True), "computed signs differ")

    def test_reversed_endpoints(self):
        def mutate(rows):
            cell = rows[0]["sectors"][1]["cell"]
            cell["lower"], cell["upper"] = cell["upper"], cell["lower"]
        self.rejects(mutate, "sector boundaries differ")

    def test_infinite_endpoint_boolean(self):
        self.rejects(lambda rows: rows[0]["sectors"][0]["cell"].__setitem__("lower", [False]),
                     "malformed sample endpoint")

    def test_infinitesimal_depth(self):
        self.rejects(lambda rows: rows[4]["context"].__setitem__(1, 0), "context stages")

    def test_lost_parent(self):
        self.rejects(lambda rows: rows[5]["context"][2].clear(), "predecessor depth")

    def test_missing_zero_polynomial(self):
        self.rejects(lambda rows: rows[3]["polynomials"].pop(), "family input")

    def test_extra_ray_root(self):
        def mutate(rows):
            rows[0]["sectors"][0]["context"] = copy.deepcopy(rows[0]["sectors"][1]["context"])
        self.rejects(mutate, "not local to its boundaries")

    def test_stale_parent_prefix(self):
        def mutate(rows):
            rows[5]["sectors"][0]["context"][2][0][2] = [1, [1, [[0, 2, 1]], [[0, 1, 1]]]]
            rows[5]["sectors"][0]["context"][2][0][3] = [2]
            rows[5]["sectors"][0]["context"][2][0][4] = []
            rows[5]["sectors"][0]["context"][2][0][5] = []
        self.rejects(mutate, "does not select one root|not local to its boundaries")

    def test_different_selected_child(self):
        def mutate(rows):
            frame = rows[0]["sections"][0]["context"][2][0]
            frame[2] = [1, [0, 0, 1]]
            frame[3] = [2]
            frame[4] = []
            frame[5] = []
        self.rejects(mutate, "cached sign differs|section boundary differs")


if __name__ == "__main__":
    unittest.main()
