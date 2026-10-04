"""Rejection tests for the exact capped-isolation completion oracle."""
import copy
from pathlib import Path
import unittest
from scripts.oracle.real_closure_isolation import parse_record, verify, squarefree_factors
from scripts.oracle.sign_det_z3 import RCF

FIXTURE = Path(__file__).resolve().parents[2] / "conformance-fixtures/HexRealClosure/isolation.jsonl"


class IsolationTests(unittest.TestCase):
    def setUp(self):
        self.rows = [parse_record(line) for line in FIXTURE.read_text().splitlines()]

    def rejects(self, mutate, message=None):
        rows = copy.deepcopy(self.rows)
        mutate(rows)
        context = (self.assertRaisesRegex((ValueError, AssertionError), message)
                   if message else self.assertRaises((ValueError, AssertionError)))
        with context:
            verify(rows)

    def test_valid(self):
        verify(self.rows)

    def test_duplicate_json_fields(self):
        for raw in ['{"output":null,"output":null}',
                    '{"output":{"head":[],"head":[1]}}']:
            with self.subTest(raw=raw), self.assertRaisesRegex(AssertionError, "duplicate JSON field"):
                parse_record(raw)

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
            value=[3, 2]), "assembled root duplicated")

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
        self.rejects(lambda rows: rows[13]["output"]["entries"][0]["root"].update(
            lower=[1, [0, 1]]), "assembled descriptor does not select one root")

    def test_assembly_impossible_infinite_endpoint(self):
        self.rejects(lambda rows: rows[13]["output"]["entries"][2]["root"].update(
            lower=[2]), "assembled descriptor does not select one root")

    def test_assembly_boolean_derivative_slot(self):
        self.rejects(lambda rows: rows[13]["output"]["entries"][0]["root"].update(
            indices=[True, 2]), "wrong assembled derivative slots")

    def test_assembly_unordered_roots(self):
        self.rejects(lambda rows: rows[13]["output"]["entries"].reverse(),
                     "assembled roots are not strictly increasing")

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

    def test_nested_selected_head_scalar(self):
        def mutate(rows):
            root = rows[17]["output"]["entries"][0]["root"]
            root["head"] = [[[2*n, d] for n, d in coefficient] for coefficient in root["head"]]
        self.rejects(mutate, "deflated Yun factor")

    def test_selected_head_retains_removed_coefficient_point(self):
        self.rejects(lambda rows: rows[18]["output"]["entries"][1]["root"].update(
            head=[[3, 2], [-5, 2], [1, 1]]), "deflated Yun factor")

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
        self.rejects(lambda rows: rows[17]["output"]["entries"][0]["root"].update(
            upper=[1, [[4, 1]]]), "nested assembly descriptor is ambiguous")

    def test_nested_assembly_unordered_roots(self):
        self.rejects(lambda rows: rows[17]["output"]["entries"].reverse(),
                     "nested assembled roots are not strictly increasing")

    def test_collection_missing_source(self):
        self.rejects(lambda rows: rows[19]["inputs"].pop(), "lost a source")

    def test_collection_changed_mapped_root(self):
        self.rejects(lambda rows: rows[19]["inputs"][0].update(
            mapped=rows[19]["inputs"][2]["mapped"]), "changed selected root")

    def test_collection_false_cached_sign(self):
        self.rejects(lambda rows: rows[19]["inputs"][0]["mapped"].__setitem__(1, -1),
                     "cached sign differs")

    def test_collection_foreign_predecessor(self):
        self.rejects(lambda rows: rows[19]["context"][2][1].__setitem__(0, [99]),
                     "malformed native root frame")

    def test_collection_changed_root_equation(self):
        self.rejects(lambda rows: rows[19]["context"][2][1].__setitem__(1, []),
                     "wrong native root equation")

    def test_collection_changed_old_inverse(self):
        self.rejects(lambda rows: rows[19]["inputs"][0].update(
            mappedInverse=rows[19]["inputs"][1]["mappedInverse"]), "inverse changed")

    def test_collection_changed_sum(self):
        self.rejects(lambda rows: rows[19].update(sum=rows[19]["inputs"][0]["mapped"]),
                     "mixed-context arithmetic differs")

    def test_collection_changed_coefficient(self):
        self.rejects(lambda rows: rows[19].update(two=rows[19]["three"]), "coefficients changed")

    def test_collection_noncanonical_rational(self):
        self.rejects(lambda rows: rows[19]["context"][2][0][1].__setitem__(0, [0, -4, 2]),
                     "noncanonical native rational")

    def test_collection_trailing_zero(self):
        self.rejects(lambda rows: rows[19]["inputs"][0]["mapped"][0].append([]),
                     "stored trailing zero")

    def test_collection_foreign_base(self):
        self.rejects(lambda rows: rows[19]["context"].__setitem__(0, [["pi", 1]]),
                     "wrong native context stages")

    def test_collection_changed_interval(self):
        self.rejects(lambda rows: rows[19]["context"][2][1].__setitem__(3, [1, [[[0, 3, 1]], 1]]),
                     "native root interval changed")

    def test_collection_false_thom_word(self):
        def corrupt(rows):
            rows[19]["context"][2][0][4] = [1, 2]
            rows[19]["context"][2][0][5] = [-1, 1]
        self.rejects(corrupt, "does not select one root")

    def test_collection_invalid_thom_slots(self):
        self.rejects(lambda rows: rows[19]["context"][2][0].__setitem__(4, [1]),
                     "malformed native root signs")

    def test_collection_changed_source_context(self):
        self.rejects(lambda rows: rows[19]["inputs"][2].update(
            context=rows[19]["inputs"][0]["context"]), "wrong native root equation")

    def test_collection_changed_input_order(self):
        def swap(rows):
            rows[19]["inputs"][0], rows[19]["inputs"][2] = rows[19]["inputs"][2], rows[19]["inputs"][0]
        self.rejects(swap)

    def test_collection_false_zero_sign(self):
        self.rejects(lambda rows: rows[19]["inputs"][0]["mapped"].__setitem__(1, 0),
                     "malformed native nonzero")

    def test_collection_boolean_predecessor(self):
        self.rejects(lambda rows: rows[19]["context"][2][0].__setitem__(0, [False]),
                     "malformed native root frame")



    def test_nested_replay_lost_root_level(self):
        self.rejects(lambda rows: rows[20]["context"][2].pop(), "wrong nested replay stages")

    def test_nested_replay_wrong_infinitesimal_depth(self):
        self.rejects(lambda rows: rows[20]["context"].__setitem__(1, 1),
                     "wrong nested replay stages")

    def test_nested_replay_wrong_consumer_sign(self):
        self.rejects(lambda rows: rows[20]["selected"][1]["values"].__setitem__(0, -1),
                     "nested selected signs differ")

    def test_nested_replay_reordered_consumer_queries(self):
        self.rejects(lambda rows: rows[20]["selected"][1]["queries"].reverse(),
                     "wrong nested consumer queries")

    def test_nested_replay_cyclic_graph(self):
        def mutate(rows):
            graph = rows[20]["selected"][1]["certificates"][0]["graph"]
            graph[2][graph[1]][1] = [[graph[1], graph[1]]]
        self.rejects(mutate, "child-before-parent")

    def test_nested_replay_stale_graph_domain(self):
        self.rejects(lambda rows: rows[20]["selected"][1]["certificates"][0]["graph"][2][0][0].__setitem__(0, [99]),
                     "nested graph domain differs")

    def test_nested_replay_false_integer_table(self):
        def mutate(rows):
            graph = rows[20]["selected"][1]["certificates"][0]["graph"]
            counts = graph[2][graph[1]][0][6][2]
            counts[0] += 1
        self.rejects(mutate, "nested graph table differs")

    def test_nested_replay_false_integer_moment(self):
        def mutate(rows):
            graph = rows[20]["selected"][1]["certificates"][0]["graph"]
            graph[2][graph[1]][0][6][3][0] += 1
        self.rejects(mutate, "nested graph moment differs")

    def test_nested_replay_zero_integer_denominator(self):
        def mutate(rows):
            graph = rows[20]["selected"][1]["certificates"][0]["graph"]
            graph[2][graph[1]][0][6][5] = 0
        self.rejects(mutate, "malformed nested integer dimensions")

    def test_nested_replay_wrong_inverse(self):
        self.rejects(lambda rows: rows[20]["values"].__setitem__(4, []),
                     "nested guard inversion or defining equation changed")

    def test_nested_replay_wrong_stored_sign(self):
        self.rejects(lambda rows: rows[20]["signs"].__setitem__(0, -1),
                     "nested stored signs changed")


    def test_nested_replay_wrong_nonzero_integer_denominator(self):
        def mutate(rows):
            graph = rows[20]["selected"][1]["certificates"][0]["graph"]
            system = graph[2][graph[1]][0][6]
            system[5] += 2
        self.rejects(mutate, "nested inverse matrix identity failed")

    def test_nested_replay_wrong_crossing_value(self):
        self.rejects(lambda rows: rows[20]["values"].__setitem__(7, []),
                     "nested guard inversion or defining equation changed")

    def test_nested_replay_wrong_crossing_sign(self):
        self.rejects(lambda rows: rows[20]["signs"].__setitem__(7, 1),
                     "nested stored signs changed")

class SquarefreeOracleTests(unittest.TestCase):
    def test_rational_factors_agree_with_independent_flint(self):
        from flint import fmpq, fmpq_poly
        rcf = RCF({"id": 10377, "levels": ["epsilon1"],
                   "order": "each-new-level-smaller-than-positive-base-elements"})
        x, a, b = fmpq_poly([0, 1]), fmpq_poly([-1, 1]), fmpq_poly([1, 0, 1])
        rows = [parse_record(line) for line in FIXTURE.read_text().splitlines()]
        fixture_inputs = [fmpq_poly([fmpq(n, d) for n, d in rows[index]["head"]])
                          for index in (11, 12, 13, 14, 15, 18)]
        for p in (fmpq_poly([5]), -5*x**6, 3*a*b, -3*x**2*a**5*b**3,
                  fmpq_poly([3, -5, 2])**2, *fixture_inputs):
            with self.subTest(polynomial=str(p)):
                coefficients = [rcf.api.RCFNum(str(c), rcf.context) for c in p.coeffs()]
                _, expected = p.factor_squarefree()
                factors = {label: [rcf.api.RCFNum(str(c/factor.leading_coefficient()), rcf.context)
                                   for c in factor.coeffs()] for factor, label in expected}
                self.assertEqual(squarefree_factors(rcf, coefficients), factors)


if __name__ == "__main__":
    unittest.main()
