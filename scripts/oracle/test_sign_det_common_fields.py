"""Adversarial checks of the independent algebraic-coefficient oracle."""
import copy
import json
import tempfile
import unittest
from pathlib import Path

from scripts.oracle import sign_det_common_fields as oracle
from scripts.oracle.common import OracleMismatch


class CommonFieldOracle(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.records = {r["case"]: r for line in oracle.DEFAULT_FIXTURE.read_text().splitlines()
                       if (r := json.loads(line))}
        assert set(cls.records) == set(oracle.CASES)

    def record(self, case):
        return copy.deepcopy(self.records[case])

    def test_exact_selected_embeddings(self):
        for case in oracle.CASES:
            with self.subTest(case=case):
                oracle.check_record(self.record(case))

    def test_generator_and_original_values_are_bound(self):
        for case in oracle.CASES:
            for mutation in ("generator", "first-input", "coordinate"):
                record = self.record(case)
                data = record["value"]
                if mutation == "generator":
                    data["generator"]["polynomial"][0] += 1
                elif mutation == "first-input":
                    data["inputs"][0]["polynomial"][0] -= 1
                else:
                    data["coordinates"][0][0][0] += 1
                with self.subTest(case=case, mutation=mutation), self.assertRaises(OracleMismatch):
                    oracle.check_record(record)

    def test_actual_polynomial_and_query_bindings(self):
        for case in oracle.CASES:
            for target in ("head", "queries"):
                record = self.record(case)
                coefficients = record["value"][target]
                if target == "queries":
                    coefficients = coefficients[0]
                coefficients[0][0][0] += 1
                with self.subTest(case=case, target=target), self.assertRaises(OracleMismatch):
                    oracle.check_record(record)

    def test_omitted_support_and_root_signs(self):
        for case in oracle.CASES:
            for mutation in ("missing-row", "wrong-count", "wrong-root", "false-replay"):
                record = self.record(case)
                result = record["value"]["result"]
                if mutation == "missing-row":
                    result["table"].pop()
                elif mutation == "wrong-count":
                    result["table"][0]["count"] += 1
                elif mutation == "wrong-root":
                    result["roots"][0]["selected"][0] = 1
                else:
                    result["roots"][0]["replay"] = False
                with self.subTest(case=case, mutation=mutation), self.assertRaises(OracleMismatch):
                    oracle.check_record(record)

    def test_both_total_orders_and_stale_replay(self):
        for case in oracle.CASES:
            for key in ("order", "totalOrder", "reverseOrder", "equalOrder",
                        "commonReplay", "leftReplay", "rightReplay", "reencodingReplay",
                        "copiedReplay", "staleReplay", "repeatedAccepted"):
                record = self.record(case)
                result = record["value"]["result"]
                current = result[key]
                result[key] = (not current) if type(current) is bool else "eq" if current != "eq" else "lt"
                with self.subTest(case=case, key=key), self.assertRaises(OracleMismatch):
                    oracle.check_record(record)
                record = self.record(case)
                del record["value"]["result"][key]
                with self.subTest(case=case, key=key, missing=True), self.assertRaises(OracleMismatch):
                    oracle.check_record(record)

    def test_missing_case_is_not_success(self):
        with tempfile.TemporaryDirectory() as tmp:
            path = Path(tmp) / "subset.jsonl"
            path.write_text(json.dumps(next(iter(self.records.values()))) + "\n")
            with self.assertRaisesRegex(OracleMismatch, "missing common-field cases"):
                oracle.check(path, Path(tmp), "local", 10377)


if __name__ == "__main__":
    unittest.main()
