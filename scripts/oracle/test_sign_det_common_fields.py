"""Adversarial checks of the independent algebraic-coefficient oracle."""
import copy
import json
import subprocess
import sys
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

    def test_conjugate_embeddings_are_rejected(self):
        case = "common/independent-quadratics"
        for target, message in (("generator", "common-field coordinates change selected values"),
                                ("first-input", "wrong original embeddings")):
            record = self.record(case)
            raw = (record["value"]["generator"] if target == "generator" else
                   record["value"]["inputs"][0])
            lower, upper = raw["lower"], raw["upper"]
            raw["lower"], raw["upper"] = [-upper[0], upper[1]], [-lower[0], lower[1]]
            with self.subTest(target=target), self.assertRaisesRegex(OracleMismatch, message):
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

    def test_root_order_encoding_and_common_head(self):
        for case in oracle.CASES:
            for mutation in ("swap-roots", "derivative-sign", "common-head",
                             "reencoded-sign", "reencoded-selected", "descriptor-sign",
                             "descriptor-context", "reencoding-head", "equal-descriptor"):
                record = self.record(case)
                result = record["value"]["result"]
                if mutation == "swap-roots":
                    result["roots"].reverse()
                elif mutation == "derivative-sign":
                    result["roots"][0]["signs"][0] *= -1
                elif mutation == "common-head":
                    result["commonHead"][0][0][0] += 1
                elif mutation == "reencoded-sign":
                    result["reencodedSigns"][0] *= -1
                elif mutation == "reencoded-selected":
                    result["reencodedSelected"][0] = 1
                elif mutation == "descriptor-sign":
                    result["leftDescriptor"]["signs"][0] *= -1
                elif mutation == "descriptor-context":
                    result["rightDescriptor"]["context"] += 1
                elif mutation == "equal-descriptor":
                    result["equalDescriptor"]["signs"][0] *= -1
                else:
                    result["reencodingHead"][0][0][0] += 1
                with self.subTest(case=case, mutation=mutation), self.assertRaises(OracleMismatch):
                    oracle.check_record(record)

    def test_both_total_orders_and_stale_replay(self):
        for case in oracle.CASES:
            for key in ("order", "totalOrder", "reverseOrder", "equalOrder",
                        "crossExpressionOrder", "crossExpressionReverse",
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


class FieldSignOracle(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.data = json.loads((oracle.DEFAULT_FIXTURE.parent / "field-signs.jsonl").read_text())

    def test_exact_close_values(self):
        oracle.check_scalar_data(copy.deepcopy(self.data))

    def test_changed_sign(self):
        data = copy.deepcopy(self.data)
        data[0]["values"][0]["sign"] *= -1
        with self.assertRaisesRegex(OracleMismatch, "wrong scalar sign"):
            oracle.check_scalar_data(data)

    def test_changed_coordinate(self):
        data = copy.deepcopy(self.data)
        data[1]["values"][0]["coordinates"][0][0] += 1
        with self.assertRaisesRegex(OracleMismatch, "wrong cancellation family value"):
            oracle.check_scalar_data(data)

    def test_stdin_reports_a_changed_sign(self):
        data = copy.deepcopy(self.data)
        data[0]["values"][0]["sign"] *= -1
        result = subprocess.run(
            [sys.executable, str(oracle.ROOT / "scripts/oracle/sign_det_field_signs.py")],
            input=json.dumps(data), text=True, capture_output=True, cwd=oracle.ROOT)
        self.assertEqual(result.returncode, 1)
        self.assertIn("FAIL HexSignDet field-sign oracle: wrong scalar sign", result.stderr)
        self.assertNotIn("Traceback", result.stderr)

    def test_missing_values(self):
        data = copy.deepcopy(self.data)
        data[0]["values"].pop()
        with self.assertRaisesRegex(OracleMismatch, "missing close-value coordinates"):
            oracle.check_scalar_data(data)


if __name__ == "__main__":
    unittest.main()
