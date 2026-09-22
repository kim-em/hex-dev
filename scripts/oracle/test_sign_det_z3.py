"""Adversarial checks of the exact nested-infinitesimal oracle."""
import copy
import json
import unittest
from unittest.mock import patch

from scripts.oracle import sign_det_z3 as oracle
from scripts.oracle.common import OracleMismatch


class InfinitesimalOracle(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        oracle.check_version()
        cls.records = {r["case"].removeprefix("infinitesimal/"): r
                       for line in oracle.DEFAULT_FIXTURE.read_text().splitlines()
                       if (r := json.loads(line))}

    def record(self, name):
        return copy.deepcopy(self.records[name])

    def reject(self, record):
        with self.assertRaises(OracleMismatch):
            oracle.check_record(record)

    def test_exact_passmore_signs(self):
        for name, expected in (("passmore/whole", [([-1], 1), ([1], 2)]),
                               ("passmore/positive", [([-1], 1), ([1], 1)]),
                               ("passmore/empty", [([], 2)])):
            record = self.record(name)
            rcf = oracle.RCF(record["value"]["coefficientContext"])
            self.assertEqual(rcf.table(record["value"]["data"]),
                             [{"signs": s, "count": c} for s, c in expected])
            oracle.check_record(record)

    def test_omitted_support_with_correct_total(self):
        for mode in ("reduced", "direct", "reference"):
            record = self.record("passmore/positive")
            record["value"]["data"][mode]["table"] = [{"signs": [1], "count": 2}]
            self.reject(record)

    def test_each_replay_and_reference_required(self):
        for mode in ("reduced", "direct", "reference"):
            record = self.record("passmore/positive")
            record["value"]["data"][mode]["replay"] = False
            self.reject(record)
        record = self.record("passmore/positive")
        del record["value"]["data"]["reference"]
        self.reject(record)

    def test_stale_child_and_missing_support_checks(self):
        for name in ("square/zero-repeat", "nested/whole"):
            for mode in ("reduced", "direct"):
                for key in ("staleChildReplay", "missingSupportReplay"):
                    record = self.record(name)
                    record["value"]["data"][mode][key] = True
                    self.reject(record)

    def test_nested_order_and_fresh_context(self):
        context = self.record("nested/whole")["value"]["coefficientContext"]
        rcf = oracle.RCF(context)
        epsilon, delta = rcf.levels
        self.assertTrue(0 < delta < epsilon ** 20)
        for _ in range(3):
            oracle.check_record(self.record("nested/whole"))
            oracle.check_record(self.record("passmore/positive"))

    def test_coefficient_context_binding(self):
        for key, value in (("id", 10378), ("id", True), ("levels", ["epsilon2", "epsilon1"]),
                           ("levels", ["epsilon1"]), ("order", "reverse")):
            record = self.record("nested/whole")
            record["value"]["coefficientContext"][key] = value
            self.reject(record)

    def test_required_case_inputs(self):
        for original, replacement, message in (
                ("nested/whole", "square/zero-repeat", "coefficient depth"),
                ("descriptor/nested/singleton", "descriptor/square/negative-head", "coefficient depth"),
                ("reencode/nested/reencode", "reencode/passmore/reencode", "coefficient depth"),
                ("square/zero-repeat", "nested/whole", "coefficient depth"),
                ("passmore/whole", "square/zero-repeat", "Passmore polynomial"),
                ("descriptor/passmore/cubic", "descriptor/square/negative-head", "Passmore polynomial"),
                ("compare/passmore/order", "compare/square/scaled-equal", "Passmore polynomial")):
            record = self.record(replacement)
            record["case"] = "infinitesimal/" + original
            with self.assertRaisesRegex(OracleMismatch, message):
                oracle.check_record(record)
        record = self.record("reencode/passmore/reencode")
        record["value"]["data"]["source"]["head"] = self.record(
            "square/zero-repeat")["value"]["data"]["head"]
        with self.assertRaisesRegex(OracleMismatch, "Passmore polynomial"):
            oracle.check_record(record)

    def test_descriptor_error_reasons(self):
        for name, reason in (("passmore/absent", "absent"), ("passmore/malformed", "malformed"),
                             ("nested/reversed", "domain")):
            record = self.record("descriptor/" + name)
            self.assertEqual(record["value"]["data"]["validation"],
                             {"status": "invalid-descriptor", "reason": reason})
            oracle.check_record(record)
            record["value"]["data"]["validation"]["reason"] = "ambiguous"
            self.reject(record)

    def test_bad_coefficient_denominator(self):
        record = self.record("passmore/whole")
        record["value"]["data"]["head"][0]["den"] = []
        self.reject(record)

    def test_domain_rejections(self):
        for name in ("square/repeated", "square/root-endpoint", "square/cancelled",
                     "nested/reversed", "nested/root-endpoint"):
            record = self.record(name)
            oracle.check_record(record)
            record["value"]["data"]["reduced"] = {"status": "ok", "table": [], "replay": True}
            self.reject(record)

    def test_completion_root_order_and_selected_signs(self):
        for name in ("descriptor/passmore/cubic", "descriptor/passmore/square",
                     "descriptor/nested/singleton", "descriptor/square/negative-head"):
            record = self.record(name)
            oracle.check_record(record)
            for key in ("completion", "selected"):
                bad = copy.deepcopy(record)
                signs = bad["value"]["data"]["validation"][key]["signs"]
                signs[0] = 1 if signs[0] != 1 else -1
                self.reject(bad)
        record = self.record("descriptor/passmore/cubic")
        record["value"]["data"]["roots"]["roots"].reverse()
        self.reject(record)

    def test_booleans_are_not_signs_or_counts(self):
        record = self.record("passmore/positive")
        record["value"]["data"]["reduced"]["table"][0]["count"] = True
        self.reject(record)
        record = self.record("descriptor/passmore/cubic")
        record["value"]["data"]["roots"]["roots"][0]["signs"][-1] = True
        self.reject(record)
        record = self.record("descriptor/passmore/square")
        record["value"]["data"]["validation"]["selected"]["signs"][0] = True
        self.reject(record)

    def test_stale_descriptor_and_changed_queries(self):
        for name in ("descriptor/passmore/cubic", "descriptor/nested/singleton"):
            for key in ("staleContextReplay", "changedHeadReplay"):
                record = self.record(name)
                record["value"]["data"]["validation"][key] = True
                self.reject(record)
            record = self.record(name)
            record["value"]["data"]["validation"]["completion"]["copiedQueriesReplay"] = True
            self.reject(record)
        record = self.record("descriptor/nested/stale-context")
        record["value"]["data"]["validation"]["reason"] = "ambiguous"
        self.reject(record)

    def test_empty_partial_descriptor_is_ambiguous(self):
        record = self.record("descriptor/passmore/ambiguous")
        oracle.check_record(record)
        record["value"]["data"]["validation"]["reason"] = "absent"
        self.reject(record)

    def test_comparison_and_reencoding(self):
        for name in ("compare/passmore/order", "compare/square/scaled-equal",
                     "compare/passmore/shared-cubic"):
            record = self.record(name)
            oracle.check_record(record)
            record["value"]["data"]["result"]["order"] = "gt"
            self.reject(record)
        for name in ("reencode/passmore/reencode", "reencode/nested/reencode"):
            record = self.record(name)
            oracle.check_record(record)
            record["value"]["data"]["result"]["signs"][0] *= -1
            self.reject(record)

    def test_version_pin(self):
        with patch.object(oracle, "version", return_value="4.15.3.0"):
            with self.assertRaises(OracleMismatch):
                oracle.check_version()
        with patch("z3.get_version", return_value=(4, 15, 3, 0)):
            with self.assertRaises(OracleMismatch):
                oracle.check_version()
        with patch("z3.get_full_version", return_value="Z3 4.15.4.0 custom build"):
            oracle.check_version()


if __name__ == "__main__":
    unittest.main()
