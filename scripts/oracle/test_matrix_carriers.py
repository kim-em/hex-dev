#!/usr/bin/env python3
"""Regression checks for exact carrier encodings and the persistent comparator."""
import copy
import json
from pathlib import Path
import subprocess
import sys
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parent))

from matrix_carriers import evaluate, prepare
from matrix_carriers_bench_driver import run

ROOT = Path(__file__).resolve().parents[2]
FIXTURES = ROOT / "conformance-fixtures/HexDeterminant/carriers.jsonl"


class MatrixCarriersTest(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.records = [json.loads(line) for line in FIXTURES.read_text().splitlines()]

    def select(self, carrier, base, case="nonconstant", arity=1):
        return copy.deepcopy(next(r for r in self.records
                                  if (r["carrier"], r["base"], r["case"], r["arity"]) ==
                                  (carrier, base, case, arity)))

    def test_all_exact_results_and_persistent_reuse(self):
        for record in self.records:
            with self.subTest(carrier=record["carrier"], base=record["base"], case=record["case"]):
                self.assertEqual(evaluate(record), record["determinant"])
                line = json.dumps(record)
                self.assertEqual(run(line), record["determinant"])
                self.assertEqual(run(line), record["determinant"])

    def test_required_fixture_shapes(self):
        domains = {(r["carrier"], r["base"], r["arity"]) for r in self.records}
        self.assertEqual(domains, {("dense", "ZZ", 1), ("dense", "QQ", 1), ("dense", "GF", 1),
                                   ("mv", "ZZ", 2), ("mv", "ZZ", 3),
                                   ("mv", "QQ", 2), ("mv", "QQ", 3), ("ratfn", "QQ", 1)})
        for carrier, base, arity in domains:
            records = {r["case"]: r for r in self.records
                       if (r["carrier"], r["base"], r["arity"]) == (carrier, base, arity)}
            self.assertEqual(set(records), {"empty", "scalar", "nonconstant", "cancellation",
                                           "singular", "triangular", "row-swap"})
            value = records["nonconstant"]["determinant"]
            if carrier == "ratfn":
                self.assertGreater(len(value["den"]), 1)
                self.assertTrue(any(len(x["den"]) > 1 for row in records["nonconstant"]["matrix"] for x in row))
            elif carrier == "mv":
                self.assertTrue(any(sum(m) > 0 for m, _ in value))
            else:
                self.assertGreater(len(value), 1)

    def test_noncanonical_inputs_rejected(self):
        mutations = []
        r = self.select("dense", "GF")
        r["matrix"][0][0][0] += 101
        mutations.append(r)
        r = self.select("dense", "GF")
        r["matrix"][0][0][0] -= 101
        mutations.append(r)
        r = self.select("dense", "QQ")
        r["matrix"][0][0][0] = [2, 4]
        mutations.append(r)
        r = self.select("dense", "ZZ")
        r["matrix"][0][0].append(0)
        mutations.append(r)
        r = self.select("mv", "ZZ", arity=3)
        r["matrix"][0][0].reverse()
        mutations.append(r)
        r = self.select("mv", "QQ", arity=2)
        r["matrix"][0][0].append(r["matrix"][0][0][0])
        mutations.append(r)
        r = self.select("ratfn", "QQ")
        # Multiplication of both parts by x preserves the value but breaks reduction.
        for part in ("num", "den"):
            r["matrix"][0][0][part].insert(0, [0, 1])
        mutations.append(r)
        r = self.select("ratfn", "QQ")
        r["matrix"][0][0]["den"] = []
        mutations.append(r)
        for record in mutations:
            with self.subTest(record=record):
                with self.assertRaises(ValueError):
                    prepare(record)

    def test_bad_kind_and_shape(self):
        record = self.select("dense", "ZZ")
        record["kind"] = "unrecognized"
        with self.assertRaises(ValueError):
            evaluate(record)
        record["n"] += 1
        with self.assertRaises(ValueError):
            prepare(record)

    def test_oracle_rejects_corrupted_result_and_empty_stream(self):
        record = self.select("dense", "ZZ")
        record["determinant"][0] += 1
        for stream in (json.dumps(record), ""):
            result = subprocess.run([sys.executable, str(ROOT / "scripts/oracle/matrix_carriers.py")],
                                    input=stream, text=True, capture_output=True)
            self.assertNotEqual(result.returncode, 0)

    def test_driver_recovers_after_bad_request(self):
        record = self.select("dense", "GF")
        requests = ['{"kind":"overhead"}', '{"kind":"bad"}', json.dumps(record)]
        result = subprocess.run([sys.executable, str(ROOT / "scripts/oracle/matrix_carriers_bench_driver.py")],
                                input="\n".join(requests) + "\n", text=True, capture_output=True, check=True)
        replies = [json.loads(line) for line in result.stdout.splitlines()]
        self.assertEqual(replies[0], {"ok": True, "result": 0})
        self.assertFalse(replies[1]["ok"])
        self.assertEqual(replies[2], {"ok": True, "result": record["determinant"]})


if __name__ == "__main__":
    unittest.main()
