#!/usr/bin/env python3
"""Regression checks for exact carrier encodings and the persistent comparator."""
import copy
import os
import tempfile
import json
from pathlib import Path
import subprocess
import sys
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parent))

from matrix_carriers import Carrier, dispatch, evaluate, prepare
from matrix_carriers_bench_driver import run

ROOT = Path(__file__).resolve().parents[2]
FIXTURES = ROOT / "conformance-fixtures/HexDeterminant/carriers.jsonl"


class DeterminantCarriersTest(unittest.TestCase):
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




class MatrixCarriersTest(unittest.TestCase):
    def setUp(self):
        path = Path(__file__).resolve().parents[2] / 'conformance-fixtures/HexBareiss/carriers.jsonl'
        self.records = [json.loads(line) for line in path.read_text().splitlines()]

    def test_complete_stream(self):
        for record in self.records:
            with self.subTest(id=record['case']):
                self.assertEqual(dispatch(record), record['result'])

    def test_nonconstant_division(self):
        # [[x, 1, 0], [-1, x, 1], [0, -1, x]] has x^3 + 2x.
        for carrier in ['zpoly', 'dense_mod']:
            record = dict(kind='bareiss_carrier', carrier=carrier, arity=1, p=101, n=3,
                          rows=[[[0, 1], [1], []], [[-1] if carrier == 'zpoly' else [100],
                                  [0, 1], [1]], [[], [-1] if carrier == 'zpoly' else [100], [0, 1]]])
            self.assertEqual(dispatch(record), [0, 2, 0, 1])

    def test_reject_noncanonical_coefficients(self):
        bad = [('rat', [2, 4]), ('rat', [1, -2]), ('rat', [True, 1]),
               ('mod', 101), ('mod', -1), ('zpoly', [1, 0]),
               ('dense_mod', [102]), ('mv_int', [[[1, 0], 0]]),
               ('mv_int', [[[1, 0], 1], [[1, 0], 2]]),
               ('mv_int', [[[1, 0], 1], [[0, 0], 2]]),
               ('mv_int', [[[-1, 0], 1]])]
        for carrier, value in bad:
            record = next(r for r in self.records if r['carrier'] == carrier)
            with self.subTest(carrier=carrier, value=value), self.assertRaises(ValueError):
                Carrier(record).decode(value)

    def test_reject_shape_and_unknown_kind(self):
        record = copy.deepcopy(self.records[0])
        record['n'] = 1
        with self.assertRaises(ValueError):
            dispatch(record)
        record['kind'] = 'unknown'
        with self.assertRaises(KeyError):
            dispatch(record)

    def test_reject_wrong_result_and_empty_stream(self):
        record = copy.deepcopy(self.records[0])
        record['result'] = [0, 1]
        driver = Path(__file__).with_name('matrix_carriers.py')
        with tempfile.TemporaryDirectory() as failure_dir:
            env = dict(os.environ, HEX_FAILURE_DIR=failure_dir)
            for stream in ['', json.dumps(record) + '\n']:
                result = subprocess.run([sys.executable, str(driver)], input=stream,
                                        text=True, capture_output=True, env=env)
                self.assertNotEqual(result.returncode, 0)
            failures = list(Path(failure_dir).glob('*.json'))
            self.assertEqual(len(failures), 1)
            failure = json.loads(failures[0].read_text())
            self.assertEqual(failure['input'], record)
            self.assertEqual(failure['lean_output'], [0, 1])
            self.assertEqual(failure['oracle_output'], [1, 1])

    def test_mixed_library_dispatch(self):
        determinant = json.loads(FIXTURES.read_text().splitlines()[0])
        records = [determinant, self.records[0]]
        driver = Path(__file__).with_name('matrix_carriers.py')
        stream = ''.join(json.dumps(r) + '\n' for r in records)
        result = subprocess.run([sys.executable, str(driver)], input=stream,
                                text=True, capture_output=True, check=True)
        self.assertIn('OK: 2 exact matrix carrier records', result.stdout)
        result = subprocess.run([sys.executable, str(driver), '--server'], input=stream,
                                text=True, capture_output=True, check=True)
        self.assertEqual([json.loads(line)['result'] for line in result.stdout.splitlines()],
                         [determinant['determinant'], self.records[0]['result']])

    def test_shared_fixture_reader(self):
        driver = Path(__file__).with_name('matrix_carriers.py')
        stream = '# canonical fixture with blank lines\n\n' + json.dumps(self.records[0]) + '\n'
        result = subprocess.run([sys.executable, str(driver)], input=stream,
                                text=True, capture_output=True, check=True)
        self.assertIn('OK: 1 exact matrix carrier records', result.stdout)

    def test_persistent_protocol_recovers_after_bad_request(self):
        driver = Path(__file__).with_name('matrix_carriers.py')
        requests = [{'kind': 'overhead'}, {'kind': 'unknown'}, self.records[0]]
        result = subprocess.run([sys.executable, str(driver), '--server'],
                                input=''.join(json.dumps(r) + '\n' for r in requests),
                                text=True, capture_output=True, check=True)
        replies = [json.loads(line) for line in result.stdout.splitlines()]
        self.assertEqual(replies[0], {'ok': True, 'result': 0})
        self.assertFalse(replies[1]['ok'])
        self.assertEqual(replies[2], {'ok': True, 'result': self.records[0]['result']})


if __name__ == '__main__':
    unittest.main()
