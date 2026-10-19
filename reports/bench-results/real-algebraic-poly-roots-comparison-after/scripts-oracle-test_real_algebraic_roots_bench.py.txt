"""Exact root fingerprints, ownership and persistent endpoint rejection."""
import json
from pathlib import Path
import subprocess
import sys
import unittest
from unittest import mock

from scripts.oracle import real_algebraic_roots_bench as bench


class Roots(unittest.TestCase):
    def test_exact_families_and_cleanup(self):
        for factory in (bench.Flint, bench.Z3):
            for quadratic in (False, True):
                for degree in (1, 2, 4, 8, 16):
                    endpoint = factory(degree, quadratic)
                    try:
                        retained = len(endpoint.oracle.owned) if factory is bench.Flint else None
                        for _ in range(2):
                            self.assertEqual(endpoint.roots(), bench.fingerprint(degree, quadratic))
                            if retained is not None:
                                self.assertEqual(len(endpoint.oracle.owned), retained)
                    finally:
                        endpoint.close()

    def test_exact_annihilation_guard(self):
        for factory in (bench.Flint, bench.Z3):
            endpoint = factory(2, False)
            try:
                endpoint.target = (endpoint.oracle.number(3) if factory is bench.Flint
                    else endpoint.api.RCFNum(3, endpoint.context))
                with self.assertRaisesRegex(ArithmeticError, "annihilation"):
                    endpoint.roots()
            finally:
                endpoint.close()

    def test_protocol_rejects_malformed_fixtures(self):
        requests = [dict(degree=4, quadratic=True), dict(degree=4, quadratic=True, control=True)]
        requests += [dict(degree=d, quadratic=False) for d in (True, 0, 3, 4.0, "4", 32)]
        requests += [dict(degree=4, quadratic=q) for q in (0, "false", None)]
        requests += [dict(degree=4, quadratic=False, control="false"), {}]
        for tool in ("flint", "z3"):
            done = subprocess.run([sys.executable, str(Path(bench.__file__)), "--tool", tool],
                input="\n".join(map(json.dumps, requests))+"\nnot JSON\n",
                capture_output=True, text=True, check=True)
            replies = [json.loads(line) for line in done.stdout.splitlines()]
            self.assertEqual(len(replies), len(requests) + 1)
            self.assertEqual(replies[:2], [{"ok": True, "result": bench.fingerprint(4, True)}] * 2)
            self.assertTrue(all(r["ok"] is False and "result" not in r for r in replies[2:]))

    def test_unsupported_z3_version(self):
        with mock.patch.object(bench, "version", return_value="unsupported"):
            with self.assertRaises(RuntimeError):
                bench.Z3(2, False)


if __name__ == "__main__":
    unittest.main()
