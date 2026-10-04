"""Exact complete-query results, temporary-value lifetimes and protocol rejection."""
import json
from pathlib import Path
import subprocess
import sys
import unittest
from unittest import mock

from scripts.oracle import sturm_bench as bench


class ExactQueries(unittest.TestCase):
    def test_all_query_shapes(self):
        for factory in [bench.Flint, bench.Z3]:
            endpoint = factory()
            try:
                for name, expected in bench.EXPECTED.items():
                    with self.subTest(tool=factory.__name__, case=name):
                        self.assertEqual(endpoint.query(name), expected)
            finally:
                endpoint.close()

    def test_flint_temporary_values_are_released(self):
        endpoint = bench.Flint()
        self.addCleanup(endpoint.close)
        retained = len(endpoint.oracle.owned)
        for _ in range(20):
            for name, expected in bench.EXPECTED.items():
                self.assertEqual(endpoint.query(name), expected)
                self.assertEqual(len(endpoint.oracle.owned), retained)

    def test_unsupported_versions_fail_closed(self):
        with mock.patch.object(bench, "version", return_value="unsupported"):
            for factory in [bench.Flint, bench.Z3]:
                with self.subTest(tool=factory.__name__), self.assertRaises(RuntimeError):
                    factory()

    def test_protocol_results_and_rejections(self):
        requests = [json.dumps({"case": name}) for name in bench.EXPECTED]
        requests += [json.dumps({"case": "count", "control": True}),
                     json.dumps({"case": "unknown"}),
                     json.dumps({"case": "count", "control": "false"}), "not JSON"]
        for tool in ["flint", "z3"]:
            completed = subprocess.run([sys.executable, str(Path(bench.__file__)), "--tool", tool],
                input="\n".join(requests)+"\n", capture_output=True, text=True, check=True)
            replies = [json.loads(line) for line in completed.stdout.splitlines()]
            self.assertEqual(len(replies), len(requests))
            self.assertEqual(replies[:5], [{"ok": True, "result": value}
                for value in [8, 0, -8, 0, 8]])
            self.assertTrue(all(reply["ok"] is False and "result" not in reply
                                for reply in replies[5:]))


if __name__ == "__main__":
    unittest.main()
