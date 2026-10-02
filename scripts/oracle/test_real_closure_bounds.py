"""Rejection tests for the exact finite-bound comparator."""

from copy import deepcopy
import json
from pathlib import Path
import subprocess
import sys
import unittest

from scripts.oracle.real_closure_bounds import verify


FIXTURES = Path(__file__).resolve().parents[2] / "conformance-fixtures/HexRealClosure/bounds.jsonl"
ORACLE = Path(__file__).with_name("real_closure_bounds.py")


class BoundsTests(unittest.TestCase):
    def setUp(self) -> None:
        self.fixtures = [json.loads(line) for line in FIXTURES.read_text().splitlines() if line.strip()]

    def test_accepts_emitted_data(self) -> None:
        verify(self.fixtures)

    def test_rejects_wrong_bounds(self) -> None:
        for name, value in (
            ("sqrt two", "2"),
            ("close roots", {"num": ["4"], "den": ["1"]}),
            ("inverse second infinitesimal", {
                "num": [{"num": ["2"], "den": ["1"]}],
                "den": [{"num": ["1"], "den": ["1"]}]}),
        ):
            with self.subTest(name=name):
                rows = deepcopy(self.fixtures)
                next(row for row in rows if row["name"] == name)["bound"] = value
                with self.assertRaises(ValueError):
                    verify(rows)

    def test_rejects_empty_or_duplicate_data(self) -> None:
        for rows in ([], self.fixtures + self.fixtures[:1]):
            with self.assertRaises(ValueError):
                verify(rows)

    def test_optimized_python_still_rejects(self) -> None:
        rows = deepcopy(self.fixtures)
        next(row for row in rows if row["name"] == "sqrt two")["bound"] = "2"
        result = subprocess.run(
            [sys.executable, "-O", str(ORACLE)],
            input="".join(json.dumps(row) + "\n" for row in rows),
            text=True, capture_output=True,
        )
        self.assertNotEqual(result.returncode, 0)
        self.assertIn("sqrt two: got 2, expected 4", result.stderr)


if __name__ == "__main__":
    unittest.main()
