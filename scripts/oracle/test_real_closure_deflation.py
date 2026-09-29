"""Reject incorrect exact division and residual-root results."""

from copy import deepcopy
import json
from pathlib import Path
import unittest

from scripts.oracle.real_closure_deflation import verify


FIXTURES = Path(__file__).resolve().parents[2] / "conformance-fixtures/HexRealClosure/deflation.jsonl"


class DeflationTests(unittest.TestCase):
    def setUp(self) -> None:
        self.fixtures = [json.loads(line) for line in FIXTURES.read_text().splitlines() if line.strip()]

    def changed(self, name: str, field: str, value) -> list[dict]:
        rows = deepcopy(self.fixtures)
        next(row for row in rows if row["name"] == name)[field] = value
        return rows

    def test_accepts_emitted_data(self) -> None:
        verify(self.fixtures)

    def test_rejects_nonroot_success(self) -> None:
        with self.assertRaisesRegex(ValueError, "not a root: wrong success result"):
            verify(self.changed("not a root", "quotient", ["1"]))

    def test_rejects_root_failure(self) -> None:
        with self.assertRaisesRegex(ValueError, "linear: wrong success result"):
            verify(self.changed("linear", "quotient", None))

    def test_rejects_failed_division_payload(self) -> None:
        with self.assertRaisesRegex(ValueError, "not a root: result on failed division"):
            verify(self.changed("not a root", "remaining_at_root", "0"))

    def test_rejects_missing_scalar(self) -> None:
        with self.assertRaisesRegex(ValueError, "nonmonic fractional root: wrong quotient or scalar"):
            verify(self.changed("nonmonic fractional root", "quotient", ["1"]))

    def test_rejects_second_removal_of_repeated_root(self) -> None:
        with self.assertRaisesRegex(ValueError, "repeated root: wrong quotient or scalar"):
            verify(self.changed("repeated root", "quotient", ["1"]))

    def test_rejects_wrong_nested_quotient(self) -> None:
        with self.assertRaisesRegex(ValueError, "remove second infinitesimal: wrong quotient or scalar"):
            verify(self.changed("remove second infinitesimal", "quotient", []))

    def test_rejects_wrong_residual_evaluation(self) -> None:
        with self.assertRaisesRegex(ValueError, "repeated root: wrong residual evaluation"):
            verify(self.changed("repeated root", "remaining_at_root", "1"))

    def test_rejects_wrong_zero_multiplicity(self) -> None:
        for multiplicity in (0, 1, 3, -1, True):
            with self.assertRaisesRegex(ValueError, "wrong zero multiplicity"):
                verify(self.changed("extract mixed fractional scalar", "multiplicity", multiplicity))

    def test_rejects_zero_quotient_scalar_loss(self) -> None:
        with self.assertRaisesRegex(ValueError, "wrong zero quotient or scalar"):
            verify(self.changed("extract pure power", "cofactor", ["1"]))

    def test_rejects_zero_polynomial_finite_payload(self) -> None:
        with self.assertRaisesRegex(ValueError, "wrong zero quotient or scalar"):
            verify(self.changed("extract zero polynomial", "cofactor", ["1"]))

    def test_rejects_zero_polynomial_multiplicity(self) -> None:
        with self.assertRaisesRegex(ValueError, "wrong zero multiplicity"):
            verify(self.changed("extract zero polynomial", "multiplicity", 1))

    def test_rejects_malformed_zero_factor_fields(self) -> None:
        for rows in (
            self.changed("extract pure power", "kind", "zero-facor"),
            self.changed("extract pure power", "root", "0"),
        ):
            with self.assertRaises(ValueError):
                verify(rows)

    def test_rejects_empty_and_duplicate_data(self) -> None:
        for rows in ([], self.fixtures + self.fixtures[:1]):
            with self.assertRaises(ValueError):
                verify(rows)


if __name__ == "__main__":
    unittest.main()
