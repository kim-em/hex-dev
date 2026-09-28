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

    def change_split(self, name: str, field: str, value) -> list[dict]:
        rows = deepcopy(self.fixtures)
        next(row for row in rows if row["name"] == name)["result"][field] = value
        return rows

    def test_rejects_missing_midpoint(self) -> None:
        with self.assertRaisesRegex(ValueError, "wrong removed point"):
            verify(self.change_split("split cubic root cut", "removed", False))

    def test_rejects_invented_midpoint(self) -> None:
        with self.assertRaisesRegex(ValueError, "wrong removed point"):
            verify(self.change_split("split regular quadratic", "removed", True))

    def test_rejects_split_scalar_loss(self) -> None:
        with self.assertRaisesRegex(ValueError, "wrong active head or scalar"):
            verify(self.change_split("split cubic root cut", "active", ["-2", "0", "1"]))

    def test_rejects_stale_split_head(self) -> None:
        original = next(row for row in self.fixtures if row["name"] == "split cubic root cut")["coefficients"]
        with self.assertRaisesRegex(ValueError, "wrong left head"):
            verify(self.change_split("split cubic root cut", "left_head", original))

    def test_rejects_wrong_split_endpoint(self) -> None:
        with self.assertRaisesRegex(ValueError, "wrong left upper endpoint"):
            verify(self.change_split("split cubic root cut", "left_upper", {"finite": "2"}))

    def test_rejects_duplicate_cut_root(self) -> None:
        with self.assertRaisesRegex(ValueError, "wrong left count"):
            verify(self.change_split("split cubic root cut", "left_count", 1))

    def test_rejects_lost_infinitesimal_root(self) -> None:
        with self.assertRaisesRegex(ValueError, "wrong left count"):
            verify(self.change_split("split close infinitesimal roots", "left_count", 1))

    def test_rejects_nested_order_reversal(self) -> None:
        with self.assertRaisesRegex(ValueError, "wrong left count"):
            verify(self.change_split("split first infinitesimal root", "left_count", 0))

    def test_rejects_valid_split_failure(self) -> None:
        with self.assertRaisesRegex(ValueError, "wrong split success"):
            verify(self.changed("split constant", "result", None))

    def test_rejects_invalid_split_success(self) -> None:
        with self.assertRaisesRegex(ValueError, "wrong split success"):
            verify(self.changed("split repeated root", "result", {}))

    def test_rejects_inexact_midpoint(self) -> None:
        with self.assertRaisesRegex(ValueError, "wrong midpoint"):
            verify(self.changed("split regular quadratic", "point", "0.99"))

    def test_rejects_unknown_fixture_kind(self) -> None:
        with self.assertRaisesRegex(ValueError, "unknown fixture kind"):
            verify(self.changed("split constant", "kind", "unknown"))

    def test_rejects_empty_and_duplicate_data(self) -> None:
        for rows in ([], self.fixtures + self.fixtures[:1]):
            with self.assertRaises(ValueError):
                verify(rows)


if __name__ == "__main__":
    unittest.main()
