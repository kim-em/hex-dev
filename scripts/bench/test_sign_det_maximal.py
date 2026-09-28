"""Reject incomplete or corrupted inventories before marking provenance complete."""
import copy
import json
from pathlib import Path
from tempfile import TemporaryDirectory
import unittest

from sign_det_maximal import ROOT, validate_inventory


class MaximalInventoryTests(unittest.TestCase):
    def setUp(self):
        fixture = ROOT / "reports/data/sign-det-maximal/247dfcc2c/inventory.jsonl"
        self.rows = [json.loads(line) for line in fixture.read_text().splitlines()]

    def validate(self, rows):
        with TemporaryDirectory() as directory:
            path = Path(directory) / "inventory.jsonl"
            path.write_text("".join(json.dumps(row) + "\n" for row in rows))
            return validate_inventory(path)

    def test_retained_known_root_inventory(self):
        self.assertEqual(self.validate(self.rows), self.rows)

    def test_incomplete_duplicate_or_reordered_schedule(self):
        for rows in (self.rows[:-1], self.rows + self.rows[:1], self.rows[::-1]):
            with self.subTest(rows=rows), self.assertRaises(ValueError):
                self.validate(rows)

    def test_wrong_support_or_missing_graph_edge(self):
        for key in ("rootCount", "realizedSupport", "maxColumns", "graphEdges"):
            rows = copy.deepcopy(self.rows)
            rows[1][key] -= 1
            with self.subTest(key=key), self.assertRaises(ValueError):
                self.validate(rows)

    def test_invalid_sizes_and_hashes(self):
        for key, value in (("querySlots", -1), ("headCoefficientBits", True),
                           ("inputHash", -1), ("tableHash", 2**64)):
            rows = copy.deepcopy(self.rows)
            rows[0][key] = value
            with self.subTest(key=key), self.assertRaises(ValueError):
                self.validate(rows)


if __name__ == "__main__":
    unittest.main()
