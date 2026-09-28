#!/usr/bin/env python3
"""Check literal identity, both roots and actual joint-list dimensions."""
import copy
import json
import hashlib
from pathlib import Path
import tempfile
import unittest

from scripts.bench.sign_det_joint import RECORDED, expected, validate


class JointValidation(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.path = Path(self.temp.name) / "inventory.jsonl"
        self.rows = [expected(3, side) | dict.fromkeys(RECORDED, 1) for side in ("left", "right")]

    def check(self, rows):
        self.path.write_text("\n".join(map(json.dumps, rows)))
        return validate(self.path, [3])

    def test_complete(self):
        self.assertEqual(self.check(self.rows), 2)
        self.assertEqual(len(self.rows[0]["queries"]), 10)
        self.assertEqual(self.rows[0]["table"][1][0][6], -1)
        self.assertEqual(self.rows[1]["table"][1][0][6], 0)

    def test_copied_binding_and_missing_root(self):
        for key in ("source", "queries", "sourceSigns", "table"):
            with self.subTest(key=key), self.assertRaises(ValueError):
                rows = copy.deepcopy(self.rows)
                rows[0][key] = rows[1][key]
                self.check(rows)
        self.rows[0]["table"] = self.rows[0]["table"][1:]
        with self.assertRaises(ValueError):
            self.check(self.rows)

    def test_dimensions(self):
        for field in ("querySlots", "treeNodes", "graphNodes", "graphEdges", "maxColumns"):
            with self.subTest(field=field), self.assertRaises(ValueError):
                rows = copy.deepcopy(self.rows)
                rows[0][field] += 1
                self.check(rows)

    def test_retained_hash_binding(self):
        self.check(self.rows)
        patch = self.path.parent / "committed-source.patch"
        patch.write_bytes(b"literal source archive")
        metadata = {"state": "complete",
                    "inventory_sha256": hashlib.sha256(self.path.read_bytes()).hexdigest(),
                    "source_archive": {"file": patch.name,
                                       "sha256": hashlib.sha256(patch.read_bytes()).hexdigest()}}
        metadata_path = self.path.parent / "metadata.json"
        metadata_path.write_text(json.dumps(metadata))
        self.assertEqual(validate(self.path, [3], retained=True), 2)
        # Positive counts would pass shape validation, but cannot silently alter retained data.
        changed = copy.deepcopy(self.rows)
        changed[0]["reducedGraphBytes"] += 1
        self.assertEqual(self.check(changed), 2)
        with self.assertRaisesRegex(ValueError, "inventory hash"):
            validate(self.path, [3], retained=True)
        self.check(self.rows)
        patch.write_bytes(b"changed archive")
        with self.assertRaisesRegex(ValueError, "archive hash"):
            validate(self.path, [3], retained=True)
        metadata["state"] = "running"
        metadata_path.write_text(json.dumps(metadata))
        with self.assertRaisesRegex(ValueError, "not complete"):
            validate(self.path, [3], retained=True)

    def test_shape_and_integer_spoof(self):
        for key, value in (("degree", 3.0), ("context", True), ("order", "lt"),
                           ("maxInverseBits", True), ("reducedGraphBytes", 0),
                           ("reducedQueryWitnessBits", 1)):
            with self.subTest(key=key), self.assertRaises(ValueError):
                rows = copy.deepcopy(self.rows)
                rows[0][key] = value
                self.check(rows)
        with self.assertRaises(ValueError):
            self.check(self.rows[::-1])
        with self.assertRaises(ValueError):
            self.check(self.rows[:1])


if __name__ == "__main__":
    unittest.main()
