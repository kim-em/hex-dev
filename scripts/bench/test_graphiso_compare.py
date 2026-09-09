# Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
# Released under Apache 2.0 license as described in the file LICENSE.
# Authors: Kim Morrison

import json
from pathlib import Path
import tempfile
import unittest

from scripts.bench.graphiso_archive import normalize
from scripts.bench.graphiso_compare import compare, load


class CompareTest(unittest.TestCase):
    def test_archive(self):
        self.assertEqual(normalize({"eng_ns": 10, "eng_nodes": 2, "lit_ns": 20,
                                    "nodes": 3})["search_ns"], 10)
        self.assertEqual(normalize({"lit_ns": 20})["search_ns"], 20)
        self.assertEqual(normalize({"search_ns": 30, "eng_ns": 10})["search_ns"], 30)

    def test_time_and_traversal_are_separate(self):
        before = {("f", "g", 3): {"search_ns": 100, "nodes": 2}}
        after = {("f", "g", 3): {"search_ns": 50, "nodes": 4}}
        table, changed = compare(before, after, "search_ns")
        self.assertEqual(table, [("f", 1, 0.5, 0.5)])
        self.assertEqual(changed, [("g", 2, 4)])

    def test_incompatible_corpora(self):
        before = {("f", "g", 3): {"search_ns": 100, "nodes": 2}}
        for after in [{}, {("f", "g", 4): {"search_ns": 100, "nodes": 2}}]:
            with self.assertRaisesRegex(ValueError, "incompatible corpora"):
                compare(before, after, "search_ns")

    def test_bad_measurements(self):
        row = {"family": "f", "name": "g", "n": 3, "nodes": 2, "search_ns": 10}
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / "sweep.jsonl"
            for records in [[], [row, row], [{**row, "search_ns": 0}], [{**row, "nodes": False}]]:
                path.write_text("\n".join(map(json.dumps, records)))
                with self.assertRaises(ValueError):
                    load(path, "search_ns")


if __name__ == "__main__":
    unittest.main()
