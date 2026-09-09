# Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
# Released under Apache 2.0 license as described in the file LICENSE.
# Authors: Kim Morrison

import copy
import json
from pathlib import Path
import tempfile
import unittest

from scripts.oracle.graphiso_trace import FIELDS, check, load, metadata


class TraceTest(unittest.TestCase):
    def setUp(self):
        output = dict.fromkeys(FIELDS, 0)
        output.update(canonlab=[0, 1], canong=[[1], [0]], autos=[[1, 0], [0, 1]],
                      bestCodes=[3, 4], orbits=[0, 0],
                      exit={"kind": "unwind", "level": 0, "short": False})
        self.row = {"corpus": "fixtures", "name": "edge",
                    "input": {"n": 2, "k": 1, "colors": [0, 0], "edges": [[0, 1]]},
                    "output": output}
        self.expected = {("fixtures", "edge"): self.row}

    def test_match(self):
        check(self.expected, copy.deepcopy(self.expected))

    def test_missing_and_added(self):
        for actual in [{}, {**self.expected, ("fixtures", "extra"): self.row}]:
            with self.assertRaisesRegex(ValueError, "trace cases differ"):
                check(self.expected, actual)

    def test_changed_fields(self):
        for field, value in [("canonlab", [1, 0]), ("canong", [[], []]),
                             ("autos", [[0, 1], [1, 0]]), ("bestCodes", [3, 5]),
                             ("orbits", [0, 1]), ("exit", {"kind": "fuel"})] + [
                                 (f, 7) for f in ["numnodes", "numorbits", "numgenerators",
                                                  "numbadleaves", "maxlevel", "tctotal", "canupdates"]]:
            with self.subTest(field=field):
                actual = copy.deepcopy(self.expected)
                actual[("fixtures", "edge")]["output"][field] = value
                with self.assertRaisesRegex(ValueError, "output." + field):
                    check(self.expected, actual)

    def test_bool_is_not_integer(self):
        actual = copy.deepcopy(self.expected)
        actual[("fixtures", "edge")]["output"]["numnodes"] = False
        with self.assertRaisesRegex(ValueError, "type"):
            check(self.expected, actual)

    def test_duplicate_empty_and_malformed(self):
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / "trace.jsonl"
            for text, error in [("", "empty"), ("{}\n", "invalid"),
                                ((json.dumps(self.row) + "\n") * 2, "duplicate")]:
                path.write_text(text)
                with self.assertRaisesRegex(ValueError, error):
                    load(path)

    def test_digest_covers_inputs_and_outputs(self):
        before = metadata(self.expected, "a" * 40)
        altered = copy.deepcopy(self.expected)
        altered[("fixtures", "edge")]["output"]["numnodes"] = 10
        after = metadata(altered, "a" * 40)
        self.assertEqual(before["corpus_sha256"], after["corpus_sha256"])
        self.assertNotEqual(before["trace_sha256"], after["trace_sha256"])
        altered[("fixtures", "edge")]["input"]["colors"] = [0, 1]
        self.assertNotEqual(before["corpus_sha256"], metadata(altered, "a" * 40)["corpus_sha256"])


if __name__ == "__main__":
    unittest.main()
