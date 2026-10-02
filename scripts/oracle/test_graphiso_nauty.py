# Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
# Released under Apache 2.0 license as described in the file LICENSE.
# Authors: Kim Morrison

"""Regression tests for the independent dense/sparse nauty oracle protocol."""
import copy
import json
import math
import subprocess
import unittest

from scripts.oracle.common import FixtureError, OracleMismatch, _validate_fixture
from scripts.oracle.graphiso_nauty import (
    STAT_FIELDS, _build_shim, _check, _check_autos, _parse, _shim_input, check_records,
)


class NautyTest(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.shim = _build_shim()

    def run_graph(self, n, edges, *, sparse=True, colors=None, trace=False):
        colors = [0] * n if colors is None else colors
        record = {"kind": "graphisosparse" if sparse else "graphiso", "n": n,
                  "k": max(colors) + 1, "colors": colors, "edges": edges}
        proc = subprocess.run(
            [str(self.shim)] + (["--sparse"] if sparse else []) + (["--trace"] if trace else []),
            input=_shim_input(record) + "-1 -1\n", text=True,
            capture_output=True, check=True, timeout=20,
        )
        return _parse(proc.stdout.strip()), proc

    def matching_record(self):
        # The labels and adjacency here are pinned independently of parsing.
        return {"kind": "graphisosparseautos", "lib": "HexGraphIso", "case": "2K2",
                "n": 4, "k": 1, "colors": [0] * 4, "edges": [[0, 3], [1, 2]],
                "canonLab": [0, 1, 2, 3], "canonEdges": [[0, 3], [1, 2]],
                "cellSizes": [4], "numnodes": 6,
                "stats": dict(zip(STAT_FIELDS, [1, 2, 6, 0, 3, 8, 1])),
                "gens": [[0, 2, 1, 3], [1, 0, 3, 2]], "numGenerators": 2,
                "orbits": [0] * 4, "numOrbits": 1, "order": 8}

    def test_distinct_canonical_forms(self):
        sparse, _ = self.run_graph(4, [[0, 3], [1, 2]])
        dense, _ = self.run_graph(4, [[0, 3], [1, 2]], sparse=False)
        self.assertEqual(sparse["lab"], [0, 1, 2, 3])
        self.assertEqual(sparse["edges"], [[0, 3], [1, 2]])
        self.assertEqual(dense["lab"], [0, 3, 1, 2])
        self.assertEqual(dense["tri"], "100001")
        self.assertEqual(sparse["order"], dense["order"])
        record = self.matching_record()
        _validate_fixture(record)
        self.assertEqual(check_records([record]), (1, 1))

    def test_exact_large_order(self):
        for sparse in (False, True):
            with self.subTest(sparse=sparse):
                answer, _ = self.run_graph(30, [], sparse=sparse)
                self.assertEqual(answer["order"], math.factorial(30))
                self.assertEqual(answer["indices"], list(range(2, 31)))
                colored, _ = self.run_graph(30, [], sparse=sparse, colors=[0] * 17 + [1] * 13)
                self.assertEqual(colored["order"], math.factorial(17) * math.factorial(13))

    def test_reject_each_changed_result(self):
        answer, proc = self.run_graph(4, [[0, 3], [1, 2]])
        for field, value in [("canonLab", [1, 0, 2, 3]), ("canonEdges", [[0, 1], [2, 3]]),
                             ("cellSizes", [3, 1]), ("numnodes", 7), ("order", 9),
                             ("numOrbits", 2), ("orbits", [0, 1, 0, 1]),
                             ("numGenerators", 1), ("gens", [[0, 1, 2, 3]])]:
            with self.subTest(field=field):
                record = self.matching_record()
                record[field] = value
                with self.assertRaises(OracleMismatch):
                    _check(record, proc.stdout.strip())
                    _check_autos(record, answer)
        for field in STAT_FIELDS:
            with self.subTest(stat=field):
                record = self.matching_record()
                record["stats"][field] += 1
                with self.assertRaises(OracleMismatch):
                    _check(record, proc.stdout.strip())

    def test_trace_does_not_change_search(self):
        _, plain = self.run_graph(8, [[i, (i + 1) % 8] for i in range(8)])
        answer, traced = self.run_graph(8, [[i, (i + 1) % 8] for i in range(8)], trace=True)
        self.assertEqual(plain.stdout, traced.stdout)
        nodes = [json.loads(line) for line in traced.stderr.splitlines()]
        self.assertEqual(len(nodes), answer["nodes"])
        self.assertTrue(all(sorted(node["lab"]) == list(range(8)) for node in nodes))

    def test_sparse_protocol_duplicates(self):
        expected, _ = self.run_graph(4, [[0, 3], [1, 2]])
        # Bypass the Python normalizer to exercise C's own CSR compaction.
        proc = subprocess.run([str(self.shim), "--sparse"], text=True, capture_output=True,
                              input="4 1\n0 0 0 0\n5\n3 0\n1 2\n0 3\n2 1\n3 0\n-1 -1\n",
                              check=True, timeout=20)
        self.assertEqual(_parse(proc.stdout.strip()), expected)

    def test_malformed_sparse_input(self):
        for data in ["2 1\n0 0\n1\n0 0\n", "2 1\n0 0\n1\n0 2\n",
                     "2 2\n0 0\n0\n", "2 1\n0 0\n1\n0\n", "2\n"]:
            with self.subTest(data=data):
                proc = subprocess.run([str(self.shim), "--sparse"], input=data,
                                      text=True, capture_output=True, timeout=20)
                self.assertNotEqual(proc.returncode, 0)

    def test_extra_trace_entry_must_be_automorphism(self):
        answer, _ = self.run_graph(4, [[0, 3], [1, 2]])
        record = self.matching_record()
        # C's emissions remain an ordered subsequence. Permutation validity
        # alone would allow this non-automorphism to pass.
        record["gens"].append([1, 0, 2, 3])
        with self.assertRaises(OracleMismatch):
            _check_autos(record, answer)

    def test_empty_statistics(self):
        record = dict(kind="graphisosparse", case="empty", n=0, k=0, colors=[],
                      edges=[], canonLab=[], canonEdges=[], cellSizes=[], numnodes=1,
                      stats=dict(zip(STAT_FIELDS, [0, 0, 1, 0, 1, 0, 1])))
        _check(record, None)
        for field in STAT_FIELDS:
            changed = copy.deepcopy(record)
            changed["stats"][field] += 1
            with self.subTest(field=field), self.assertRaises(OracleMismatch):
                _check(changed, None)

    def test_malformed_sparse_fixture(self):
        for field, value in [("canonEdges", [[0, 3], [0, 3]]), ("canonEdges", [[1, 1]]),
                             ("canonEdges", [[False, 3]]), ("stats", {})]:
            record = copy.deepcopy(self.matching_record())
            record[field] = value
            with self.subTest(field=field, value=value), self.assertRaises(FixtureError):
                _validate_fixture(record)


if __name__ == "__main__":
    unittest.main()
