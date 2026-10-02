"""Regression checks for allocation capture validation and attribution."""
import copy
import unittest

from scripts.bench import sign_det_allocations as capture


class AllocationValidationTests(unittest.TestCase):
    def setUp(self):
        self.counts = {"callbacks": 1, "overflow": 0,
                       "lean_requests": 2, "lean_bytes": 64,
                       "mimalloc_requests": 2, "mimalloc_bytes": 56,
                       "gmp_requests": 2, "gmp_bytes": 160}
        self.dhat = {"mode": "ad-hoc", "ftbl": ["[root]",
                     "0x1: lean_alloc_object (in /capture/wrapper.so)",
                     "0x2: mi_malloc (in /capture/wrapper.so)",
                     "0x3: __gmp_default_allocate (in /capture/wrapper.so)"],
                     "pps": [{"tb": 64, "tbk": 2, "fs": [1]},
                             {"tb": 56, "tbk": 2, "fs": [2]},
                             {"tb": 160, "tbk": 2, "fs": [3]}]}

    def test_per_entry_point_events(self):
        capture.check_events(self.counts, self.dhat)

    def test_same_total_wrong_bucket_rejects(self):
        counts = dict(self.counts, lean_bytes=56, mimalloc_bytes=64)
        self.assertEqual(sum(counts[k + "_bytes"] for k in capture.KINDS), 280)
        with self.assertRaisesRegex(ValueError, "entry-point assignment"):
            capture.check_events(counts, self.dhat)

    def test_unknown_emitting_wrapper_rejects(self):
        dhat = copy.deepcopy(self.dhat)
        dhat["ftbl"][1] = "0x1: foreign_allocator (in /capture/wrapper.so)"
        with self.assertRaisesRegex(ValueError, "unclassified"):
            capture.check_events(self.counts, dhat)

    def test_missing_hash_does_not_prove_result_equivalence(self):
        row = '{"schema_version":1,"function":"f","param":3,"status":"ok",' \
              '"inner_repeats":1,"cache_mode":"cold","result_hash":null}'
        with self.assertRaisesRegex(ValueError, "missing hash"):
            capture.benchmark_row(row, "f", 3)

    def test_names_requiring_lean_escaping_reject(self):
        with self.assertRaisesRegex(ValueError, "plain alphanumeric"):
            capture.callback_type("Hex.SignDetBench.run_comparison")

    def test_repeated_callbacks_reject(self):
        import json
        counts = dict(self.counts, callbacks=2)
        with self.assertRaisesRegex(ValueError, "one nonoverflowing"):
            capture.counters("SIGN_DET_ALLOCATIONS " + json.dumps(counts))


if __name__ == "__main__":
    unittest.main()
