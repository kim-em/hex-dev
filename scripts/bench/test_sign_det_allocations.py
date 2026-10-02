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
        capture.check_events(self.counts, self.dhat, "/capture/wrapper.so")

    def test_same_total_wrong_bucket_rejects(self):
        counts = dict(self.counts, lean_bytes=56, mimalloc_bytes=64)
        self.assertEqual(sum(counts[k + "_bytes"] for k in capture.KINDS), 280)
        with self.assertRaisesRegex(ValueError, "entry-point assignment"):
            capture.check_events(counts, self.dhat, "/capture/wrapper.so")

    def test_unknown_emitting_wrapper_rejects(self):
        dhat = copy.deepcopy(self.dhat)
        dhat["ftbl"][1] = "0x1: foreign_allocator (in /capture/wrapper.so)"
        with self.assertRaisesRegex(ValueError, "unclassified"):
            capture.check_events(self.counts, dhat, "/capture/wrapper.so")

    def test_real_allocator_frame_is_not_a_wrapper_event(self):
        dhat = copy.deepcopy(self.dhat)
        dhat["ftbl"][1] = "0x1: lean_alloc_object (in /capture/real-benchmark)"
        with self.assertRaisesRegex(ValueError, "expected wrapper"):
            capture.check_events(self.counts, dhat, "/capture/wrapper.so")

    def test_missing_hash_does_not_prove_result_equivalence(self):
        row = '{"schema_version":1,"function":"f","param":3,"status":"ok",' \
              '"inner_repeats":1,"cache_mode":"cold","result_hash":null}'
        with self.assertRaisesRegex(ValueError, "missing hash"):
            capture.benchmark_row(row, "f", 3)

    def test_names_requiring_lean_escaping_reject(self):
        with self.assertRaisesRegex(ValueError, "plain alphanumeric"):
            capture.callback_type("Hex.SignDetBench.run_comparison")

    def test_retained_clean_capture(self):
        import gzip
        import hashlib
        import json
        from pathlib import Path
        root = Path(__file__).resolve().parents[2] / "reports/data/sign-det-allocations/validation"
        meta = json.loads((root / "metadata.json").read_text())
        self.assertEqual(meta["state"], "complete")
        self.assertEqual(meta["git_status"], "")
        self.assertTrue(meta["source_unchanged"])
        self.assertEqual(meta["source_sha256"], meta["source_sha256_after"])
        self.assertEqual(meta["binary_sha256"], meta["binary_sha256_after"])
        for name, expected in meta["collector_sha256"].items():
            self.assertEqual(capture.digest(root / "collector-sources" / name), expected)
        rows = [json.loads(line) for line in (root / "samples.jsonl").read_text().splitlines()]
        self.assertEqual(rows, meta["samples"])
        self.assertEqual(len(rows), 2)
        for i, row in enumerate(rows):
            stem = f"{i:03d}"
            log = root / (stem + ".log")
            native = root / (stem + ".native.log")
            self.assertEqual(capture.digest(log), row["log_sha256"])
            self.assertEqual(capture.digest(native), row["native_log_sha256"])
            original = capture.benchmark_row(native.read_text(), row["function"], row["parameter"])
            instrumented = capture.benchmark_row(log.read_text(), row["function"], row["parameter"])
            self.assertEqual(original["result_hash"], row["result_hash"])
            self.assertEqual(instrumented["result_hash"], row["result_hash"])
            raw = gzip.decompress((root / (stem + ".dhat.json.gz")).read_bytes())
            self.assertEqual(hashlib.sha256(raw).hexdigest(), row["dhat_sha256"])
            wrapper = next(arg.removeprefix("env LD_PRELOAD=").split()[0]
                           for arg in row["command"] if arg.startswith("env LD_PRELOAD="))
            capture.check_events(row["counters"], json.loads(raw), wrapper)
            self.assertEqual(capture.counters(log.read_text()), row["counters"])
        self.assertEqual(len(meta["self_checks"]), 3)
        for i, check in enumerate(meta["self_checks"]):
            log = root / f"self-check-{i}.log"
            self.assertEqual(capture.digest(log), check["log_sha256"])
            raw = gzip.decompress((root / f"self-check-{i}.dhat.json.gz").read_bytes())
            self.assertEqual(hashlib.sha256(raw).hexdigest(), check["dhat_sha256"])
            capture.check_events(check["counters"], json.loads(raw),
                                 Path(meta["compile_commands"][i][-1]))

    def test_retained_joint_capture(self):
        import gzip
        import hashlib
        import json
        from pathlib import Path
        root = Path(__file__).resolve().parents[2] / "reports/data/sign-det-allocations/joint-25b179f5c"
        meta = json.loads((root / "metadata.json").read_text())
        self.assertEqual(meta["state"], "complete")
        self.assertEqual(meta["git_status"], "")
        self.assertTrue(meta["source_unchanged"])
        self.assertEqual(meta["source_sha256"], meta["source_sha256_after"])
        self.assertEqual(meta["binary_sha256"], meta["binary_sha256_after"])
        for name, expected in meta["collector_sha256"].items():
            self.assertEqual(capture.digest(root / "collector-sources" / name), expected)
        rows = [json.loads(line) for line in (root / "samples.jsonl").read_text().splitlines()]
        self.assertEqual(rows, meta["samples"])
        schedule = [(trial, n, f) for trial in range(1, meta["trials"] + 1)
                    for n in meta["parameters"] for f in meta["functions"]]
        self.assertEqual([(r["trial"], r["parameter"], r["function"]) for r in rows], schedule)
        self.assertEqual(len(rows), 36)
        observations = {}
        for i, row in enumerate(rows):
            self.assertEqual(row["state"], "complete")
            stem = f"{i:03d}"
            log = root / (stem + ".log")
            native = root / (stem + ".native.log")
            self.assertEqual(capture.digest(log), row["log_sha256"])
            self.assertEqual(capture.digest(native), row["native_log_sha256"])
            original = capture.benchmark_row(native.read_text(), row["function"], row["parameter"])
            instrumented = capture.benchmark_row(log.read_text(), row["function"], row["parameter"])
            self.assertEqual(original["result_hash"], row["result_hash"])
            self.assertEqual(instrumented["result_hash"], row["result_hash"])
            raw = gzip.decompress((root / (stem + ".dhat.json.gz")).read_bytes())
            self.assertEqual(hashlib.sha256(raw).hexdigest(), row["dhat_sha256"])
            wrapper = next(arg.removeprefix("env LD_PRELOAD=").split()[0]
                           for arg in row["command"] if arg.startswith("env LD_PRELOAD="))
            capture.check_events(row["counters"], json.loads(raw), wrapper)
            self.assertEqual(capture.counters(log.read_text()), row["counters"])
            key = row["function"], row["parameter"]
            if key in observations:
                self.assertEqual(row["counters"], observations[key])
            observations[key] = row["counters"]

    def test_repeated_callbacks_reject(self):
        import json
        counts = dict(self.counts, callbacks=2)
        with self.assertRaisesRegex(ValueError, "one nonoverflowing"):
            capture.counters("SIGN_DET_ALLOCATIONS " + json.dumps(counts))


if __name__ == "__main__":
    unittest.main()
