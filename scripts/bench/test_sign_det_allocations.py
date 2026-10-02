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

    def check_self_checks(self, root, meta):
        import gzip
        import hashlib
        import json
        from pathlib import Path
        expected = {"callbacks": 1, "overflow": 0, "lean_requests": 2, "lean_bytes": 64,
                    "mimalloc_requests": 2, "mimalloc_bytes": 56, "gmp_requests": 2, "gmp_bytes": 160}
        self.assertEqual(len(meta["self_checks"]), 3)
        abis = [("void*", "0x12345678u"), ("uint8_t", "0xabu"),
                ("uint64_t", "0xfedcba9876543210ULL")]
        for i, check in enumerate(meta["self_checks"]):
            self.assertEqual((check["result_type"], check["returned_value"]), abis[i])
            self.assertEqual(check["counters"], expected)
            log = root / f"self-check-{i}.log"
            self.assertEqual(capture.digest(log), check["log_sha256"])
            self.assertEqual(capture.counters(log.read_text()), expected)
            raw = gzip.decompress((root / f"self-check-{i}.dhat.json.gz").read_bytes())
            self.assertEqual(hashlib.sha256(raw).hexdigest(), check["dhat_sha256"])
            capture.check_events(check["counters"], json.loads(raw),
                                 Path(meta["compile_commands"][i][-1]))

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
        self.check_self_checks(root, meta)

    def test_retained_joint_capture(self):
        import gzip
        import hashlib
        import json
        from pathlib import Path
        root = Path(__file__).resolve().parents[2] / "reports/data/sign-det-allocations/joint-25b179f5c"
        meta = json.loads((root / "metadata.json").read_text())
        self.assertEqual(meta["state"], "complete")
        self.assertEqual(meta["revision"], "25b179f5c8f2143cd77753cd8c802d364aefd958")
        self.assertEqual(meta["parameters"], [3, 7, 15])
        self.assertEqual(meta["trials"], 3)
        self.assertEqual(meta["host"], "chungus2")
        self.assertEqual(meta["cpu"], 56)
        self.assertEqual(meta["functions"], ["Hex.SignDetBench.Joint." + name for name in
                         ["runCompletion", "runComparison", "runCheckReduced", "runCheckDirect"]])
        self.check_self_checks(root, meta)
        timing_root = root.parents[1] / "sign-det-joint-timing/394c3c548"
        expected_answers = {}
        for name in ["runCompletion", "runComparison"]:
            prior = json.loads((timing_root / (name + ".json")).read_text())
            for result in prior["results"]:
                for point in result["points"]:
                    if point["status"] == "ok":
                        key = "Hex.SignDetBench.Joint." + name, point["param"]
                        if key in expected_answers:
                            self.assertEqual(expected_answers[key], point["result_hash"])
                        expected_answers[key] = point["result_hash"]
        for name in ["runCheckReduced", "runCheckDirect"]:
            for n in [3, 7, 15]:
                expected_answers["Hex.SignDetBench.Joint." + name, n] = "0xb"
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
            self.assertEqual(row["result_hash"], expected_answers[row["function"], row["parameter"]])
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

        report = (root.parents[2] / "sign-det-joint-allocations.md").read_text()
        operation_names = {"Completion": "runCompletion", "Comparison": "runComparison",
                           "Reduced replay": "runCheckReduced", "Direct replay": "runCheckDirect"}
        table = []
        for line in report.splitlines():
            cells = [c.strip() for c in line.split("|")]
            if len(cells) == 8 and cells[1].isdigit() and cells[2] in operation_names:
                function = "Hex.SignDetBench.Joint." + operation_names[cells[2]]
                values = [int(cell.replace(",", "")) for cell in cells[3:7]]
                counts = observations[function, int(cells[1])]
                actual = [counts[kind + "_bytes"] for kind in capture.KINDS]
                self.assertEqual(values, actual + [sum(actual)])
                table.append((function, int(cells[1])))
        self.assertEqual(set(table), set(observations))
        self.assertEqual(len(table), len(observations))

    def check_supplement(self, directory, functions, parameters, trials, cpu):
        import gzip
        import hashlib
        import json
        from pathlib import Path
        base = Path(__file__).resolve().parents[2] / "reports/data/sign-det-allocations"
        root = base / directory
        meta = json.loads((root / "metadata.json").read_text())
        main = json.loads((base / "joint-25b179f5c/metadata.json").read_text())
        self.assertEqual(meta["state"], "complete")
        self.assertEqual(meta["git_status"], "")
        self.assertTrue(meta["source_unchanged"])
        self.assertEqual(meta["revision"], main["revision"])
        self.assertEqual(meta["host"], "chungus2")
        self.assertEqual(meta["cpu"], cpu)
        self.assertEqual(meta["functions"], functions)
        self.assertEqual(meta["parameters"], parameters)
        self.assertEqual(meta["trials"], trials)
        self.assertEqual(meta["source_sha256"], main["source_sha256"])
        self.assertEqual(meta["source_sha256_after"], main["source_sha256"])
        self.assertEqual(meta["binary_sha256"], main["binary_sha256"])
        self.assertEqual(meta["binary_sha256_after"], main["binary_sha256"])
        for name, expected in meta["collector_sha256"].items():
            self.assertEqual(capture.digest(root / "collector-sources" / name), expected)
        self.check_self_checks(root, meta)
        rows = [json.loads(line) for line in (root / "samples.jsonl").read_text().splitlines()]
        self.assertEqual(rows, meta["samples"])
        schedule = [(trial, n, f) for trial in range(1, trials + 1)
                    for n in parameters for f in functions]
        self.assertEqual([(r["trial"], r["parameter"], r["function"]) for r in rows], schedule)
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
        return meta, rows

    def test_retained_production_capture(self):
        import json
        from pathlib import Path
        functions = ["Hex.SignDetBench.Joint.runReduced", "Hex.SignDetBench.Joint.runDirect"]
        meta, rows = self.check_supplement("joint-production-25b179f5c", functions, [3, 7, 15], 3, 46)
        timing = Path(__file__).resolve().parents[2] / "reports/data/sign-det-joint-timing/394c3c548"
        expected = {}
        for line in (timing / "production.jsonl").read_text().splitlines():
            record = json.loads(line)
            if record["kind"] == "sample" and record["point"]["status"] == "ok":
                key = record["arm"], record["point"]["param"]
                answer = record["point"]["result_hash"]
                if key in expected:
                    self.assertEqual(expected[key], answer)
                expected[key] = answer
        for row in rows:
            self.assertEqual(row["result_hash"], expected[row["function"], row["parameter"]])
        report = (timing.parents[2] / "sign-det-joint-allocations.md").read_text()
        observed = {(r["function"], r["parameter"]): r["counters"] for r in rows}
        operations = {"Reduced production": functions[0], "Direct production": functions[1]}
        table = []
        for line in report.splitlines():
            cells = [c.strip() for c in line.split("|")]
            if len(cells) == 8 and cells[1].isdigit() and cells[2] in operations:
                key = operations[cells[2]], int(cells[1])
                actual = [observed[key][kind + "_bytes"] for kind in capture.KINDS]
                self.assertEqual([int(c.replace(",", "")) for c in cells[3:7]], actual + [sum(actual)])
                table.append(key)
        self.assertEqual(set(table), set(observed))
        self.assertEqual(len(table), len(observed))

    def test_retained_comparison_31(self):
        import json
        from pathlib import Path
        meta, rows = self.check_supplement("comparison-31-25b179f5c",
            ["Hex.SignDetBench.Joint.runComparison"], [31], 1, 59)
        self.assertEqual(len(rows), 1)
        row = rows[0]
        self.assertEqual(row["counters"]["gmp_requests"], 386473472)
        self.assertGreaterEqual(row["counters"]["gmp_requests"], 385922080)
        timing = Path(__file__).resolve().parents[2] / "reports/data/sign-det-joint-timing/394c3c548/runComparison.json"
        hashes = {point["result_hash"] for result in json.loads(timing.read_text())["results"]
                  for point in result["points"] if point["param"] == 31 and point["status"] == "ok"}
        self.assertEqual(hashes, {row["result_hash"]})

    def test_joint_source_reconstruction(self):
        import gzip
        import hashlib
        import json
        import os
        from pathlib import Path
        import subprocess
        import tempfile
        root = Path(__file__).resolve().parents[2] / "reports/data/sign-det-allocations/joint-25b179f5c"
        meta = json.loads((root / "metadata.json").read_text())
        generated = gzip.decompress((root / "generated-joint.c.gz").read_bytes())
        self.assertEqual({hashlib.sha256(generated).hexdigest()},
                         {c["generated_c_sha256"] for c in meta["callbacks"].values()})
        reconstruction = json.loads((root / "source-reconstruction.json").read_text())
        patch = root / "committed-source.patch"
        self.assertEqual(capture.digest(patch), reconstruction["patch_sha256"])
        with tempfile.TemporaryDirectory() as temporary:
            env = dict(os.environ, GIT_INDEX_FILE=str(Path(temporary) / "index"))
            subprocess.run(["git", "read-tree", reconstruction["base"]], env=env, check=True)
            subprocess.run(["git", "apply", "--cached", str(patch)], env=env, check=True)
            self.assertEqual(set(reconstruction["paths"]), set(meta["source_sha256"]))
            for name, expected in meta["source_sha256"].items():
                content = subprocess.check_output(["git", "show", ":" + name], env=env)
                self.assertEqual(hashlib.sha256(content).hexdigest(), expected, name)
        post = json.loads((root / "post-capture-build-identity.json").read_text())
        self.assertEqual(post["binary_sha256"], meta["binary_sha256"])
        self.assertIn("post-capture", post["scope"])
        for name, expected in post["disassembly"].items():
            self.assertEqual(capture.digest(root / name), expected)
            self.assertIn("<lean_alloc_small_object_core>", (root / name).read_text())

    def test_repeated_callbacks_reject(self):
        import json
        counts = dict(self.counts, callbacks=2)
        with self.assertRaisesRegex(ValueError, "one nonoverflowing"):
            capture.counters("SIGN_DET_ALLOCATIONS " + json.dumps(counts))


if __name__ == "__main__":
    unittest.main()
