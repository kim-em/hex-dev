#!/usr/bin/env python3
"""Collect the unchanged full-support checker on tensor-prepared larger systems."""
from __future__ import annotations
import argparse
import hashlib
import json
import math
import os
from pathlib import Path
import platform
import subprocess
import sys
import time

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT))
from scripts.bench.cpu_lease import cpu_lease
from scripts.bench.sign_det_compare import archive_sources
from scripts.bench.sign_det_sparse import source_hashes
from scripts.bench.sign_det_joint_timing import harness_binding

ARITIES = [5, 6, 7, 8]
PARAMS = [3**s for s in ARITIES]
FUNCTION = "Hex.SignDetBench.MaximalMatrix.runTensorCheck"
CONFIG = {"param_floor": PARAMS[0], "param_ceiling": PARAMS[-1], "outer_trials": 6,
          "param_schedule": {"kind": "custom", "params": PARAMS},
          "target_inner_nanos": 100000000, "max_seconds_per_call": 3600,
          "signal_floor_multiplier": 1, "cache_mode": "warm",
          "verdict_warmup_fraction": 0.2, "slope_tolerance": 0.15,
          "narrow_range_noise_floor": 1.5}


def validate_inputs(path):
    rows = [json.loads(line) for line in Path(path).read_text().splitlines()]
    if [r["queries"] for r in rows] != ARITIES:
        raise ValueError("missing or reordered wide checker inputs")
    for row, s in zip(rows, ARITIES, strict=True):
        r = 3**s
        expected = {"queries": s, "matrixSize": r, "supportSize": r, "countSum": r,
                    "inverseIdentityScalarPairs": r**3, "inverseBits": s+1,
                    "denominatorBits": s+1, "valuesBits": r.bit_length()}
        if any(type(row.get(k)) is not int or row[k] != v for k, v in expected.items()):
            raise ValueError("wrong full-support dimensions or witness sizes")
        if row.get("literalOrders") is not True or row.get("finiteMoments") is not True:
            raise ValueError("missing literal-order or finite-moment guard")
        for k in ("inputHash", "checkResultHash"):
            if type(row.get(k)) is not int or not 0 <= row[k] < 2**64:
                raise ValueError("invalid input or result hash")
    if len({r["checkResultHash"] for r in rows}) != 1:
        raise ValueError("successful checker answers disagree")
    return {r["matrixSize"]: hex(r["checkResultHash"]) for r in rows}


def validate_overlap(path):
    expected = [f"tensor matrix {3**s}: complete witness matches ordinary solve" for s in range(7)]
    if Path(path).read_text().splitlines() != expected:
        raise ValueError("missing or changed tensor/ordinary-solver comparison")


def validate_result(path, expected, revision):
    export = json.loads(Path(path).read_text())
    if export["export_schema_version"] != 1 or len(export["results"]) != 1:
        raise ValueError("wrong wide checker export")
    result = export["results"][0]
    if (result["function"] != FUNCTION or result["kind"] != "parametric" or
            result["hashable"] is not True or result["budget_truncated"] is not False or
            result["complexity_formula"].replace(" ", "") != "r^3" or
            any(type(result["config"][k]) is not type(v) or result["config"][k] != v for k, v in CONFIG.items()) or
            result["env"]["git_commit"] != revision or result["env"]["git_dirty"] is not False):
        raise ValueError("wrong wide checker declaration, configuration or source binding")
    points = result["points"]
    if [(p["trial_index"], p["param"]) for p in points] != [
            (trial, r) for trial in range(6) for r in PARAMS]:
        raise ValueError("incomplete or reordered wide checker observations")
    for point in points:
        duration = point["per_call_nanos"]
        if (point["status"] != "ok" or point["result_hash"] != expected[point["param"]] or
                point["part_of_verdict"] is not True or point["below_signal_floor"] is not False or
                type(duration) not in (int, float) or not math.isfinite(duration) or duration <= 0 or
                type(point["inner_repeats"]) is not int or point["inner_repeats"] <= 0 or
                type(point["trial_index"]) is not int or type(point["param"]) is not int or
                type(point["peak_rss_kb"]) is not int or point["peak_rss_kb"] <= 0 or
                point["alloc_bytes"] is not None):
            raise ValueError("failed or substituted wide checker observation")
    if result["verdict"] not in ("consistent_with_declared_complexity", "inconclusive"):
        raise ValueError("unknown wide checker verdict")
    return {key: result[key] for key in ["verdict", "slope", "complexity_formula", "advisories"]}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    revision = subprocess.check_output(["git", "rev-parse", "HEAD"], cwd=ROOT, text=True).strip()
    if subprocess.check_output(["git", "status", "--porcelain"], cwd=ROOT, text=True):
        raise ValueError("commit sources before collection")
    subprocess.run(["lake", "build", "--no-build", "hexsigndet_bench"], cwd=ROOT, check=True)
    executable = ROOT / ".lake/build/bin/hexsigndet_bench"
    out = args.output.resolve()
    if out.is_relative_to(ROOT):
        raise ValueError("collect outside the worktree")
    out.mkdir(parents=True, exist_ok=False)
    cpu, lease = cpu_lease()
    os.sched_setaffinity(0, {cpu})
    digest = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
    sources = source_hashes()
    for name in ("scripts/bench/sign_det_matrix_wide.py", "scripts/bench/test_sign_det_matrix_wide.py",
                 "scripts/bench/sign_det_compare.py", "scripts/bench/sign_det_joint_timing.py",
                 "reports/sign-det-matrix-wide.md"):
        sources[name] = digest(ROOT / name)
    m = {"kind": "wide-full-support-checker-timing", "revision": revision,
         "source_sha256": sources, "binary_sha256": digest(executable), "harness_binding": harness_binding(ROOT),
         "host": platform.node(), "platform": platform.platform(), "cpu": cpu,
         "affinity": sorted(os.sched_getaffinity(0)), "executable": str(executable),
         "load_before": os.getloadavg(),
         "runs": [], "state": "running"}
    def save():
        temporary = out / "metadata.tmp"
        temporary.write_text(json.dumps(m, indent=2) + "\n")
        os.replace(temporary, out / "metadata.json")
    def run(label, arguments):
        record = {"label": label, "command": [str(executable), *arguments], "state": "running"}
        m["runs"].append(record); save()
        start = time.monotonic()
        with (out / (label + ".stdout")).open("w") as stdout, (out / (label + ".stderr")).open("w") as stderr:
            code = subprocess.run(record["command"], cwd=ROOT, stdout=stdout, stderr=stderr).returncode
        record.update(state="complete", exit_code=code, elapsed_seconds=time.monotonic()-start,
                      load_after=os.getloadavg()); save()
        return code
    try:
        archive_sources(out, m); save()
        if run("overlap", ["inspect-maximal-matrix-tensors"]):
            raise ValueError("tensor/ordinary-solver comparison failed")
        validate_overlap(out / "overlap.stdout")
        if run("inputs", ["inspect-wide-matrix-checks"]):
            raise ValueError("wide checker inspection failed")
        expected = validate_inputs(out / "inputs.stdout")
        if run("timings", ["run", FUNCTION, "--export-file", str(out / "timings.json")]) not in (0, 1):
            raise ValueError("wide checker runner failed; raw output retained")
        summary = validate_result(out / "timings.json", expected, revision)
        (out / "summary.json").write_text(json.dumps(summary, indent=2) + "\n")
        m["source_sha256_after"] = {name: digest(ROOT / name) for name in sources}
        if (m["source_sha256_after"] != sources or digest(executable) != m["binary_sha256"] or harness_binding(ROOT) != m["harness_binding"] or
                subprocess.check_output(["git", "rev-parse", "HEAD"], cwd=ROOT, text=True).strip() != revision or
                subprocess.check_output(["git", "status", "--porcelain"], cwd=ROOT, text=True)):
            raise ValueError("source, binary or harness changed during collection")
        m.update(state="complete", scientific_samples=24)
        code = int(summary["verdict"] == "inconclusive")
        m["collector_exit_code"] = code
        return code
    except BaseException as error:
        m.update(state="failed", error=str(error), exception=type(error).__name__,
                 collector_exit_code=(130 if isinstance(error, KeyboardInterrupt) else 2)); raise
    finally:
        final_error = None
        try:
            m["source_sha256_after"] = {name: digest(ROOT / name) for name in sources}
            m["binary_sha256_after"] = digest(executable)
            m["harness_binding_after"] = harness_binding(ROOT)
            m["revision_after"] = subprocess.check_output(["git", "rev-parse", "HEAD"], cwd=ROOT, text=True).strip()
            m["git_status_after"] = subprocess.check_output(["git", "status", "--porcelain"], cwd=ROOT, text=True)
            m["source_unchanged"] = (m["source_sha256_after"] == sources and
                m["binary_sha256_after"] == m["binary_sha256"] and
                m["harness_binding_after"] == m["harness_binding"] and
                m["revision_after"] == revision and m["git_status_after"] == "")
            if not m["source_unchanged"]:
                final_error = "source, binary or harness changed during collection"
        except BaseException as error:
            final_error = str(error)
        was_complete = m["state"] == "complete"
        if final_error is not None:
            m["final_identity_error"] = final_error
            if was_complete:
                m.update(state="failed", exception="RuntimeError", collector_exit_code=2)
        m["file_sha256"] = {p.name: digest(p) for p in out.iterdir() if p.is_file() and p.name != "metadata.json"}
        m["load_after"] = os.getloadavg(); save(); lease.close()
        if final_error is not None and was_complete:
            raise RuntimeError(final_error)


if __name__ == "__main__":
    try:
        exit_code = main()
    except KeyboardInterrupt:
        exit_code = 130
    except Exception:
        import traceback
        traceback.print_exc()
        exit_code = 2
    raise SystemExit(exit_code)
