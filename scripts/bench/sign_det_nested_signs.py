#!/usr/bin/env python3
"""Collect nested coefficient-sign costs without changing field arithmetic."""
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

DEPTHS = [2, 4, 6, 8, 10, 12]
FUNCTION = "Hex.SignDetBench.NestedSigns.runSign"
CONFIG = {"param_floor": 2, "param_ceiling": 12, "outer_trials": 6,
          "param_schedule": {"kind": "custom", "params": DEPTHS},
          "target_inner_nanos": 100000000, "max_seconds_per_call": 30,
          "signal_floor_multiplier": 1, "cache_mode": "warm",
          "verdict_warmup_fraction": 0.2, "slope_tolerance": 0.15,
          "narrow_range_noise_floor": 1.5}


def constant(value, depth):
    if depth == 0:
        return [value, 1]
    return {"num": [] if value == 0 else [constant(value, depth-1)],
            "den": [constant(1, depth-1)]}


def validate_inputs(path):
    rows = [json.loads(line) for line in Path(path).read_text().splitlines()]
    if [row["depth"] for row in rows] != DEPTHS:
        raise ValueError("missing or reordered nested coefficient inputs")
    for row in rows:
        depth = row["depth"]
        expected = {"num": [constant(0, depth-1), constant(1, depth-1)],
                    "den": [constant(1, depth-1)]}
        if (type(depth) is not int or
                json.dumps(json.loads(row["coefficient"]), sort_keys=True) != json.dumps(expected, sort_keys=True) or
                row["encodedBytes"] != len(row["coefficient"].encode()) or
                type(row["predictedBaseSigns"]) is not int or row["predictedBaseSigns"] != 2**depth or
                type(row["encodedBytes"]) is not int or type(row["resultHash"]) is not int or
                not 0 <= row["resultHash"] < 2**64):
            raise ValueError("nested coefficient differs from the literal positive infinitesimal")
    if len({r["resultHash"] for r in rows}) != 1:
        raise ValueError("positive infinitesimal answers disagree")
    return {row["depth"]: hex(row["resultHash"]) for row in rows}


def validate_result(path, expected, revision):
    export = json.loads(Path(path).read_text())
    if export["export_schema_version"] != 1 or len(export["results"]) != 1:
        raise ValueError("wrong nested-sign export")
    result = export["results"][0]
    if (result["function"] != FUNCTION or result["kind"] != "parametric" or
            result["hashable"] is not True or result["budget_truncated"] is not False or
            result["complexity_formula"].replace(" ", "") != "numeralCostd" or
            any(result["config"][k] != v for k, v in CONFIG.items()) or
            result["env"]["git_commit"] != revision or result["env"]["git_dirty"] is not False):
        raise ValueError("wrong nested-sign registration or source binding")
    points = result["points"]
    if [(p["trial_index"], p["param"]) for p in points] != [
            (trial, depth) for trial in range(6) for depth in DEPTHS]:
        raise ValueError("incomplete or reordered nested-sign observations")
    for point in points:
        duration = point["per_call_nanos"]
        if (point["status"] != "ok" or point["result_hash"] != expected[point["param"]] or
                point["part_of_verdict"] is not True or point["below_signal_floor"] is not False or
                type(duration) not in (int, float) or not math.isfinite(duration) or duration <= 0 or
                type(point["inner_repeats"]) is not int or point["inner_repeats"] <= 0 or
                type(point["trial_index"]) is not int or type(point["param"]) is not int or
                type(point["peak_rss_kb"]) is not int or point["peak_rss_kb"] <= 0 or
                point["alloc_bytes"] is not None):
            raise ValueError("failed or substituted nested-sign observation")
    if result["verdict"] not in ("consistent_with_declared_complexity", "inconclusive"):
        raise ValueError("unknown nested-sign verdict")
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
    for name in ("HexRationalFn", "HexOrderedFn"):
        for path in [ROOT / (name + ".lean"), *(ROOT / name).rglob("*.lean")]:
            sources[str(path.relative_to(ROOT))] = digest(path)
    for name in ("scripts/bench/sign_det_nested_signs.py", "scripts/bench/test_sign_det_nested_signs.py",
                 "scripts/bench/sign_det_compare.py", "scripts/bench/sign_det_joint_timing.py",
                 "reports/sign-det-nested-signs.md"):
        sources[name] = digest(ROOT / name)
    m = {"kind": "nested-coefficient-sign-timing", "revision": revision,
         "source_sha256": sources, "binary_sha256": digest(executable), "harness_binding": harness_binding(ROOT),
         "host": platform.node(), "cpu": cpu, "load_before": os.getloadavg(),
         "runs": [], "state": "running"}
    def save(): (out / "metadata.json").write_text(json.dumps(m, indent=2) + "\n")
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
        if run("inputs", ["inspect-nested-signs"]):
            raise ValueError("nested coefficient inspection failed")
        expected = validate_inputs(out / "inputs.stdout")
        if run("timings", ["run", FUNCTION, "--export-file", str(out / "timings.json")]) not in (0, 1):
            raise ValueError("nested-sign runner failed; raw output retained")
        summary = validate_result(out / "timings.json", expected, revision)
        (out / "summary.json").write_text(json.dumps(summary, indent=2) + "\n")
        m["source_sha256_after"] = {name: digest(ROOT / name) for name in sources}
        if (m["source_sha256_after"] != sources or digest(executable) != m["binary_sha256"] or harness_binding(ROOT) != m["harness_binding"] or
                subprocess.check_output(["git", "rev-parse", "HEAD"], cwd=ROOT, text=True).strip() != revision or
                subprocess.check_output(["git", "status", "--porcelain"], cwd=ROOT, text=True)):
            raise ValueError("source, binary or harness changed during collection")
        m.update(state="complete", scientific_samples=36)
        return int(summary["verdict"] == "inconclusive")
    except BaseException as error:
        m.update(state="failed", error=str(error)); raise
    finally:
        m["file_sha256"] = {p.name: digest(p) for p in out.iterdir() if p.is_file() and p.name != "metadata.json"}
        m["load_after"] = os.getloadavg(); save(); lease.close()


if __name__ == "__main__":
    raise SystemExit(main())
