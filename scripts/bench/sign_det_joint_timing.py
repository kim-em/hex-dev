#!/usr/bin/env python3
"""Collect source-bound joint Thom-query timings with the shared fixed schedules."""
from __future__ import annotations

import argparse
import hashlib
import json
import math
import os
from pathlib import Path
import platform
import statistics
import subprocess
import sys
import time

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT))
from scripts.bench.sign_det_compare import archive_sources
from scripts.bench.sign_det_joint import COST_FIELDS, DEGREES, validate as validate_inputs
from scripts.bench.sign_det_sparse import source_hashes
from scripts.bench.cpu_lease import cpu_lease as acquire_cpu

TRIALS = 6
PREFIX = "Hex.SignDetBench.Joint."
RESULT_KEYS = {
    "runCompletion": "completionResultHash", "runComparison": "comparisonResultHash",
    "runReduced": "tableResultHash", "runDirect": "tableResultHash",
    "runCheckReduced": "replayResultHash", "runCheckDirect": "replayResultHash",
}
CONFIG = {"param_floor": 3, "param_ceiling": 63, "outer_trials": TRIALS,
          "param_schedule": {"kind": "custom", "params": DEGREES},
          "target_inner_nanos": 100000000, "max_seconds_per_call": 180,
          "signal_floor_multiplier": 1, "cache_mode": "warm",
          "verdict_warmup_fraction": 0.2, "slope_tolerance": 0.15,
          "narrow_range_noise_floor": 1.5}


def validate_hashes(path):
    rows = [json.loads(line) for line in path.read_text().splitlines()]
    if [r.get("degree") for r in rows] != DEGREES:
        raise ValueError("missing, extra or reordered callback inputs")
    for row, n in zip(rows, DEGREES, strict=True):
        if type(row["degree"]) is not int or row.get("queries") != 3*n+1:
            raise ValueError("wrong callback query count")
        if set(row) != {"degree", "queries", *RESULT_KEYS.values()}:
            raise ValueError("changed callback result fields")
        for key in set(RESULT_KEYS.values()):
            if type(row[key]) is not int or not 0 <= row[key] < 2**64:
                raise ValueError("invalid callback result hash")
    return {row["degree"]: row for row in rows}


def validate_points(points, name, expected, schedule):
    if [(p["trial_index"], p["param"]) for p in points] != schedule:
        raise ValueError("missing, duplicated or reordered scientific observations")
    for point in points:
        if type(point["trial_index"]) is not int or type(point["param"]) is not int:
            raise ValueError("non-integer scientific schedule index")
        n = point["param"]
        if (point["status"] != "ok" or point["result_hash"] != hex(expected[n][RESULT_KEYS[name]]) or
                point["part_of_verdict"] is not True or point["below_signal_floor"] is not False):
            raise ValueError("failed, incorrect or substituted scientific observation")
        value = point["per_call_nanos"]
        if (type(value) not in (int, float) or not math.isfinite(value) or value <= 0 or
                type(point["inner_repeats"]) is not int or point["inner_repeats"] <= 0):
            raise ValueError("invalid scientific timing or repeat count")
        rss = point.get("peak_rss_kb")
        if type(rss) is not int or rss <= 0:
            raise ValueError("missing child peak resident-set observation")
        if point.get("alloc_bytes") is not None:
            raise ValueError("unexpected allocated-byte counter; check its interpretation")


def validate_result(result, name, expected, revision, points=None):
    if (result["function"] != PREFIX+name or result["kind"] != "parametric" or
            result["hashable"] is not True or result["budget_truncated"] is not False):
        raise ValueError("wrong benchmark result or truncated measurement")
    if result["env"]["git_commit"] != revision or result["env"]["git_dirty"] is not False:
        raise ValueError("measurement is not bound to the clean source revision")
    if any(result["config"][k] != v for k, v in CONFIG.items()):
        raise ValueError("measurement changed the registered schedule")
    if result["complexity_formula"].replace(" ", "") != "n^3":
        raise ValueError("measurement changed the declared cost model")
    if points is not None and result["points"] != points:
        raise ValueError("summary differs from the retained sample stream")
    validate_points(result["points"], name, expected,
                    [(trial, n) for trial in range(TRIALS) for n in DEGREES])
    if result["verdict"] not in ("consistent_with_declared_complexity", "inconclusive"):
        raise ValueError("unknown harness verdict")
    return {k: result[k] for k in ("verdict", "complexity_formula", "slope", "c_min", "c_max", "advisories")}


def validate_single(path, name, expected, revision):
    export = json.loads(path.read_text())
    if export["export_schema_version"] != 1 or len(export["results"]) != 1:
        raise ValueError("wrong export schema or result count")
    return validate_result(export["results"][0], name, expected, revision)


def validate_pair(path, names, expected, revision):
    rows = [json.loads(line) for line in path.read_text().splitlines()]
    header = rows[0]
    arms = [PREFIX+name for name in names]
    if any(header.get(k) != v for k, v in {
            "kind": "header", "schema": "hex-sign-det-paired-v1", "params": DEGREES,
            "trials": TRIALS, "left": arms[0], "right": arms[1]}.items()):
        raise ValueError("wrong paired header")
    if header["env"]["git_commit"] != revision or header["env"]["git_dirty"] is not False:
        raise ValueError("paired child source differs")
    schedule = [(arm, trial, n) for trial in range(TRIALS) for n in DEGREES
                for arm in (arms if trial % 2 == 0 else arms[::-1])]
    if len(rows) != len(schedule)+3:
        raise ValueError("missing or extra paired records")
    points = {arm: [] for arm in arms}
    for row, (arm, trial, n) in zip(rows[1:-2], schedule, strict=True):
        p = row["point"]
        if (row["kind"], row["arm"], p["trial_index"], p["param"]) != ("sample", arm, trial, n):
            raise ValueError("paired arms are missing, duplicated or reordered")
        points[arm].append(p)
    observations = {}
    for row, name, arm in zip(rows[-2:], names, arms, strict=True):
        if row["kind"] != "summary" or row["result"]["env"] != header["env"]:
            raise ValueError("paired summary environment differs")
        observations[name] = validate_result(row["result"], name, expected, revision, points[arm])
    paired = []
    for n in DEGREES:
        a, b = ([p["per_call_nanos"] for p in points[arm] if p["param"] == n] for arm in arms)
        ratios = [y/x for x, y in zip(a, b, strict=True)]
        deltas = [y-x for x, y in zip(a, b, strict=True)]
        paired.append({"degree": n, "left_nanos": a, "right_nanos": b,
                       "ratios": ratios, "deltas_nanos": deltas,
                       "median_ratio": statistics.median(ratios),
                       "median_delta_nanos": statistics.median(deltas)})
    return {"observations": observations, "paired": paired}


def collect_results(run, out, expected, revision):
    """Retain all scheduled arms before judging any scientific observation."""
    records = []
    for name in ("runCompletion", "runComparison"):
        target = out/(name+".json")
        code = run(name, ["run", PREFIX+name, "--export-file", str(target)])
        records.append((name, target, code, None))
    for label, names, command in (
            ("production", ("runReduced", "runDirect"), "paired-joint-production"),
            ("replay", ("runCheckReduced", "runCheckDirect"), "paired-joint-replay")):
        target = out/(label+".jsonl")
        records.append((label, target, run(label, [command, str(target)]), names))
    summary = {"observations": {}, "pairs": {}, "validation_errors": []}
    for label, target, code, names in records:
        if code not in (0, 1):
            summary["validation_errors"].append({"label": label, "exit_code": code})
        try:
            if names is None:
                summary["observations"][label] = validate_single(target, label, expected, revision)
            else:
                pair = validate_pair(target, names, expected, revision)
                summary["observations"].update(pair["observations"])
                summary["pairs"][label] = pair["paired"]
        except (ValueError, KeyError, TypeError, IndexError, OSError) as exc:
            summary["validation_errors"].append({"label": label, "error": str(exc),
                                                   "exception": type(exc).__name__})
    (out/"summary.json").write_text(json.dumps(summary, indent=2)+"\n")
    return summary


def harness_binding(root):
    package = root/".lake/packages/lean-bench"
    revision = subprocess.check_output(["git", "rev-parse", "HEAD"], cwd=package, text=True).strip()
    status = subprocess.check_output(["git", "status", "--porcelain"], cwd=package, text=True)
    pins = [p["rev"] for p in json.loads((root/"lake-manifest.json").read_text())["packages"]
            if p["name"] in ("lean-bench", "«lean-bench»")]
    if len(pins) != 1:
        raise ValueError("manifest must contain one benchmark harness pin")
    pin = pins[0]
    if status or revision != pin:
        raise ValueError("benchmark harness must be clean and match the manifest pin")
    return {"revision": revision, "manifest_revision": pin, "status": status}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    revision = subprocess.check_output(["git", "rev-parse", "HEAD"], cwd=ROOT, text=True).strip()
    if subprocess.check_output(["git", "status", "--porcelain"], cwd=ROOT, text=True):
        raise ValueError("commit the measurement sources first")
    exe = ROOT / ".lake/build/bin/hexsigndet_bench"
    subprocess.run(["lake", "build", "--no-build", "hexsigndet_bench"], cwd=ROOT, check=True)
    harness = harness_binding(ROOT)
    out = args.output.resolve()
    if out.is_relative_to(ROOT.resolve()):
        raise ValueError("write measurement output outside the source checkout")
    out.mkdir(parents=True, exist_ok=False)
    cpu, lease = acquire_cpu()
    os.sched_setaffinity(0, {cpu})
    sources = source_hashes()
    for name in ("scripts/bench/sign_det_joint.py", "scripts/bench/test_sign_det_joint.py",
                 "scripts/bench/sign_det_joint_timing.py", "scripts/bench/test_sign_det_joint_timing.py",
                 "scripts/bench/sign_det_compare.py", "reports/sign-det-joint-performance.md"):
        sources[name] = hashlib.sha256((ROOT/name).read_bytes()).hexdigest()
    metadata = {"schema": "hex-sign-det-joint-timing-v1", "revision": revision,
                "source_sha256": sources, "binary_sha256": hashlib.sha256(exe.read_bytes()).hexdigest(),
                "host": platform.node(), "platform": platform.platform(), "cpu": cpu,
                "affinity": sorted(os.sched_getaffinity(0)), "load_before": os.getloadavg(),
                "harness_revision": harness["revision"], "harness_binding": harness,
                "runs": [], "state": "running"}

    def save():
        (out/"metadata.json").write_text(json.dumps(metadata, indent=2)+"\n")

    def run(label, arguments):
        record = {"label": label, "command": [str(exe), *arguments], "state": "running"}
        metadata["runs"].append(record)
        save()
        start = time.monotonic()
        with (out/(label+".log")).open("w") as stdout, (out/(label+".stderr.log")).open("w") as stderr:
            result = subprocess.run(record["command"], cwd=ROOT, stdout=stdout, stderr=stderr)
        record.update(state="complete", exit_code=result.returncode,
                      wall_seconds=time.monotonic()-start, load_after=os.getloadavg())
        save()
        return result.returncode

    try:
        archive_sources(out, metadata)
        save()
        if run("inputs", ["inspect-joint"]) or run("callbacks", ["inspect-joint-timings"]):
            raise ValueError("untimed joint input or callback verification failed")
        validate_inputs(out/"inputs.log")
        if any(not COST_FIELDS <= set(json.loads(line)) for line in (out/"inputs.log").read_text().splitlines()):
            raise ValueError("joint cost-model inventory is missing")
        expected = validate_hashes(out/"callbacks.log")
        summary = collect_results(run, out, expected, revision)
        metadata["source_sha256_after"] = {
            p: hashlib.sha256((ROOT/p).read_bytes()).hexdigest() for p in sources}
        metadata["binary_sha256_after"] = hashlib.sha256(exe.read_bytes()).hexdigest()
        metadata["revision_after"] = subprocess.check_output(
            ["git", "rev-parse", "HEAD"], cwd=ROOT, text=True).strip()
        metadata["status_after"] = subprocess.check_output(
            ["git", "status", "--porcelain"], cwd=ROOT, text=True)
        metadata["harness_binding_after"] = harness_binding(ROOT)
        if (metadata["source_sha256_after"] != sources or
                metadata["binary_sha256_after"] != metadata["binary_sha256"] or
                metadata["revision_after"] != revision or metadata["status_after"] or
                metadata["harness_binding_after"] != harness):
            raise ValueError("measurement source or executable changed during collection")
        if summary["validation_errors"]:
            raise ValueError("scientific validation failed; all scheduled arm records are retained")
        metadata["state"] = "complete"
        metadata["scientific_samples"] = 180
        return int(any(v["verdict"] == "inconclusive" for v in summary["observations"].values()))
    except BaseException as exc:
        metadata.update(state="failed", error=str(exc), exception=type(exc).__name__)
        raise
    finally:
        metadata["load_after"] = os.getloadavg()
        save()
        lease.close()


if __name__ == "__main__":
    raise SystemExit(main())
