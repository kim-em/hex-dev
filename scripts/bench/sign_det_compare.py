#!/usr/bin/env python3
"""Retain adjacent AB/BA sign-table comparisons and the shared harness verdicts."""
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
import tempfile
import time

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT))
from scripts.bench.sign_det_sparse import source_hashes
from scripts.bench.structural_tactic_sweep import acquire_cpu

PARAMS = [1, 2, 3, 4, 5]
TRIALS = 6
ARMS = ["Hex.SignDetBench.runSmallReduced", "Hex.SignDetBench.runSmallFull"]


def archive_sources(out, metadata):
    """Retain and verify a patch reconstructing every recorded source file."""
    revision = metadata["revision"]
    paths = sorted(metadata["source_sha256"])
    base = subprocess.check_output(["git", "merge-base", revision, "origin/main"],
                                   cwd=ROOT, text=True).strip()
    patch = subprocess.check_output(
        ["git", "diff", "--binary", "--unified=0", base, revision, "--", *paths], cwd=ROOT)
    with tempfile.TemporaryDirectory(prefix="hex-sign-det-source-") as temporary:
        env = dict(os.environ, GIT_INDEX_FILE=str(Path(temporary) / "index"))
        subprocess.run(["git", "read-tree", base], cwd=ROOT, env=env, check=True)
        if patch:
            subprocess.run(["git", "apply", "--cached", "--unidiff-zero"],
                           input=patch, cwd=ROOT, env=env, check=True)
        for path, expected in metadata["source_sha256"].items():
            contents = subprocess.check_output(["git", "show", ":" + path], cwd=ROOT, env=env)
            if hashlib.sha256(contents).hexdigest() != expected:
                raise ValueError("archived source does not match measurement: " + path)
    (out / "committed-source.patch").write_bytes(patch)
    metadata["source_archive"] = {
        "base_revision": base, "file": "committed-source.patch",
        "sha256": hashlib.sha256(patch).hexdigest(), "apply_option": "--unidiff-zero",
        "scope": "all paths in source_sha256", "reconstruction_check": "passed"}


def validate(path, inventory, revision):
    """Require every scheduled arm, true result, and the unmodified summaries."""
    expected = [json.loads(line) for line in inventory.read_text().splitlines()]
    if [r["queries"] for r in expected] != PARAMS:
        raise ValueError("incomplete comparison inventory")
    hashes = {r["queries"]: hex(r["resultHash"]) for r in expected}
    rows = [json.loads(line) for line in path.read_text().splitlines()]
    header = rows[0]
    if any(header.get(k) != v for k, v in {
            "kind": "header", "schema": "hex-sign-det-paired-v1", "params": PARAMS,
            "trials": TRIALS, "left": ARMS[0], "right": ARMS[1]}.items()):
        raise ValueError("wrong comparison header")
    if (header["env"]["git_commit"] != revision or
            header["env"]["git_dirty"] is not False):
        raise ValueError("comparison child did not run from the clean measured revision")
    schedule = [(arm, trial, param) for trial in range(TRIALS) for param in PARAMS
                for arm in (ARMS if trial % 2 == 0 else ARMS[::-1])]
    if len(rows) != 1 + len(schedule) + 2:
        raise ValueError("missing or extra comparison records")
    points = {arm: [] for arm in ARMS}
    for row, (arm, trial, param) in zip(rows[1:-2], schedule, strict=True):
        point = row["point"]
        if (row["kind"], row["arm"], point["trial_index"], point["param"]) != (
                "sample", arm, trial, param):
            raise ValueError("comparison arms are missing, duplicated or reordered")
        if (point["status"] != "ok" or point["result_hash"] != hashes[param] or
                point["part_of_verdict"] is not True or point["below_signal_floor"] is not False):
            raise ValueError("failed or incorrect comparison sample")
        nanos = point["per_call_nanos"]
        if (type(nanos) not in (int, float) or not math.isfinite(nanos) or nanos <= 0 or
                type(point["inner_repeats"]) is not int or point["inner_repeats"] <= 0):
            raise ValueError("invalid timing or repeat count")
        points[arm].append(point)
    summaries = {}
    for row, arm in zip(rows[-2:], ARMS, strict=True):
        result = row["result"]
        if (row["kind"] != "summary" or result["function"] != arm or
                result["kind"] != "parametric" or result["hashable"] is not True or
                result["budget_truncated"] is not False or result["points"] != points[arm] or
                result["env"] != header["env"]):
            raise ValueError("summary differs from the retained sample stream")
        required = {"param_floor": 1, "param_ceiling": 5, "outer_trials": TRIALS,
                    "param_schedule": {"kind": "custom", "params": PARAMS},
                    "target_inner_nanos": 100000000, "max_seconds_per_call": 60,
                    "signal_floor_multiplier": 1, "cache_mode": "warm"}
        if any(result["config"][k] != v for k, v in required.items()):
            raise ValueError("comparison changed the registered configuration")
        if result["verdict"] not in ("consistent_with_declared_complexity", "inconclusive"):
            raise ValueError("unknown harness verdict")
        summaries[arm] = {k: result[k] for k in (
            "verdict", "complexity_formula", "slope", "c_min", "c_max", "advisories")}
    paired = []
    for param in PARAMS:
        left = [p["per_call_nanos"] for p in points[ARMS[0]] if p["param"] == param]
        right = [p["per_call_nanos"] for p in points[ARMS[1]] if p["param"] == param]
        ratios = [b/a for a, b in zip(left, right, strict=True)]
        deltas = [b-a for a, b in zip(left, right, strict=True)]
        paired.append({"param": param, "left_nanos": left, "right_nanos": right,
                       "ratios": ratios, "deltas_nanos": deltas,
                       "median_ratio": statistics.median(ratios),
                       "median_delta_nanos": statistics.median(deltas)})
    return {"observations": summaries, "paired": paired}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    status = subprocess.check_output(["git", "status", "--short"], cwd=ROOT, text=True)
    if status:
        raise RuntimeError("commit the measured sources before running the comparison")
    out = args.output.resolve()
    if out.is_relative_to(ROOT):
        raise ValueError("write measurement output outside the source worktree")
    out.mkdir(parents=True, exist_ok=False)
    exe = ROOT / ".lake/build/bin/hexsigndet_bench"
    cpu, lease = acquire_cpu()
    os.sched_setaffinity(0, {cpu})
    sources = source_hashes()
    # The report is the measurement result; the profile runner is source.
    for name in ("scripts/bench/sign_det_compare.py", "scripts/bench/test_sign_det_compare.py",
                 "scripts/profile/sign_det.py"):
        sources[name] = hashlib.sha256((ROOT / name).read_bytes()).hexdigest()
    metadata = {"revision": subprocess.check_output(["git", "rev-parse", "HEAD"],
                    cwd=ROOT, text=True).strip(), "status": status, "source_sha256": sources,
                "binary_sha256": hashlib.sha256(exe.read_bytes()).hexdigest(),
                "host": platform.node(), "platform": platform.platform(), "cpu": cpu,
                "affinity": sorted(os.sched_getaffinity(0)), "load_before": os.getloadavg(),
                "harness_revision": subprocess.check_output(["git", "rev-parse", "HEAD"],
                    cwd=ROOT / ".lake/packages/lean-bench", text=True).strip(),
                "runs": [], "state": "running"}
    def save():
        (out / "metadata.json").write_text(json.dumps(metadata, indent=2) + "\n")

    save()
    try:
        archive_sources(out, metadata)
        save()
        for label, command in (
                ("inventory", [str(exe), "inspect-small"]),
                ("paired", [str(exe), "paired-small", str(out / "samples.jsonl")])):
            start = time.monotonic()
            with (out / (label + ".log")).open("w") as log:
                result = subprocess.run(command, cwd=ROOT, stdout=log, stderr=subprocess.STDOUT)
            metadata["runs"].append({"label": label, "command": command,
                "exit_code": result.returncode, "wall_seconds": time.monotonic()-start,
                "load_after": os.getloadavg()})
            save()
            if label == "inventory" and result.returncode:
                raise ValueError("comparison inventory failed")
        summary = validate(out / "samples.jsonl", out / "inventory.log", metadata["revision"])
        (out / "summary.json").write_text(json.dumps(summary, indent=2) + "\n")
        metadata["source_sha256_after"] = {
            name: hashlib.sha256((ROOT / name).read_bytes()).hexdigest() for name in sources}
        metadata["binary_sha256_after"] = hashlib.sha256(exe.read_bytes()).hexdigest()
        metadata["revision_after"] = subprocess.check_output(
            ["git", "rev-parse", "HEAD"], cwd=ROOT, text=True).strip()
        if (metadata["source_sha256_after"] != sources or
                metadata["binary_sha256_after"] != metadata["binary_sha256"] or
                metadata["revision_after"] != metadata["revision"]):
            raise ValueError("measured source or executable changed during the comparison")
        metadata["state"] = "complete"
        return int(any(r["exit_code"] for r in metadata["runs"]) or any(
            r["verdict"] == "inconclusive" for r in summary["observations"].values()))
    except (OSError, ValueError, KeyError, TypeError, IndexError,
            subprocess.CalledProcessError) as error:
        metadata.update(state="failed", error=str(error))
        return 1
    finally:
        metadata["load_after"] = os.getloadavg()
        save()
        lease.close()


if __name__ == "__main__":
    raise SystemExit(main())
