#!/usr/bin/env python3
"""Retain a short adjacent AB/BA comparison of nested constants and consumers."""
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

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT))
from scripts.bench.cpu_lease import cpu_lease
from scripts.bench.sign_det_nested_signs import constant

# Declared before collection. No activity-dependent filtering or retries.
TRIALS = 6
TARGET_NANOS = 100_000_000
CASES = [
    ("units", "hexrationalfn_bench", "Hex.RationalFnBench.Nested.runUnits", [2, 6, 10]),
    ("arithmetic", "hexrationalfn_bench", "Hex.RationalFnBench.Nested.runArithmetic", [1, 2, 3]),
    ("sign", "hexsigndet_bench", "Hex.SignDetBench.NestedSigns.runSign", [6, 9, 12]),
]


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def binding(root):
    if subprocess.check_output(["git", "status", "--porcelain"], cwd=root, text=True):
        raise ValueError("commit all source before collection")
    sources = {}
    for name in ("HexRationalFn", "HexPoly", "HexOrderedFn", "bench/HexRationalFn", "bench/HexSignDet"):
        for p in (root / name).rglob("*.lean"):
            sources[str(p.relative_to(root))] = digest(p)
    for name in ("lean-toolchain", "lake-manifest.json", "lakefile.lean"):
        sources[name] = digest(root / name)
    return {
        "revision": subprocess.check_output(["git", "rev-parse", "HEAD"], cwd=root, text=True).strip(),
        "source_sha256": sources,
        "binary_sha256": {exe: digest(root / ".lake/build/bin" / exe) for exe in
                           ("hexrationalfn_bench", "hexsigndet_bench")},
        "harness_revision": subprocess.check_output(
            ["git", "rev-parse", "HEAD"], cwd=root / ".lake/packages/lean-bench", text=True).strip(),
    }


def validate_inventory(rows):
    expected = [("units", d) for d in [2, 6, 10]] + [("arithmetic", d) for d in [1, 2, 3]]
    if [(r["operation"], r["depth"]) for r in rows] != expected:
        raise ValueError("missing or reordered inventories")
    hashes = {}
    for row in rows:
        d = row["depth"]
        if row["operation"] == "units":
            value = {"zero": constant(0, d), "one": constant(1, d)}
        else:
            value = {"num": [constant(1, d-1), constant(1, d-1)],
                     "den": [constant(-1, d-1), constant(1, d-1)]}
        if json.loads(row["input"]) != value or json.loads(row["output"]) != value:
            raise ValueError("canonical output disagrees with independent expected coefficients")
        if type(row["resultHash"]) is not int or not 0 <= row["resultHash"] < 2**64:
            raise ValueError("invalid result hash")
        hashes[(row["operation"], d)] = hex(row["resultHash"])
    return hashes


def validate_samples(rows, hashes, bindings):
    schedule = [(trial, op, depth, arm) for trial in range(TRIALS)
                for op, _, _, depths in CASES for depth in depths
                for arm in (["before", "after"] if trial % 2 == 0 else ["after", "before"])]
    if [(r["trial"], r["operation"], r["depth"], r["arm"]) for r in rows] != schedule:
        raise ValueError("missing, duplicated or reordered samples")
    for row in rows:
        point = row["point"]
        function = next(function for op, _, function, _ in CASES if op == row["operation"])
        if (point["function"] != function or point["param"] != row["depth"] or
                point["cache_mode"] != "warm" or point["status"] != "ok" or
                point["result_hash"] != hashes[(row["operation"], row["depth"])] or
                type(point["inner_repeats"]) is not int or point["inner_repeats"] <= 0 or
                type(point["per_call_nanos"]) not in (int, float) or
                not math.isfinite(point["per_call_nanos"]) or point["per_call_nanos"] <= 0 or
                point["env"]["git_commit"] != bindings[row["arm"]]["revision"] or
                point["env"]["git_dirty"] is not False):
            raise ValueError("failed sample, substituted result or wrong source")
    summary = []
    for op, _, _, depths in CASES:
        for d in depths:
            arms = {arm: [r["point"]["per_call_nanos"] for r in rows
                          if (r["operation"], r["depth"], r["arm"]) == (op, d, arm)]
                    for arm in ("before", "after")}
            ratios = [a/b for a, b in zip(arms["before"], arms["after"])]
            summary.append({"operation": op, "depth": d,
                            "before_median_nanos": statistics.median(arms["before"]),
                            "after_median_nanos": statistics.median(arms["after"]),
                            "paired_speedup_median": statistics.median(ratios),
                            "paired_speedup_range": [min(ratios), max(ratios)]})
    return summary


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--before", type=Path, required=True)
    parser.add_argument("--after", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    roots = {"before": args.before.resolve(), "after": args.after.resolve()}
    bindings = {arm: binding(root) for arm, root in roots.items()}
    if bindings["before"]["harness_revision"] != bindings["after"]["harness_revision"]:
        raise ValueError("harness revisions differ")
    out = args.output.resolve()
    if any(out.is_relative_to(root) for root in roots.values()):
        raise ValueError("collect outside both worktrees")
    out.mkdir(parents=True, exist_ok=False)
    cpu, lease = cpu_lease()
    os.sched_setaffinity(0, {cpu})
    metadata = {"protocol": {"trials": TRIALS, "cases": CASES, "target_nanos": TARGET_NANOS,
                             "arm_order": "AB/BA", "child_timeout_seconds": 30},
                "bindings": bindings, "host": platform.node(), "cpu": cpu,
                "load_before": os.getloadavg(), "runner_sha256": digest(Path(__file__)), "state": "running"}
    save = lambda: (out / "metadata.json").write_text(json.dumps(metadata, indent=2) + "\n")
    save()
    try:
        expected = None
        for arm, root in roots.items():
            result = subprocess.run([str(root / ".lake/build/bin/hexrationalfn_bench"), "inspect-nested"],
                                    cwd=root, capture_output=True, text=True, check=True)
            (out / f"{arm}-inputs.jsonl").write_text(result.stdout)
            values = validate_inventory([json.loads(line) for line in result.stdout.splitlines()])
            if expected is not None and expected != values:
                raise ValueError("before/after outputs differ")
            expected = values
        for d in [6, 9, 12]:
            expected[("sign", d)] = "0x2"  # Hashable Int maps positive one to two.
        rows = []
        with (out / "samples.jsonl").open("w") as stream:
            for trial in range(TRIALS):
                for op, exe, function, depths in CASES:
                    for d in depths:
                        for arm in (["before", "after"] if trial % 2 == 0 else ["after", "before"]):
                            root = roots[arm]
                            result = subprocess.run([
                                str(root / ".lake/build/bin" / exe), "_child", "--bench", function,
                                "--param", str(d), "--target-nanos", str(TARGET_NANOS)],
                                cwd=root, capture_output=True, text=True, timeout=30)
                            label = f"{trial}-{op}-{d}-{arm}"
                            (out / f"{label}.stdout").write_text(result.stdout)
                            (out / f"{label}.stderr").write_text(result.stderr)
                            if result.returncode:
                                raise ValueError(f"child failed: {label}")
                            point = json.loads(result.stdout)
                            row = {"trial": trial, "operation": op, "depth": d, "arm": arm,
                                   "point": point, "load_after": os.getloadavg()}
                            rows.append(row)
                            stream.write(json.dumps(row) + "\n"); stream.flush()
        summary = validate_samples(rows, expected, bindings)
        (out / "summary.json").write_text(json.dumps(summary, indent=2) + "\n")
        if ({arm: binding(root) for arm, root in roots.items()} != bindings or
                digest(Path(__file__)) != metadata["runner_sha256"]):
            raise ValueError("sources or binaries changed during collection")
        metadata.update(state="complete", observations=len(rows))
    except BaseException as error:
        metadata.update(state="failed", error=str(error)); raise
    finally:
        metadata["load_after"] = os.getloadavg()
        metadata["file_sha256"] = {p.name: digest(p) for p in out.iterdir()
                                   if p.is_file() and p.name != "metadata.json"}
        save(); lease.close()


if __name__ == "__main__":
    main()
