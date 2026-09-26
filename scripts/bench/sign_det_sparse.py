#!/usr/bin/env python3
"""Run the declared sparse-support SignDet schedules without changing their models.

Retain every completed sample and command, with an automatic CPU lease and
recorded host activity. No quiet-core preflight, filtering or automatic rerun.
"""
from __future__ import annotations

import argparse
import datetime
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
from scripts.bench.structural_tactic_sweep import acquire_cpu
from scripts.libgraph import load_libraries, reachable_dependencies

PARAMS = [64, 128, 256, 512, 1024, 2048]
TRIALS = 6
FUNCTIONS = ("runProduce", "runDirect", "runTree", "runGraph")
COMPONENTS = ("runQueries", "runProducts", "runMatrices", "runSolvers", "runSigns")


def inventory_hashes(path, components=False):
    """Require the complete independently checked inventory before timing."""
    rows = [json.loads(line) for line in path.read_text().splitlines()]
    if [row["queries"] for row in rows] != PARAMS:
        raise ValueError("inventory does not match the declared parameter schedule")
    expected = {}
    for row in rows:
        keys = COMPONENTS if components else ("productionResultHash", "replayResultHash")
        for key in (*keys, "inputHash"):
            if type(row[key]) is not int or not 0 <= row[key] < 2**64:
                raise ValueError("invalid inventory hash: " + key)
        expected[row["queries"]] = row
    return expected


def validate_export(path, name, expected):
    """Validate outputs and scheduling, while retaining the harness verdict.

    An inconclusive model is a valid observation needing investigation, not
    an output error and never a reason to discard or silently repeat a run.
    """
    data = json.loads(path.read_text())
    if data["export_schema_version"] != 1 or len(data["results"]) != 1:
        raise ValueError("unexpected export schema or result count")
    result = data["results"][0]
    if (result["function"] != "Hex.SignDetBench." + name or
            result["kind"] != "parametric" or result["hashable"] is not True or
            result["budget_truncated"] is not False):
        raise ValueError("wrong benchmark or truncated measurement")
    config = result["config"]
    required = {"param_floor": PARAMS[0], "param_ceiling": PARAMS[-1],
                "outer_trials": TRIALS, "target_inner_nanos": 100000000,
                "max_seconds_per_call": 10, "signal_floor_multiplier": 1,
                "cache_mode": "warm",
                "param_schedule": {"kind": "custom", "params": PARAMS}}
    if any(config[key] != value for key, value in required.items()):
        raise ValueError("measurement configuration differs from the declared schedule")
    points = result["points"]
    if [(p["trial_index"], p["param"]) for p in points] != [
            (trial, param) for trial in range(TRIALS) for param in PARAMS]:
        raise ValueError("missing, duplicate, reordered or out-of-schedule samples")
    key = name if name in COMPONENTS else (
        "productionResultHash" if name in FUNCTIONS[:2] else "replayResultHash")
    for point in points:
        if point["status"] != "ok" or point["part_of_verdict"] is not True:
            raise ValueError("non-ok sample or probe substituted for scientific sample")
        actual = point["result_hash"]
        if not isinstance(actual, str) or actual != hex(expected[point["param"]][key]):
            raise ValueError("result differs from the known complete table or true replay")
        nanos = point["per_call_nanos"]
        if (type(nanos) not in (int, float) or not math.isfinite(nanos) or nanos <= 0 or
                type(point["inner_repeats"]) is not int or point["inner_repeats"] <= 0):
            raise ValueError("invalid timing or repeat count")
    if result["verdict"] not in ("consistent_with_declared_complexity", "inconclusive"):
        raise ValueError("unrecognized harness verdict")
    return {key: result[key] for key in (
        "verdict", "complexity_formula", "slope", "c_min", "c_max", "advisories")}


def source_hashes():
    libraries = load_libraries()
    names = {"HexSignDet"} | reachable_dependencies(libraries)["HexSignDet"]
    files = {ROOT / path for path in (
        "bench/HexSignDet/Bench.lean", "reports/sign-det-sparse-model.md",
        "reports/sign-det-phase-model.md",
        "scripts/bench/sign_det_sparse.py", "scripts/bench/structural_tactic_sweep.py",
        "scripts/bench/test_sign_det_sparse.py",
        "scripts/libgraph.py",
        "lakefile.lean", "lake-manifest.json", "lean-toolchain", "libraries.yml")}
    for name in names:
        root = ROOT / (name + ".lean")
        if root.exists():
            files.add(root)
        files.update((ROOT / name).rglob("*.lean"))
    files.update((ROOT / "bench/HexSignDet").rglob("*.lean"))
    return {str(path.relative_to(ROOT)): hashlib.sha256(path.read_bytes()).hexdigest()
            for path in sorted(files)}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--components", action="store_true",
                        help="Run the separately declared internal-phase schedules.")
    args = parser.parse_args()
    out = args.output.resolve()
    out.mkdir(parents=True, exist_ok=False)
    executable = ROOT / ".lake/build/bin/hexsigndet_bench"
    cpu, lease = acquire_cpu()
    os.sched_setaffinity(0, {cpu})
    inventory = "inspect-phases" if args.components else "inspect"
    schedule = [("inventory", [str(executable), inventory])] + [
        (name, [str(executable), "run", "Hex.SignDetBench." + name,
                "--export-file", str(out / (name + ".json"))])
        for name in (COMPONENTS if args.components else FUNCTIONS)]
    metadata = {
        "started": datetime.datetime.now(datetime.timezone.utc).isoformat(),
        "revision": subprocess.check_output(["git", "rev-parse", "HEAD"], cwd=ROOT, text=True).strip(),
        "status": subprocess.check_output(["git", "status", "--short"], cwd=ROOT, text=True),
        "source_sha256": source_hashes(),
        "binary_sha256": hashlib.sha256(executable.read_bytes()).hexdigest(),
        "host": platform.node(), "platform": platform.platform(),
        "cpu_description": subprocess.check_output(["lscpu"], text=True),
        "cpu": cpu, "affinity": sorted(os.sched_getaffinity(0)),
        "load_start": os.getloadavg(), "command": sys.argv, "schedule": schedule,
        "harness_revision": subprocess.check_output(["git", "rev-parse", "HEAD"],
            cwd=ROOT / ".lake/packages/lean-bench", text=True).strip(),
    }
    (out / "metadata.json").write_text(json.dumps(metadata, indent=2) + "\n")
    (out / "source.patch").write_bytes(subprocess.check_output(["git", "diff", "HEAD"], cwd=ROOT))
    failed = []
    observations = {}
    expected = {}
    try:
        with (out / "commands.jsonl").open("w") as journal:
            for name, command in schedule:
                print(name, flush=True)
                started = time.monotonic()
                with (out / (name + ".log")).open("w") as log:
                    result = subprocess.run(command, cwd=ROOT, stdout=log, stderr=subprocess.STDOUT)
                record = {"label": name, "command": command, "exit_code": result.returncode,
                          "wall_seconds": time.monotonic() - started, "load_after": os.getloadavg()}
                try:
                    if name == "inventory":
                        expected = inventory_hashes(out / "inventory.log", args.components)
                    else:
                        observations[name] = validate_export(out / (name + ".json"), name, expected)
                        record["observation"] = observations[name]
                except (OSError, ValueError, KeyError, TypeError) as error:
                    record["validation_error"] = str(error)
                journal.write(json.dumps(record) + "\n")
                journal.flush()
                if result.returncode or "validation_error" in record:
                    failed.append(name)
                    if name == "inventory":
                        break
    finally:
        metadata.update(ended=datetime.datetime.now(datetime.timezone.utc).isoformat(),
                        load_end=os.getloadavg(), failed_commands=failed, observations=observations)
        (out / "metadata.json").write_text(json.dumps(metadata, indent=2) + "\n")
        lease.close()
    return bool(failed) or any(r["verdict"] == "inconclusive" for r in observations.values())


if __name__ == "__main__":
    raise SystemExit(main())
