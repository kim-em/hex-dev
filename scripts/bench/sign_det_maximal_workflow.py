#!/usr/bin/env python3
"""Measure three complete maximal-support workflows; no timing law is assumed."""
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
from scripts.bench.sign_det_compare import archive_sources
from scripts.bench.sign_det_sparse import source_hashes
from scripts.bench.sign_det_maximal import validate_inventory

CASES = ("maximalOne", "maximalTwo", "maximalThree")
TRIALS = 6


def validate_export(path, case, expected, revision):
    data = json.loads(path.read_text())
    if data["export_schema_version"] != 1 or len(data["results"]) != 1:
        raise ValueError("wrong export schema")
    r = data["results"][0]
    required = {"function": "Hex.SignDetBench." + case, "kind": "fixed",
                "hashable": True, "hashes_agree": True, "budget_truncated": False,
                "observed_hash": hex(expected)}
    if any(r.get(k) != v for k, v in required.items()):
        raise ValueError("wrong, incomplete or incorrect workflow result")
    if r["env"]["git_commit"] != revision or r["env"]["git_dirty"] is not False:
        raise ValueError("measurement is not bound to clean sources")
    if r["config"] != {"warmup_first_iter": False, "warmup": True, "repeats": 1,
                       "min_total_seconds": 0.1, "max_seconds_per_call": 30,
                       "expected_hash": None}:
        raise ValueError("changed fixed measurement schedule")
    if len(r["points"]) != 1:
        raise ValueError("missing or extra observations")
    p = r["points"][0]
    if (p["status"] != "ok" or p["repeat_index"] != 0 or
            p["result_hash"] != hex(expected) or type(p["inner_repeats"]) is not int or
            p["inner_repeats"] <= 0 or type(p["total_nanos"]) is not int or
            p["total_nanos"] <= 0):
        raise ValueError("invalid fixed observation")
    nanos = r["median_nanos"]
    if (type(nanos) not in (float, int) or not math.isfinite(nanos) or
            nanos <= 0 or nanos != p["total_nanos"] // p["inner_repeats"]):
        raise ValueError("summary disagrees with retained observation")
    return nanos


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    if subprocess.check_output(["git", "status", "--porcelain"], cwd=ROOT):
        raise ValueError("commit measured sources first")
    subprocess.run(["lake", "build", "--no-build", "hexsigndet_bench"], cwd=ROOT, check=True)
    out = args.output.resolve()
    if out.is_relative_to(ROOT):
        raise ValueError("collect outside the source worktree")
    out.mkdir(parents=True, exist_ok=False)
    exe = ROOT / ".lake/build/bin/hexsigndet_bench"
    sources = source_hashes()
    for path in ("scripts/bench/sign_det_maximal_workflow.py", "scripts/bench/sign_det_maximal.py",
                 "scripts/bench/sign_det_compare.py", "scripts/bench/test_sign_det_maximal_workflow.py"):
        sources[path] = hashlib.sha256((ROOT / path).read_bytes()).hexdigest()
    cpu, lease = cpu_lease()
    os.sched_setaffinity(0, {cpu})
    metadata = {"kind": "fixed-complete-maximal-workflows", "trials": TRIALS,
                "cases": list(CASES), "schedule": "trial-major", "state": "running",
                "revision": subprocess.check_output(["git", "rev-parse", "HEAD"], cwd=ROOT, text=True).strip(),
                "source_sha256": sources, "binary_sha256": hashlib.sha256(exe.read_bytes()).hexdigest(),
                "host": platform.node(), "platform": platform.platform(), "cpu": cpu,
                "affinity": sorted(os.sched_getaffinity(0)), "load_start": os.getloadavg()}
    record = out / "metadata.json"
    try:
        archive_sources(out, metadata)
        record.write_text(json.dumps(metadata, indent=2) + "\n")
        for command, name in (("inspect-maximal", "inventory"),
                              ("inspect-maximal-workflow", "hashes")):
            with (out / (name + ".jsonl")).open("w") as stdout, (out / (name + ".stderr")).open("w") as stderr:
                subprocess.run([str(exe), command], cwd=ROOT, stdout=stdout, stderr=stderr, check=True)
        inventory = validate_inventory(out / "inventory.jsonl")
        hashes = [json.loads(line) for line in (out / "hashes.jsonl").read_text().splitlines()]
        if [r["queries"] for r in hashes] != [1, 2, 3] or any(
                r["inputHash"] != i["inputHash"] or type(r["expectedHash"]) is not int or
                not 0 <= r["expectedHash"] < 2**64 for r, i in zip(hashes, inventory, strict=True)):
            raise ValueError("workflow hashes do not bind the checked inputs")
        observations = {case: [] for case in CASES}
        with (out / "commands.jsonl").open("w") as journal:
            for trial in range(TRIALS):
                for case, binding in zip(CASES, hashes, strict=True):
                    path = out / f"{trial}-{case}.json"
                    command = [str(exe), "run", "--filter", case, "--export-file", str(path)]
                    with path.with_suffix(".stdout").open("w") as stdout, path.with_suffix(".stderr").open("w") as stderr:
                        result = subprocess.run(command, cwd=ROOT, stdout=stdout, stderr=stderr)
                    journal.write(json.dumps({"trial": trial, "case": case, "command": command,
                        "exit_code": result.returncode, "export": path.name, "load": os.getloadavg()}) + "\n")
                    journal.flush()
                    result.check_returncode()
                    observations[case].append(validate_export(path, case, binding["expectedHash"], metadata["revision"]))
        if any(hashlib.sha256((ROOT / p).read_bytes()).hexdigest() != h for p, h in sources.items()) or (
                hashlib.sha256(exe.read_bytes()).hexdigest() != metadata["binary_sha256"] or
                subprocess.check_output(["git", "rev-parse", "HEAD"], cwd=ROOT, text=True).strip() != metadata["revision"]):
            raise ValueError("sources or executable changed during collection")
        metadata.update(state="complete", observations=observations,
                        median_nanos={k: statistics.median(v) for k, v in observations.items()})
    except Exception as error:
        metadata.update(state="failed", error=str(error))
        raise
    finally:
        metadata["load_end"] = os.getloadavg()
        record.write_text(json.dumps(metadata, indent=2) + "\n")
        lease.close()
    print(json.dumps(metadata["median_nanos"]))


if __name__ == "__main__":
    main()
