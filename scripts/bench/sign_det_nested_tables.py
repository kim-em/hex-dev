#!/usr/bin/env python3
"""Collect BKR production and supplied-tree replay over fixed nested fields."""
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
from scripts.bench.sign_det_nested_signs import constant

DEPTHS = [1, 2]
SIZES = [8, 16, 32, 64, 128]
TRIALS = 6
PREFIX = "Hex.SignDetBench.NestedTables."
CONFIG = {"param_floor": SIZES[0], "param_ceiling": SIZES[-1], "outer_trials": TRIALS,
          "param_schedule": {"kind": "custom", "params": SIZES},
          "target_inner_nanos": 100000000, "max_seconds_per_call": 300,
          "signal_floor_multiplier": 1, "cache_mode": "warm",
          "verdict_warmup_fraction": 0.2, "slope_tolerance": 0.15,
          "narrow_range_noise_floor": 1.5}


def validate_inputs(path):
    rows = [json.loads(line) for line in Path(path).read_text().splitlines()]
    if [(row["depth"], row["queries"]) for row in rows] != [
            (depth, size) for depth in DEPTHS for size in SIZES]:
        raise ValueError("missing or reordered nested-field inputs")
    expected = {}
    def literal(value):
        return json.dumps(value, sort_keys=True, separators=(",", ":"))
    for row in rows:
        if type(row["depth"]) is not int or type(row["queries"]) is not int:
            raise ValueError("noninteger depth or query count")
        depth, size = row["depth"], row["queries"]
        epsilon = {"num": [constant(0, depth-1), constant(1, depth-1)],
                   "den": [constant(1, depth-1)]}
        # P=X has only root zero. Each supplied constant query is the positive
        # newest infinitesimal; this elementary oracle uses no Tarski/matrix code.
        if (literal(row["head"]) != literal([constant(0, depth), constant(1, depth)]) or
                literal(row["coefficient"]) != literal(epsilon) or
                literal(row["queryPolynomials"]) != literal([[epsilon]]*size) or
                literal(row["table"]) != literal([[[1]*size, 1]])):
            raise ValueError("wrong literal polynomial, coefficient or complete one-root table")
        sizes = {"headDegree": 1, "queryDegree": 0, "rootCount": 1, "realizedSupport": 1,
                 "treeNodes": 2*size-1, "momentSlots": 4*size-1, "maxMatrixSize": 3}
        if any(type(row.get(key)) is not int or row[key] != value for key, value in sizes.items()):
            raise ValueError("wrong nested-field evidence dimensions")
        if (type(row.get("graphNodes")) is not int or row["graphNodes"] < 1 or
                type(row.get("graphEdges")) is not int or row["graphEdges"] < 0):
            raise ValueError("invalid graph inventory")
        for key in ("inputHash", "productionResultHash", "replayResultHash"):
            if type(row.get(key)) is not int or not 0 <= row[key] < 2**64:
                raise ValueError("invalid inventory hash")
        expected[depth, size] = row
    return expected


def validate_result(path, name, expected, revision):
    export = json.loads(Path(path).read_text())
    if export["export_schema_version"] != 1 or len(export["results"]) != 1:
        raise ValueError("wrong nested-table export")
    result = export["results"][0]
    depth = int(name[-1])
    if (name not in [op+str(d) for d in DEPTHS for op in ("runProduce", "runTree")] or
            result["function"] != PREFIX+name or result["kind"] != "parametric" or
            result["hashable"] is not True or result["budget_truncated"] is not False or
            result["complexity_formula"].replace(" ", "") != "s*(Nat.log2s+1)" or
            result["env"]["git_commit"] != revision or result["env"]["git_dirty"] is not False or
            any(type(result["config"][key]) is not type(value) or result["config"][key] != value
                for key, value in CONFIG.items())):
        raise ValueError("wrong registration, model, settings or source binding")
    points = result["points"]
    if [(p["trial_index"], p["param"]) for p in points] != [
            (trial, size) for trial in range(TRIALS) for size in SIZES]:
        raise ValueError("incomplete or reordered nested-table schedule")
    key = "productionResultHash" if name.startswith("runProduce") else "replayResultHash"
    for point in points:
        if (point["status"] != "ok" or point["result_hash"] != hex(expected[depth, point["param"]][key]) or
                point["part_of_verdict"] is not True or point["below_signal_floor"] is not False or
                type(point["per_call_nanos"]) not in (int, float) or
                not math.isfinite(point["per_call_nanos"]) or point["per_call_nanos"] <= 0 or
                type(point["inner_repeats"]) is not int or point["inner_repeats"] < 1 or
                type(point["trial_index"]) is not int or type(point["param"]) is not int or
                type(point["peak_rss_kb"]) is not int or point["peak_rss_kb"] < 1 or
                point["alloc_bytes"] is not None):
            raise ValueError("failed or substituted nested-table observation")
    if result["verdict"] not in ("consistent_with_declared_complexity", "inconclusive"):
        raise ValueError("unknown nested-table verdict")
    return {key: result[key] for key in ("verdict", "slope", "complexity_formula", "advisories")}



def run_owned(command, stdout, stderr):
    """Own benchmark descendants while waiting; always terminate the group."""
    import signal
    process = subprocess.Popen(command, cwd=ROOT, stdout=stdout, stderr=stderr,
                               start_new_session=True)
    try:
        os.waitid(os.P_PID, process.pid, os.WEXITED | os.WNOWAIT)
    finally:
        try:
            os.killpg(process.pid, signal.SIGKILL)
        except ProcessLookupError:
            pass
        process.wait()
    return process.returncode


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    revision = subprocess.check_output(["git", "rev-parse", "HEAD"], cwd=ROOT, text=True).strip()
    if subprocess.check_output(["git", "status", "--porcelain"], cwd=ROOT, text=True):
        raise ValueError("commit sources before collection")
    subprocess.run(["lake", "build", "--no-build", "hexsigndet_bench"], cwd=ROOT, check=True)
    out = args.output.resolve()
    if out.is_relative_to(ROOT):
        raise ValueError("collect outside the worktree")
    out.mkdir(parents=True, exist_ok=False)
    executable = ROOT / ".lake/build/bin/hexsigndet_bench"
    digest = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
    sources = source_hashes()
    for library in ("HexRationalFn", "HexOrderedFn"):
        for p in [ROOT/(library+".lean"), *(ROOT/library).rglob("*.lean")]:
            sources[str(p.relative_to(ROOT))] = digest(p)
    for name in ("scripts/bench/sign_det_nested_tables.py", "scripts/bench/test_sign_det_nested_tables.py",
                 "scripts/bench/sign_det_nested_signs.py", "scripts/bench/sign_det_compare.py",
                 "scripts/bench/sign_det_joint_timing.py", "reports/sign-det-nested-tables.md"):
        sources[name] = digest(ROOT/name)
    cpu, lease = cpu_lease()
    os.sched_setaffinity(0, {cpu})
    metadata = {"kind": "nested-table-timing", "revision": revision, "source_sha256": sources,
                "binary_sha256": digest(executable), "harness_binding": harness_binding(ROOT),
                "host": platform.node(), "cpu": cpu, "affinity": sorted(os.sched_getaffinity(0)),
                "load_before": os.getloadavg(), "runs": [], "state": "running"}
    def save():
        temporary = out/"metadata.tmp"
        temporary.write_text(json.dumps(metadata, indent=2)+"\n")
        os.replace(temporary, out/"metadata.json")
    def run(label, arguments):
        row = {"label": label, "command": [str(executable), *arguments], "state": "running"}
        metadata["runs"].append(row); save()
        start = time.monotonic()
        with (out/(label+".stdout")).open("w") as stdout, (out/(label+".stderr")).open("w") as stderr:
            code = run_owned(row["command"], stdout, stderr)
        row.update(state="complete", exit_code=code, elapsed_seconds=time.monotonic()-start)
        save()
        return code
    try:
        save()
        archive_sources(out, metadata); save()
        if run("inputs", ["inspect-nested-tables"]):
            raise ValueError("nested-table input inspection failed")
        expected = validate_inputs(out/"inputs.stdout")
        summaries, errors = {}, []
        for depth in DEPTHS:
            for operation in ("runProduce", "runTree"):
                name = operation+str(depth)
                target = out/(name+".json")
                code = run(name, ["run", PREFIX+name, "--export-file", str(target)])
                try:
                    if code not in (0, 1):
                        raise ValueError(f"runner exit {code}")
                    summaries[name] = validate_result(target, name, expected, revision)
                except (ValueError, KeyError, TypeError, IndexError, OSError) as error:
                    errors.append({"name": name, "error": str(error)})
        (out/"summary.json").write_text(json.dumps({"observations": summaries,
                                                   "validation_errors": errors}, indent=2)+"\n")
        if errors:
            raise ValueError("invalid observations; all scheduled arms retained")
        metadata.update(state="complete", scientific_samples=TRIALS*len(SIZES)*len(DEPTHS)*2)
        code = int(any(s["verdict"] == "inconclusive" for s in summaries.values()))
    except BaseException as error:
        metadata.update(state="failed", exception=type(error).__name__, error=str(error))
        raise
    finally:
        try:
            metadata["source_sha256_after"] = {name: digest(ROOT/name) for name in sources}
            metadata["binary_sha256_after"] = digest(executable)
            metadata["harness_binding_after"] = harness_binding(ROOT)
            metadata["revision_after"] = subprocess.check_output(["git", "rev-parse", "HEAD"], cwd=ROOT, text=True).strip()
            metadata["git_status_after"] = subprocess.check_output(["git", "status", "--porcelain"], cwd=ROOT, text=True)
            metadata["source_unchanged"] = (sources == metadata["source_sha256_after"] and
                metadata["binary_sha256_after"] == metadata["binary_sha256"] and
                metadata["harness_binding_after"] == metadata["harness_binding"] and
                metadata["revision_after"] == revision and metadata["git_status_after"] == "")
            if not metadata["source_unchanged"]:
                metadata.update(state="failed", final_identity_error="source, binary or harness changed")
            if metadata["state"] != "complete":
                metadata.pop("scientific_samples", None)
            metadata["file_sha256"] = {p.name: digest(p) for p in out.iterdir()
                                       if p.is_file() and p.name not in ("metadata.json", "metadata.tmp")}
            metadata["load_after"] = os.getloadavg(); save()
        finally:
            lease.close()
    if metadata["state"] != "complete":
        raise RuntimeError("source changed; observations retained")
    return code


if __name__ == "__main__":
    raise SystemExit(main())
