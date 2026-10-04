#!/usr/bin/env python3
"""Capture kernel-only MetiTarski tower profiles from a retained executable.

Build a clean source commit, retain a copied executable and every command's
output, and filter 1000 Hz perf samples through LeanBench kernel sidecars.
Raw profiles stay outside the checkout; publish manifests and summaries.
"""
import argparse
import fcntl
import hashlib
import json
import os
from pathlib import Path
import platform
import shutil
import subprocess
import sys
import time

ROOT = Path(__file__).resolve().parents[2]
CASES = {
    "first": ("runMetiFirst", None, 15_000_000_000),
    "second": ("runMetiSecond", 3, 3_000_000_000),
}


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--stage", choices=CASES, required=True)
    parser.add_argument("--raw", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--profiler-root", type=Path, required=True)
    args = parser.parse_args()
    args.raw = args.raw.resolve()
    args.output = args.output.resolve()
    args.profiler_root = args.profiler_root.resolve()
    for path in (args.raw, args.output):
        if path == ROOT or ROOT in path.parents:
            parser.error("capture destinations must be outside the measured checkout")
    os.chdir(ROOT)
    args.raw.mkdir(parents=True, exist_ok=False)
    args.output.mkdir(parents=True, exist_ok=True)
    record = dict(stage=args.stage, host=platform.node(), platform=platform.platform(),
                  raw=str(args.raw), commands=[], status="running", sample_frequency_hz=1000)
    manifest = args.output / f"{args.stage}.manifest.json"
    if manifest.exists():
        parser.error("refusing to overwrite a prior manifest")
    lease = None

    def run(command):
        argv = list(map(str, command))
        result = subprocess.run(argv, capture_output=True, text=True)
        index = len(record["commands"])
        (args.raw / f"{index}.stdout").write_text(result.stdout)
        (args.raw / f"{index}.stderr").write_text(result.stderr)
        record["commands"].append(dict(argv=argv, exit_code=result.returncode))
        manifest.write_text(json.dumps(record, indent=2) + "\n")
        result.check_returncode()
        return result.stdout

    try:
        record["commit"] = run(["git", "rev-parse", "HEAD"]).strip()
        if run(["git", "status", "--porcelain"]).strip():
            raise RuntimeError("measurement source is dirty")
        record["dirty"] = False
        record["profiler_commit"] = run(["git", "-C", args.profiler_root, "rev-parse", "HEAD"]).strip()
        if run(["git", "-C", args.profiler_root, "status", "--porcelain"]).strip():
            raise RuntimeError("profile filter source is dirty")
        for key, command in (("samply_version", ["samply", "--version"]),
                             ("perf_version", ["perf", "--version"]),
                             ("lean_version", ["lake", "env", "lean", "--version"]),
                             ("lake_version", ["lake", "--version"])):
            record[key] = run(command).strip()
        run(["lake", "build", "hexrealclosure_bench"])
        built = ROOT / ".lake/build/bin/hexrealclosure_bench"
        snapshot = args.raw / "hexrealclosure_bench"
        shutil.copy2(built, snapshot)
        record["executable_sha256"] = digest(snapshot)
        record["executable_snapshot"] = str(snapshot)
        cpus = sorted(os.sched_getaffinity(0))
        offset = os.getpid() % len(cpus)
        for cpu in cpus[offset:] + cpus[:offset]:
            lease = open(f"/tmp/hex-bench-cpu-{cpu}.lock", "a")
            try:
                fcntl.flock(lease, fcntl.LOCK_EX | fcntl.LOCK_NB)
                break
            except BlockingIOError:
                lease.close()
                lease = None
        else:
            raise RuntimeError("all measurement CPU leases are held")
        os.sched_setaffinity(0, {cpu})
        record.update(cpu=cpu, affinity=sorted(os.sched_getaffinity(0)), load=os.getloadavg())
        name, parameter, duration = CASES[args.stage]
        record.update(function="Hex.RealClosure.Bench." + name, parameter=parameter,
                      target_inner_nanos=duration)
        anchor = args.raw / "spawn-anchor.json"
        anchor.write_text(json.dumps(dict(wall_ns_at_spawn=time.time_ns(),
                                         mono_ns_at_spawn=time.monotonic_ns())))
        profile = [snapshot, "profile", record["function"]]
        if parameter is not None:
            profile.extend(["--param", parameter])
        profile.extend(["--target-inner-nanos", duration, "--profiler", "env"])
        measured = run(["perf", "record", "--clockid", "mono", "-e", "cycles:u", "-F", "1000",
             "--call-graph", "dwarf", "-o", args.raw / "perf.data", "--", "env",
             f"LEAN_BENCH_TIMED_REGIONS_SIDECAR={args.raw}/timed-%p.jsonl", *profile])
        rows = [json.loads(line) for line in measured.splitlines() if line.startswith("{")]
        if len(rows) != 1 or rows[0].get("status") != "ok" or rows[0].get("result_hash") != 1:
            raise RuntimeError("profile did not return the expected complete-root result")
        record["measurement"] = rows[0]
        run(["samply", "import", "--save-only", "--no-open", "--unstable-presymbolicate",
             "-o", args.raw / "samply.json.gz", args.raw / "perf.data"])
        samples = run(["perf", "script", "--ns", "-F", "pid,tid,time,event",
                       "-i", args.raw / "perf.data"])
        (args.raw / "perf-samples.txt").write_text(samples)
        run([sys.executable, "scripts/profile/normalize_perf.py", "--profile", args.raw / "samply.json.gz",
             "--perf-script", args.raw / "perf-samples.txt", "--spawn-anchor", anchor,
             "--output", args.raw / "normalized.json.gz"])
        sidecars = list(args.raw.glob("timed-*.jsonl"))
        if len(sidecars) != 1:
            raise RuntimeError("expected one timed-region sidecar")
        run([sys.executable, args.profiler_root / "scripts/filter_samply.py",
             "--samply-json", args.raw / "normalized.json.gz", "--sidecar", sidecars[0],
             "--spawn-anchor", anchor, "--out", args.raw / "filtered.json.gz",
             "--diagnostics", args.raw / "diagnostics.json", "--label-filter", "kernel"])
        run([sys.executable, "scripts/profile/elf_symbols.py", args.raw / "filtered.json.gz",
             "--output", args.raw / "symbols.json"])
        diagnostics = json.loads((args.raw / "diagnostics.json").read_text())
        run([sys.executable, "scripts/profile/summarize_profile.py", args.raw / "filtered.json.gz",
             "--symbols", args.raw / "symbols.json", "--diagnostics", args.raw / "diagnostics.json",
             "--thread", diagnostics["bench_thread_name"], "--top", 20,
             "--output", args.output / f"{args.stage}.summary.json"])
        if run(["git", "rev-parse", "HEAD"]).strip() != record["commit"] or \
                run(["git", "status", "--porcelain"]).strip():
            raise RuntimeError("measurement source changed during capture")
        record["status"] = "profiled"
    except BaseException as error:
        record.update(status="failed", error=str(error))
        raise
    finally:
        diagnostics = args.raw / "diagnostics.json"
        if diagnostics.exists():
            record["diagnostics"] = json.loads(diagnostics.read_text())
        record["artifacts"] = {p.name: digest(p) for p in args.raw.iterdir() if p.is_file()}
        manifest.write_text(json.dumps(record, indent=2) + "\n")
        if lease is not None:
            lease.close()


if __name__ == "__main__":
    main()
