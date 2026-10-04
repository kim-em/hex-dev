#!/usr/bin/env python3
"""Capture kernel-only MetiTarski tower profiles from a retained executable.

Build a clean source commit, retain a copied executable and every command's
output, and filter 1000 Hz perf samples through LeanBench kernel sidecars.
Raw profiles stay outside the checkout; publish manifests and summaries.
"""
import argparse
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
sys.path.insert(0, str(ROOT / "scripts/bench"))
from cpu_lease import cpu_lease
CASES = {
    "first": ("runMetiFirst", None, 15_000_000_000),
    "second": ("runMetiSecond", 3, 3_000_000_000),
}


def digest(path):
    with path.open("rb") as stream:
        return hashlib.file_digest(stream, "sha256").hexdigest()


def measurement_rows(text):
    return [json.loads(line) for line in text.splitlines() if line.startswith("{")]


def validate_measurement(rows, commit):
    if len(rows) != 1 or rows[0].get("status") != "ok" or rows[0].get("result_hash") != "0x1":
        raise RuntimeError("profile did not return the expected complete-root result")
    env = rows[0].get("env", {})
    if env.get("git_commit") != commit or env.get("git_dirty") is not False:
        raise RuntimeError("measurement row is not bound to the clean capture commit")
    return rows[0]


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--stage", choices=CASES, required=True)
    parser.add_argument("--raw", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--profiler-root", type=Path, required=True)
    parser.add_argument("--postprocess", type=Path, help="retained capture manifest; reuse raw samples without measurement")
    args = parser.parse_args()
    args.raw = args.raw.resolve()
    args.output = args.output.resolve()
    args.profiler_root = args.profiler_root.resolve()
    for path in (args.raw, args.output):
        if path == ROOT or ROOT in path.parents:
            parser.error("capture destinations must be outside the measured checkout")
    os.chdir(ROOT)
    if args.postprocess:
        args.postprocess = args.postprocess.resolve()
        if not args.raw.is_dir():
            parser.error("postprocessing requires the retained raw capture directory")
    else:
        args.raw.mkdir(parents=True, exist_ok=False)
    args.output.mkdir(parents=True, exist_ok=True)
    record = dict(stage=args.stage, host=platform.node(), platform=platform.platform(),
                  raw=str(args.raw), commands=[], status="running", sample_frequency_hz=1000)
    manifest = args.output / f"{args.stage}.manifest.json"
    if manifest.exists():
        parser.error("refusing to overwrite a prior manifest")
    work = args.output / f"{args.stage}.postprocess" if args.postprocess else args.raw
    work.mkdir(exist_ok=not args.postprocess)
    lease = None

    def run(command):
        argv = list(map(str, command))
        result = subprocess.run(argv, capture_output=True, text=True)
        index = len(record["commands"])
        (work / f"{index}.stdout").write_text(result.stdout)
        (work / f"{index}.stderr").write_text(result.stderr)
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
        package_pin = next(p["rev"] for p in json.loads((ROOT / "lake-manifest.json").read_text())["packages"] if p["name"] == "lean-bench")
        if args.postprocess:
            capture = json.loads(args.postprocess.read_text())
            if capture["stage"] != args.stage or Path(capture["raw"]).resolve() != args.raw:
                raise RuntimeError("capture manifest does not match the requested stage and raw directory")
            for name, expected in capture["artifacts"].items():
                if digest(args.raw / name) != expected:
                    raise RuntimeError(f"retained artifact changed: {name}")
            record.update(capture_manifest=str(args.postprocess), capture_manifest_sha256=digest(args.postprocess),
                          capture_commit=capture["commit"], capture_dirty=capture["dirty"],
                          original_status=capture["status"], original_error=capture.get("error"))
            if capture["dirty"] is not False:
                raise RuntimeError("capture source was dirty")
            perf_index = next(i for i,c in enumerate(capture["commands"]) if c["argv"][:2] == ["perf", "record"])
            rows = measurement_rows((args.raw / f"{perf_index}.stdout").read_text())
            record["measurement_rows"] = rows
            record["measurement"] = validate_measurement(rows, capture["commit"])
            capture_commit = capture["commit"]
            anchor = args.raw / "spawn-anchor.json"
        else:
            package_root = ROOT / ".lake/packages/lean-bench"
            if run(["git", "-C", package_root, "rev-parse", "HEAD"]).strip() != package_pin or run(["git", "-C", package_root, "status", "--porcelain"]).strip():
                raise RuntimeError("compiled lean-bench dependency is not at its clean pinned revision")
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
            cpu, lease = cpu_lease()
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
                 "--call-graph", "dwarf,65528", "-o", args.raw / "perf.data", "--", "env",
                 f"LEAN_BENCH_TIMED_REGIONS_SIDECAR={args.raw}/timed-%p.jsonl", *profile])
            rows = measurement_rows(measured)
            record["measurement_rows"] = rows
            record["measurement"] = validate_measurement(rows, record["commit"])
            capture_commit = record["commit"]
        pinned = json.loads(run(["git", "show", f"{capture_commit}:lake-manifest.json"]))
        record["compiled_lean_bench_commit"] = next(p["rev"] for p in pinned["packages"] if p["name"] == "lean-bench")
        run(["samply", "import", "--save-only", "--no-open", "--unstable-presymbolicate",
             "-o", work / "samply.json.gz", args.raw / "perf.data"])
        samples = run(["perf", "script", "--ns", "-F", "pid,tid,time,event",
                       "-i", args.raw / "perf.data"])
        (work / "perf-samples.txt").write_text(samples)
        run([sys.executable, "scripts/profile/normalize_perf.py", "--profile", work / "samply.json.gz",
             "--perf-script", work / "perf-samples.txt", "--spawn-anchor", anchor,
             "--output", work / "normalized.json.gz"])
        sidecars = list(args.raw.glob("timed-*.jsonl"))
        if len(sidecars) != 1:
            raise RuntimeError("expected one timed-region sidecar")
        run([sys.executable, args.profiler_root / "scripts/filter_samply.py",
             "--samply-json", work / "normalized.json.gz", "--sidecar", sidecars[0],
             "--spawn-anchor", anchor, "--out", work / "filtered.json.gz",
             "--diagnostics", work / "diagnostics.json", "--label-filter", "kernel"])
        run([sys.executable, "scripts/profile/elf_symbols.py", work / "filtered.json.gz",
             "--output", work / "symbols.json"])
        diagnostics = json.loads((work / "diagnostics.json").read_text())
        run([sys.executable, "scripts/profile/summarize_profile.py", work / "filtered.json.gz",
             "--symbols", work / "symbols.json", "--diagnostics", work / "diagnostics.json",
             "--thread", diagnostics["bench_thread_name"], "--top", 20,
             "--benchmark", "Hex.RealClosure.Bench." + CASES[args.stage][0],
             "--output", args.output / f"{args.stage}.summary.json"])
        if run(["git", "rev-parse", "HEAD"]).strip() != record["commit"] or \
                run(["git", "status", "--porcelain"]).strip():
            raise RuntimeError("measurement source changed during capture")
        if run(["git", "-C", args.profiler_root, "rev-parse", "HEAD"]).strip() != record["profiler_commit"] or run(["git", "-C", args.profiler_root, "status", "--porcelain"]).strip():
            raise RuntimeError("profile filter source changed during processing")
        record["summary_sha256"] = digest(args.output / f"{args.stage}.summary.json")
        record["status"] = "profiled"
    except BaseException as error:
        record.update(status="failed", error=str(error))
        raise
    finally:
        diagnostics = work / "diagnostics.json"
        if diagnostics.exists():
            record["diagnostics"] = json.loads(diagnostics.read_text())
        record["artifacts"] = {p.name: digest(p) for p in args.raw.iterdir() if p.is_file()}
        record["postprocess_artifacts"] = {p.name: digest(p) for p in work.iterdir() if p.is_file()}
        manifest.write_text(json.dumps(record, indent=2) + "\n")
        if lease is not None:
            lease.close()


if __name__ == "__main__":
    main()
