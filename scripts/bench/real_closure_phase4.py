#!/usr/bin/env python3
"""Retain a compiled functional run; this is not a scientific timing schedule."""
import argparse
from datetime import datetime, timezone
import hashlib
import json
import os
from pathlib import Path
import platform
import subprocess
import sys
import time

REPO = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(REPO))
from scripts.bench.cpu_lease import cpu_lease


def git(*args):
    return subprocess.check_output(["git", *args], cwd=REPO, text=True).strip()


def utc():
    return datetime.now(timezone.utc).isoformat()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("backend", choices=["native", "canonical"])
    parser.add_argument("output", type=Path)
    parser.add_argument("--timeout", type=float, default=1800)
    args = parser.parse_args()
    if args.timeout <= 0:
        parser.error("timeout must be positive")
    if REPO in args.output.resolve().parents:
        parser.error("retain runs outside the checkout; archive them afterwards")
    if git("status", "--porcelain"):
        parser.error("run from a clean source checkout, including untracked files")
    source_head = git("rev-parse", "HEAD")
    # Refuse to replace evidence, including interrupted earlier runs.
    args.output.mkdir(parents=True, exist_ok=False)
    metadata_path = args.output / "metadata.json"
    metadata_path.write_text(json.dumps({"status": "building", "source_head": source_head,
                                        "started_utc": utc()}, indent=2) + "\n")
    build_command = ["lake", "build", "hexrealclosure_phase4"]
    with (args.output / "build.log").open("w") as log:
        build = subprocess.run(build_command, cwd=REPO, stdout=log, stderr=log)
    if build.returncode != 0:
        metadata_path.write_text(json.dumps({"status": "build failed", "source_head": source_head,
                                            "exit_code": build.returncode, "ended_utc": utc()},
                                           indent=2) + "\n")
        return 1
    if git("rev-parse", "HEAD") != source_head or git("status", "--porcelain"):
        raise RuntimeError("source changed during the retained build")
    cpu, lease = cpu_lease()
    executable = REPO / ".lake/build/bin/hexrealclosure_phase4"
    command = ["taskset", "-c", str(cpu), str(executable), "metitarski", args.backend]
    metadata = {
        "purpose": "compiled functional validation; not a scientific timing comparison",
        "backend": args.backend, "source_head": source_head, "source_dirty": False,
        "build_command": build_command,
        "build_log_sha256": hashlib.sha256((args.output / "build.log").read_bytes()).hexdigest(),
        "executable_sha256": hashlib.sha256(executable.read_bytes()).hexdigest(),
        "host": platform.node(), "kernel": platform.release(), "os": platform.platform(),
        "cpu_model": next((line.split(":", 1)[1].strip() for line in
                           Path("/proc/cpuinfo").read_text().splitlines()
                           if line.startswith("model name")), "unknown"),
        "cpu": cpu, "affinity": sorted(os.sched_getaffinity(0)),
        "command": command, "operational_timeout_seconds": args.timeout,
        "started_utc": utc(),
    }
    path = metadata_path
    path.write_text(json.dumps(metadata, indent=2) + "\n")
    started = time.monotonic()
    with (args.output / "stdout.jsonl").open("w") as out, \
            (args.output / "stderr.log").open("w") as err:
        process = subprocess.Popen(command, cwd=REPO, stdout=out, stderr=err)
        try:
            process.wait(timeout=args.timeout)
            metadata["status"] = "completed" if process.returncode == 0 else "failed"
        except subprocess.TimeoutExpired:
            process.kill()
            process.wait()
            metadata["status"] = "operational timeout"
        except KeyboardInterrupt:
            process.kill()
            process.wait()
            metadata["status"] = "interrupted"
        metadata["exit_code"] = process.returncode
        metadata["termination_signal"] = -process.returncode if process.returncode < 0 else None
    metadata["elapsed_wall_seconds"] = time.monotonic() - started
    metadata["ended_utc"] = utc()
    path.write_text(json.dumps(metadata, indent=2) + "\n")
    print(json.dumps(metadata, indent=2))
    # Keep the lease alive through process completion and evidence writes.
    lease.close()
    return 0 if metadata["exit_code"] == 0 else 1


if __name__ == "__main__":
    raise SystemExit(main())
