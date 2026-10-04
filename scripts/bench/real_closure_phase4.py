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
    # Refuse to replace evidence, including interrupted earlier runs.
    args.output.mkdir(parents=True, exist_ok=False)
    cpu, lease = cpu_lease()
    executable = REPO / ".lake/build/bin/hexrealclosure_phase4"
    command = ["taskset", "-c", str(cpu), str(executable), "metitarski", args.backend]
    metadata = {
        "purpose": "compiled functional validation; not a scientific timing comparison",
        "backend": args.backend, "source_head": git("rev-parse", "HEAD"),
        "source_dirty": bool(git("status", "--porcelain")),
        "source_diff_sha256": hashlib.sha256(git("diff", "HEAD").encode()).hexdigest(),
        "executable_sha256": hashlib.sha256(executable.read_bytes()).hexdigest(),
        "host": platform.node(), "kernel": platform.release(), "os": platform.platform(),
        "cpu_model": next((line.split(":", 1)[1].strip() for line in
                           Path("/proc/cpuinfo").read_text().splitlines()
                           if line.startswith("model name")), "unknown"),
        "cpu": cpu, "affinity": sorted(os.sched_getaffinity(0)),
        "command": command, "operational_timeout_seconds": args.timeout,
        "started_utc": utc(),
        "build_provenance_limit": "Execution source snapshot; record the build log separately.",
    }
    path = args.output / "metadata.json"
    path.write_text(json.dumps(metadata, indent=2) + "\n")
    started = time.monotonic()
    with (args.output / "stdout.jsonl").open("w") as out, \
            (args.output / "stderr.log").open("w") as err:
        process = subprocess.Popen(command, cwd=REPO, stdout=out, stderr=err)
        try:
            process.wait(timeout=args.timeout)
            metadata["status"] = "completed"
        except subprocess.TimeoutExpired:
            process.kill()
            process.wait()
            metadata["status"] = "operational timeout"
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
