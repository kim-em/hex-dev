#!/usr/bin/env python3
"""Retain fixed size-axis observations and wider Sturm benchmark schedules.

No verdict/model overrides, sample filtering, quiet-host checks or automatic
reruns. Build hexsturm_bench first. Instrumented diagnostics are untimed.
"""
from __future__ import annotations

import argparse
import datetime
import hashlib
import json
import os
from pathlib import Path
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT))
from scripts.bench.det_symbolic_sweep import cpu_lease  # noqa: E402


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    out = args.output.resolve()
    out.mkdir(parents=True, exist_ok=False)
    exe = ROOT / ".lake/build/bin/hexsturm_bench"
    source = ROOT / "bench/HexSturm/Bench.lean"
    cpu, lease = cpu_lease()
    os.sched_setaffinity(0, {cpu})
    metadata = {
        "cpu": cpu, "host": os.uname().nodename,
        "start": datetime.datetime.now(datetime.timezone.utc).isoformat(),
        "load_start": os.getloadavg(),
        "git_head": subprocess.check_output(["git", "rev-parse", "HEAD"], cwd=ROOT, text=True).strip(),
        "git_status": subprocess.check_output(["git", "status", "--short"], cwd=ROOT, text=True),
        "binary_sha256": hashlib.sha256(exe.read_bytes()).hexdigest(),
        "source_sha256": hashlib.sha256(source.read_bytes()).hexdigest(),
        "commands": [],
    }
    (out / "registration.lean.txt").write_bytes(source.read_bytes())
    commands = [
        (["axes"], "axes.jsonl"),
        (["diagnostics"], "degree-diagnostics.jsonl"),
        (["run", "Hex.SturmBench.runReplay", "--param-floor", "8", "--param-ceiling", "128",
          "--param-schedule", "doubling", "--export-file", str(out / "replay-wide.json")], "replay-wide.log"),
        (["run", "Hex.SturmBench.runIntegerHigh", "Hex.SturmBench.runInitialHigh",
          "Hex.SturmBench.runReplayHigh", "--param-floor", "16", "--param-ceiling", "1024",
          "--param-schedule", "doubling", "--export-file", str(out / "query-wide.json")], "query-wide.log"),
    ]
    try:
        for command, filename in commands:
            argv = [str(exe), *command]
            print(" ".join(argv), flush=True)
            with (out / filename).open("w") as log:
                result = subprocess.run(argv, cwd=ROOT, stdout=log, stderr=subprocess.STDOUT)
            metadata["commands"].append({"argv": argv, "exit_code": result.returncode})
            (out / "metadata.json").write_text(json.dumps(metadata, indent=2) + "\n")
            if result.returncode:
                raise RuntimeError(f"command failed ({result.returncode}); output retained in {filename}")
        rows = [json.loads(line) for line in (out / "axes.jsonl").read_text().splitlines()]
        (out / "fixtures.jsonl").write_text("".join(
            json.dumps(row) + "\n" for row in rows if row["kind"] == "fixture"))
    finally:
        metadata.update(end=datetime.datetime.now(datetime.timezone.utc).isoformat(), load_end=os.getloadavg())
        (out / "metadata.json").write_text(json.dumps(metadata, indent=2) + "\n")
        lease.close()


if __name__ == "__main__":
    main()
