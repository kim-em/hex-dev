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
    parser.add_argument("--executable", type=Path, help="a previously built, unchanged benchmark binary")
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--control-only", action="store_true",
                        help="measure only the new odd-remainder coefficient control")
    parser.add_argument("--bit-cost-only", action="store_true",
                        help="validate the declared multiword query-degree models")
    parser.add_argument("--replay-bit-cost-only", action="store_true",
                        help="validate the declared dyadic replay bit-cost model")
    parser.add_argument("--rational-bit-cost-only", action="store_true",
                        help="validate the rational high-query bit-cost model")
    args = parser.parse_args()
    if sum([args.control_only, args.bit_cost_only, args.replay_bit_cost_only, args.rational_bit_cost_only]) > 1:
        parser.error("select at most one dedicated measurement")
    out = args.output.resolve()
    out.mkdir(parents=True, exist_ok=False)
    exe = (args.executable or (ROOT / ".lake/build/bin/hexsturm_bench")).resolve()
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
    model = ROOT / "reports/sturm-bit-cost-models.md"
    if args.bit_cost_only or args.replay_bit_cost_only or args.rational_bit_cost_only:
        metadata["derivation_sha256"] = hashlib.sha256(model.read_bytes()).hexdigest()
        (out / "derivation.md").write_bytes(model.read_bytes())
    commands = [
        (["axes"], "axes.jsonl"),
        (["diagnostics"], "degree-diagnostics.jsonl"),

    ]
    if args.control_only:
        commands = [(["coefficient-control"], "axes.jsonl")]
    if args.bit_cost_only:
        commands = [(["run", "Hex.SturmBench.runIntegerHigh", "Hex.SturmBench.runInitialHigh",
                      "Hex.SturmBench.runReplayHigh", "--export-file", str(out / "query-bits.json")],
                     "query-bits.log")]
    if args.replay_bit_cost_only:
        commands = [(["run", "Hex.SturmBench.runReplay", "--export-file", str(out / "replay-bits.json")],
                     "replay-bits.log")]
    if args.rational_bit_cost_only:
        commands = [(["run", "Hex.SturmBench.runRationalHigh", "--export-file", str(out / "rational-bits.json")],
                     "rational-bits.log")]
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
        rows = [] if args.bit_cost_only or args.replay_bit_cost_only or args.rational_bit_cost_only else [json.loads(line) for line in (out / "axes.jsonl").read_text().splitlines()]
        if rows:
            (out / "fixtures.jsonl").write_text("".join(
                json.dumps(row) + "\n" for row in rows if row["kind"] == "fixture"))
    finally:
        metadata.update(end=datetime.datetime.now(datetime.timezone.utc).isoformat(), load_end=os.getloadavg())
        (out / "metadata.json").write_text(json.dumps(metadata, indent=2) + "\n")
        lease.close()


if __name__ == "__main__":
    main()
