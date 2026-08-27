#!/usr/bin/env python3
"""Generate and fresh-elaborate candidate HexPrimality prime tables.

Each sample invokes the standard ``#rebuild_primeTable`` generator, checks that
its emitted source is byte-identical to the other samples for that bound, then
fresh-elaborates the emitted replay module and records source/olean size and raw
wall times.  Candidate batches retain the committed table's maximum of eight
sieve bases per kernel-replayed chunk.

Scientific run::

    python3 scripts/bench/primality_table_sweep.py --samples 3 \
      --output reports/bench-results/hex-primality-table-issue-9757-chungus2.json

``--report FILE`` reproduces the summary without measuring.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import math
import os
import platform
from pathlib import Path
import re
import signal
import shlex
import socket
import statistics
import struct
import subprocess
import sys
import tempfile
import time

try:
    import idle_core
except ModuleNotFoundError:  # imported as ``scripts.bench.*`` by unit tests
    from scripts.bench import idle_core


ROOT = Path(__file__).resolve().parents[2]
DEFAULT_BOUNDS = (10_000, 100_000, 1_000_000, 10_000_000)


def host_state(cpu: int) -> dict:
    """Record enough host state to interpret and reproduce a timing run."""
    model = "unknown"
    try:
        blocks = Path("/proc/cpuinfo").read_text().split("\n\n")
        block = next((item for item in blocks
                      if f"processor\t: {cpu}" in item), blocks[0])
        for line in block.splitlines():
            if line.startswith("model name"):
                model = line.partition(":")[2].strip()
                break
    except (OSError, StopIteration):
        pass
    try:
        pressure = Path("/proc/pressure/cpu").read_text().strip()
    except OSError:
        pressure = "unavailable"
    return {
        "cpu": cpu,
        "affinity": sorted(os.sched_getaffinity(0)),
        "cpu_model": model,
        "load_average": list(os.getloadavg()),
        "cpu_pressure": pressure,
    }


def lean_version() -> str:
    return subprocess.run(
        ["lake", "env", "lean", "--version"], cwd=ROOT, check=True,
        capture_output=True, text=True,
    ).stdout.strip()


def git(args: list[str]) -> str:
    return subprocess.run(
        ["git", *args], cwd=ROOT, check=True, capture_output=True, text=True
    ).stdout.strip()


def index_width(bound: int) -> int:
    # Exact mirror of Hex.Nat.indexWidth.
    return 2 * (bound // 6) + (1 if bound % 6 >= 2 else 0)


def plan(bound: int) -> tuple[int, int]:
    sqrt_bound = math.isqrt(bound)
    if sqrt_bound * sqrt_bound < bound:
        sqrt_bound += 1
    count = index_width(sqrt_bound + 1) - 1
    return sqrt_bound, max(1, (count + 7) // 8)


def extract_emission(output: str) -> str:
    if output.startswith("@[expose]\ndef primeTableBound"):
        return output
    marker = ": info: @[expose]\ndef primeTableBound"
    at = output.find(marker)
    if at < 0:
        raise RuntimeError(f"could not find generator emission in output:\n{output[-2000:]}")
    return "@[expose]\ndef primeTableBound" + output[at + len(marker):]


def run_command(command: list[str], timeout: float) -> tuple[str, float, int | None]:
    start = time.monotonic_ns()
    proc = subprocess.Popen(
        command, cwd=ROOT, text=True, stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT, start_new_session=True,
    )
    try:
        output, _ = proc.communicate(timeout=timeout)
    except subprocess.TimeoutExpired:
        os.killpg(os.getpgid(proc.pid), signal.SIGKILL)
        output, _ = proc.communicate()
        elapsed = time.monotonic_ns() - start
        return output, elapsed, None
    elapsed = time.monotonic_ns() - start
    return output, elapsed, proc.returncode


def one_sample(bound: int, timeout: float, directory: Path) -> tuple[dict, str | None]:
    sqrt_bound, batches = plan(bound)
    generator = directory / "Generate.lean"
    generator.write_text(
        "import HexPrimality.SieveElab\n"
        f"#rebuild_primeTable {bound} {sqrt_bound} {batches}\n"
    )
    output, generation_nanos, generation_code = run_command(
        ["lake", "env", "lean", str(generator)], timeout
    )
    if generation_code != 0:
        return ({
            "status": "generation-timeout" if generation_code is None else "generation-failed",
            "generation_wall_nanos": generation_nanos,
            "generation_exit_code": generation_code,
            "diagnostic_tail": output[-2000:],
        }, None)
    emission = extract_emission(output)
    replay = directory / "Replay.lean"
    replay.write_text(
        "module\n\n"
        "public import HexArith.Nat.Prime\n"
        "public import HexPrimality.Sieve\n"
        "public import HexBasic.ArrayDecEq\n\n"
        "public section\n\n"
        "namespace Hex.Nat\n"
        "set_option maxRecDepth 100000\n\n"
        + emission + "\nend Hex.Nat\n\n"
        "def main : IO Unit := do\n"
        "  let table := Hex.Nat.primeTable\n"
        "  let first := table[0]!\n"
        "  let last := table[table.size - 1]!\n"
        "  let checksum := table.foldl (fun acc n => acc + n) 0\n"
        "  IO.println s!\"{table.size},{first},{last},{checksum}\"\n"
    )
    olean = directory / "Replay.olean"
    c_source = directory / "Replay.c"
    replay_output, replay_nanos, replay_code = run_command(
        ["lake", "env", "lean", str(replay), "-o", str(olean),
         "-c", str(c_source)], timeout
    )
    source = replay.read_bytes()
    generated_c = c_source.read_bytes() if c_source.exists() else b""
    static_array_lengths = [int(value) for value in re.findall(
        rb"sizeof\(void\*\)\*([0-9]+)", generated_c
    )]
    # `lean_array_object` is a 24-byte header on this 64-bit runtime; this is
    # the exact expression assigned to its 16-bit `m_cs_sz` field in generated C.
    max_object_bytes = max(
        (24 + struct.calcsize("P") * length for length in static_array_lengths),
        default=0,
    )
    status = ("ok" if replay_code == 0 else
              "replay-timeout" if replay_code is None else "replay-failed")
    native_output, native_nanos, native_code = "", 0, None
    run_output, run_nanos, run_code = "", 0, None
    expected_readback = None
    if status == "ok":
        native_output, native_nanos, native_code = run_command(
            ["lake", "env", "leanc", "-c", str(c_source),
             "-o", str(directory / "Replay.o")], timeout
        )
        if native_code != 0:
            status = ("native-compile-timeout" if native_code is None else
                      "native-compile-failed")
    if status == "ok":
        literal = emission[emission.index("#[") : emission.index("]\n\n-- #rebuild")]
        values = [int(value) for value in re.findall(r"\d+", literal)]
        expected_readback = f"{len(values)},{values[0]},{values[-1]},{sum(values)}"
        run_output, run_nanos, run_code = run_command(
            ["lake", "env", "lean", "--run", str(replay)], timeout
        )
        if run_code != 0:
            status = "native-run-timeout" if run_code is None else "native-run-failed"
        elif expected_readback not in run_output.splitlines():
            status = "native-readback-mismatch"
    row = {
        "status": status,
        "generation_wall_nanos": generation_nanos,
        "replay_wall_nanos": replay_nanos,
        "source_bytes": len(source), "generated_c_bytes": len(generated_c),
        "max_runtime_object_bytes": max_object_bytes,
        "runtime_object_limit_bytes": 65535,
        "source_sha256": hashlib.sha256(source).hexdigest(),
        "replay_exit_code": replay_code,
        "native_compile_wall_nanos": native_nanos,
        "native_compile_exit_code": native_code,
        "native_compile_diagnostic_tail": native_output[-2000:],
        "native_run_wall_nanos": run_nanos,
        "native_run_exit_code": run_code,
        "native_run_output_tail": run_output[-2000:],
        "expected_native_readback": expected_readback,
    }
    if olean.exists():
        artifact = olean.read_bytes()
        row.update({"olean_bytes": len(artifact),
                    "olean_sha256": hashlib.sha256(artifact).hexdigest()})
    if replay_code != 0:
        row["diagnostic_tail"] = replay_output[-2000:]
    return row, emission


def summarize(record: dict) -> list[dict]:
    rows = []
    for candidate in record["candidates"]:
        samples = candidate["samples"]
        complete = [row for row in samples if row["status"] == "ok"]
        if not complete:
            generation = [row["generation_wall_nanos"] for row in samples]
            replay = [row["replay_wall_nanos"] for row in samples
                      if "replay_wall_nanos" in row]
            rows.append({
                "bound": candidate["bound"], "sqrt_bound": candidate["sqrt_bound"],
                "batches": candidate["batches"], "status": samples[-1]["status"],
                "sample_count": len(samples),
                "generation_median_nanos": statistics.median(generation),
                "replay_median_nanos": statistics.median(replay) if replay else None,
                "source_bytes": samples[-1].get("source_bytes"),
                "generated_c_bytes": samples[-1].get("generated_c_bytes"),
                "olean_bytes": samples[-1].get("olean_bytes"),
                "max_runtime_object_bytes": samples[-1].get("max_runtime_object_bytes"),
                "source_sha256": samples[-1].get("source_sha256"),
            })
            continue
        rows.append({
            "bound": candidate["bound"], "sqrt_bound": candidate["sqrt_bound"],
            "batches": candidate["batches"], "status": "ok",
            "sample_count": len(complete),
            "generation_median_nanos": statistics.median(
                row["generation_wall_nanos"] for row in complete),
            "replay_median_nanos": statistics.median(
                row["replay_wall_nanos"] for row in complete),
            "source_bytes": complete[0]["source_bytes"],
            "generated_c_bytes": complete[0]["generated_c_bytes"],
            "olean_bytes": complete[0]["olean_bytes"],
            "max_runtime_object_bytes": complete[0]["max_runtime_object_bytes"],
            "source_sha256": complete[0]["source_sha256"],
        })
    return rows


def print_report(record: dict) -> None:
    print("| bound | n | batches | generation | fresh replay | source | olean | max object |")
    print("|---:|---:|---:|---:|---:|---:|---:|---:|")
    for row in record.get("summary") or summarize(record):
        if row["status"] != "ok":
            size = "--" if row["source_bytes"] is None else f"{row['source_bytes'] / 1024:.1f} KiB"
            olean_size = ("--" if row["olean_bytes"] is None else
                          f"{row['olean_bytes'] / 1024:.1f} KiB")
            object_size = ("--" if row["max_runtime_object_bytes"] is None else
                           str(row["max_runtime_object_bytes"]))
            replay = ("not measured" if row["replay_median_nanos"] is None else
                      f"{row['replay_median_nanos'] / 1e9:.3f} s")
            print(
                f"| {row['bound']:,} | {row['sample_count']} | {row['batches']} | "
                f"{row['generation_median_nanos'] / 1e9:.3f} s | "
                f"{row['status']} ({replay}) | "
                f"{size} | {olean_size} | {object_size} |"
            )
            continue
        print(
            f"| {row['bound']:,} | {row['sample_count']} | {row['batches']} | "
            f"{row['generation_median_nanos'] / 1e9:.3f} s | "
            f"{row['replay_median_nanos'] / 1e9:.3f} s | "
            f"{row['source_bytes'] / 1024:.1f} KiB | "
            f"{row['olean_bytes'] / 1024:.1f} KiB | "
            f"{row['max_runtime_object_bytes']} |"
        )


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--bounds", default=",".join(map(str, DEFAULT_BOUNDS)))
    parser.add_argument("--samples", type=int, default=3)
    parser.add_argument("--timeout", type=float, default=300.0)
    parser.add_argument("--cpu", default="auto",
                        help="logical CPU to pin, or auto for an idle core")
    parser.add_argument("--output", type=Path)
    parser.add_argument("--report", type=Path)
    parser.add_argument("--allow-dirty", action="store_true")
    args = parser.parse_args()
    if args.report:
        record = json.loads(args.report.read_text())
        print_report(record)
        return 0
    if args.output is None:
        parser.error("--output is required unless --report is used")
    if args.samples < 1 or args.timeout <= 0:
        parser.error("--samples and --timeout must be positive")
    bounds = tuple(int(value) for value in args.bounds.split(","))
    if any(bound <= 3 for bound in bounds):
        parser.error("every bound must exceed 3")
    dirty = git(["status", "--porcelain", "--untracked-files=all"])
    if dirty and not args.allow_dirty:
        parser.error("worktree is dirty; commit first or use --allow-dirty for diagnostics")

    cpu = idle_core.resolve(args.cpu)
    idle_core.pin_self(cpu)
    state_before = host_state(cpu)
    subprocess.run(["lake", "build", "HexPrimality.SieveElab"], cwd=ROOT, check=True)
    candidates = []
    with tempfile.TemporaryDirectory(
        prefix="hex-primality-table-", dir=ROOT / ".lake"
    ) as tmp:
        tmpdir = Path(tmp)
        for bound in bounds:
            samples, expected = [], None
            for sample in range(args.samples):
                directory = tmpdir / f"b{bound}-s{sample}"
                directory.mkdir()
                row, emission = one_sample(bound, args.timeout, directory)
                if expected is not None and emission is not None and emission != expected:
                    raise RuntimeError(f"nondeterministic generator output at bound {bound}")
                if emission is not None:
                    expected = emission
                samples.append(row)
                if row["status"] != "ok":
                    # Compiler heartbeat failures and the per-command timeout are
                    # deterministic budget failures; repeating them adds no signal.
                    break
            sqrt_bound, batches = plan(bound)
            candidates.append({"bound": bound, "sqrt_bound": sqrt_bound,
                               "batches": batches, "samples": samples})
            print(f"measured bound {bound}", file=sys.stderr)
    record = {
        "schema": "hex-primality-table-policy/1",
        "measurement": "standard generator plus fresh emitted replay module",
        "environment": {
            "hostname": socket.gethostname(), "platform": platform.platform(),
            "python": platform.python_version(), "commit": git(["rev-parse", "HEAD"]),
            "dirty": bool(dirty), "dirty_status": dirty,
            "lean": lean_version(), "command": shlex.join(sys.argv),
            "state_before": state_before, "state_after": host_state(cpu),
        },
        "config": {"bounds": bounds, "samples": args.samples,
                   "timeout_seconds": args.timeout, "max_sieve_bases_per_batch": 8},
        "candidates": candidates,
    }
    record["summary"] = summarize(record)
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(record, indent=2, sort_keys=True) + "\n")
    print_report(record)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
