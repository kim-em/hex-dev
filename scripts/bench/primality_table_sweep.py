#!/usr/bin/env python3
"""Generate and fresh-elaborate candidate HexPrimality prime tables.

Each sample invokes the standard ``#rebuild_primeTable`` generator, checks that
its emitted source is byte-identical to the other samples for that bound, then
fresh-elaborates the emitted replay module and records source/olean size and raw
wall times.  Candidate batches retain the committed table's maximum of eight
sieve bases per kernel-replayed chunk.

Scientific run::

    python3 scripts/bench/primality_table_sweep.py --samples 3 \
      --output reports/bench-results/hex-primality-table.json

``--report FILE`` reproduces the summary without measuring.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import math
import platform
from pathlib import Path
import re
import socket
import statistics
import struct
import subprocess
import sys
import tempfile
import time


ROOT = Path(__file__).resolve().parents[2]
DEFAULT_BOUNDS = (10_000, 100_000, 1_000_000, 10_000_000)


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
    try:
        proc = subprocess.run(
            command, cwd=ROOT, text=True, capture_output=True, timeout=timeout,
        )
    except subprocess.TimeoutExpired as error:
        elapsed = time.monotonic_ns() - start
        output = (error.stdout or "") + (error.stderr or "")
        if isinstance(output, bytes):
            output = output.decode(errors="replace")
        return output, elapsed, None
    elapsed = time.monotonic_ns() - start
    return proc.stdout + proc.stderr, elapsed, proc.returncode


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
        "import HexArith.Nat.Prime\n"
        "import HexPrimality.Sieve\n"
        "import HexBasic.ArrayDecEq\n"
        "namespace Hex.Nat\n"
        "set_option maxRecDepth 100000\n\n"
        + emission + "\nend Hex.Nat\n"
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
    if status == "ok" and max_object_bytes > 65535:
        status = "native-object-too-large"
    row = {
        "status": status,
        "generation_wall_nanos": generation_nanos,
        "replay_wall_nanos": replay_nanos,
        "source_bytes": len(source), "generated_c_bytes": len(generated_c),
        "max_runtime_object_bytes": max_object_bytes,
        "runtime_object_limit_bytes": 65535,
        "source_sha256": hashlib.sha256(source).hexdigest(),
        "replay_exit_code": replay_code,
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
            rows.append({
                "bound": candidate["bound"], "sqrt_bound": candidate["sqrt_bound"],
                "batches": candidate["batches"], "status": samples[-1]["status"],
                "generation_median_nanos": statistics.median(
                    row["generation_wall_nanos"] for row in samples),
                "replay_median_nanos": statistics.median(
                    row.get("replay_wall_nanos", 0) for row in samples),
                "source_bytes": samples[-1].get("source_bytes"),
                "olean_bytes": samples[-1].get("olean_bytes"),
                "max_runtime_object_bytes": samples[-1].get("max_runtime_object_bytes"),
                "source_sha256": samples[-1].get("source_sha256"),
            })
            continue
        rows.append({
            "bound": candidate["bound"], "sqrt_bound": candidate["sqrt_bound"],
            "batches": candidate["batches"], "status": "ok",
            "generation_median_nanos": statistics.median(
                row["generation_wall_nanos"] for row in complete),
            "replay_median_nanos": statistics.median(
                row["replay_wall_nanos"] for row in complete),
            "source_bytes": complete[0]["source_bytes"],
            "olean_bytes": complete[0]["olean_bytes"],
            "max_runtime_object_bytes": complete[0]["max_runtime_object_bytes"],
            "source_sha256": complete[0]["source_sha256"],
        })
    return rows


def print_report(record: dict) -> None:
    print("| bound | batches | generation | fresh replay | source | olean | max object |")
    print("|---:|---:|---:|---:|---:|---:|---:|")
    for row in record.get("summary") or summarize(record):
        if row["status"] != "ok":
            size = "--" if row["source_bytes"] is None else f"{row['source_bytes'] / 1024:.1f} KiB"
            olean_size = ("--" if row["olean_bytes"] is None else
                          f"{row['olean_bytes'] / 1024:.1f} KiB")
            object_size = ("--" if row["max_runtime_object_bytes"] is None else
                           str(row["max_runtime_object_bytes"]))
            print(
                f"| {row['bound']:,} | {row['batches']} | "
                f"{row['generation_median_nanos'] / 1e9:.3f} s | "
                f"{row['status']} ({row['replay_median_nanos'] / 1e9:.3f} s) | "
                f"{size} | {olean_size} | {object_size} |"
            )
            continue
        print(
            f"| {row['bound']:,} | {row['batches']} | "
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
