#!/usr/bin/env python3
"""Controlled crossover measurement for HexPrimality decision dispatch.

The native probe times inside one process, after an untimed warmup, so process
startup is excluded.  This runner alternates the trial and bounded-certificate
arms in AB/BA blocks, retains every raw timing, and checks both answers with an
independent deterministic Miller--Rabin implementation valid below ``2^64``.

Scientific run::

    python3 scripts/bench/primality_policy_sweep.py \
      --rounds 7 --repeats 200 --output reports/bench-results/hex-primality-policy.json

The default ladder deliberately includes a prime and a hard semiprime near each
magnitude.  ``--report FILE`` reproduces the summary without measuring.
"""

from __future__ import annotations

import argparse
import json
import platform
from pathlib import Path
import socket
import statistics
import subprocess
import sys


ROOT = Path(__file__).resolve().parents[2]
PROBE = ROOT / ".lake" / "build" / "bin" / "hexprimality_policy_probe"
CASES = (
    ("prime-10k", 10_007, True),
    ("semiprime-10k", 10_403, False),       # 101 * 103
    ("prime-15k", 15_013, True),
    ("semiprime-15k", 14_351, False),       # 113 * 127
    ("prime-20k", 20_011, True),
    ("semiprime-20k", 20_711, False),       # 139 * 149
    ("prime-30k", 30_011, True),
    ("semiprime-30k", 29_893, False),       # 167 * 179
    ("prime-50k", 50_021, True),
    ("semiprime-50k", 47_897, False),       # 211 * 227
    ("prime-70k", 70_001, True),
    ("semiprime-70k", 70_747, False),       # 263 * 269
    ("prime-100k", 100_003, True),
    ("semiprime-100k", 99_221, False),      # 313 * 317
    ("prime-150k", 150_001, True),
    ("semiprime-150k", 148_987, False),     # 383 * 389
    ("prime-300k", 300_007, True),
    ("semiprime-300k", 301_337, False),     # 541 * 557
    ("prime-1m", 1_000_003, True),
    ("semiprime-1m", 1_005_973, False),     # 997 * 1009
)
MR_BASES_64 = (2, 325, 9375, 28178, 450775, 9780504, 1795265022)


def is_prime_64(n: int) -> bool:
    """Independent deterministic Miller--Rabin oracle for ``n < 2^64``."""
    if n < 2:
        return False
    for p in (2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37):
        if n % p == 0:
            return n == p
    d, s = n - 1, 0
    while d % 2 == 0:
        d //= 2
        s += 1
    for base in MR_BASES_64:
        if base % n == 0:
            continue
        x = pow(base, d, n)
        if x in (1, n - 1):
            continue
        for _ in range(s - 1):
            x = x * x % n
            if x == n - 1:
                break
        else:
            return False
    return True


def git(args: list[str]) -> str:
    return subprocess.run(
        ["git", *args], cwd=ROOT, check=True, capture_output=True, text=True
    ).stdout.strip()


def run_arm(route: str, n: int, repeats: int) -> dict:
    proc = subprocess.run(
        [str(PROBE), route, str(n), str(repeats)], cwd=ROOT,
        check=True, capture_output=True, text=True,
    )
    row = json.loads(proc.stdout)
    row["per_call_nanos"] = row["total_nanos"] / repeats
    return row


def summarize(record: dict) -> list[dict]:
    rows = []
    for case in record["cases"]:
        arms = {}
        for route in ("trial", "certificate"):
            samples = [block[route]["per_call_nanos"] for block in case["blocks"]]
            arms[route] = {
                "samples_nanos": samples,
                "median_nanos": statistics.median(samples),
                "min_nanos": min(samples),
                "max_nanos": max(samples),
            }
        rows.append({
            "name": case["name"], "n": case["n"], "prime": case["prime"],
            "trial": arms["trial"], "certificate": arms["certificate"],
            "certificate_over_trial": (
                arms["certificate"]["median_nanos"] / arms["trial"]["median_nanos"]
            ),
        })
    return rows


def print_report(record: dict) -> None:
    print("| case | n | trial | certificate | cert / trial |")
    print("|---|---:|---:|---:|---:|")
    for row in record.get("summary") or summarize(record):
        print(
            f"| {row['name']} | {row['n']} | {row['trial']['median_nanos'] / 1e3:.2f} us | "
            f"{row['certificate']['median_nanos'] / 1e3:.2f} us | "
            f"{row['certificate_over_trial']:.3f}x |"
        )


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--rounds", type=int, default=7)
    parser.add_argument("--repeats", type=int, default=200)
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
    if args.rounds < 3 or args.repeats < 1:
        parser.error("--rounds must be at least 3 and --repeats must be positive")
    dirty = git(["status", "--porcelain", "--untracked-files=all"])
    if dirty and not args.allow_dirty:
        parser.error("worktree is dirty; commit first or use --allow-dirty for diagnostics")

    subprocess.run(["lake", "build", "hexprimality_policy_probe"], cwd=ROOT, check=True)
    cases = []
    for name, n, expected in CASES:
        oracle = is_prime_64(n)
        if oracle != expected:
            raise RuntimeError(f"bad committed classification for {name}: {n}")
        blocks = []
        for block in range(args.rounds):
            order = ("trial", "certificate") if block % 2 == 0 else ("certificate", "trial")
            measured = {route: run_arm(route, n, args.repeats) for route in order}
            want = args.repeats if expected else 0
            if any(measured[route]["checksum"] != want for route in order):
                raise RuntimeError(f"Hex routes disagree with independent oracle at {n}")
            blocks.append({"order": "AB" if block % 2 == 0 else "BA", **measured})
        cases.append({"name": name, "n": n, "prime": expected, "blocks": blocks})
        print(f"measured {name}", file=sys.stderr)

    record = {
        "schema": "hex-primality-decision-policy/1",
        "measurement": "warm in-process wall time; counterbalanced process order",
        "oracle": "deterministic Miller-Rabin bases for unsigned 64-bit integers",
        "environment": {
            "hostname": socket.gethostname(), "platform": platform.platform(),
            "python": platform.python_version(), "commit": git(["rev-parse", "HEAD"]),
            "dirty": bool(dirty), "dirty_status": dirty,
        },
        "config": {"rounds": args.rounds, "repeats": args.repeats,
                   "block_orders": ["AB" if i % 2 == 0 else "BA"
                                    for i in range(args.rounds)]},
        "cases": cases,
    }
    record["summary"] = summarize(record)
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(record, indent=2, sort_keys=True) + "\n")
    print_report(record)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
