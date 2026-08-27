#!/usr/bin/env python3
"""Controlled crossover measurement for HexPrimality decision dispatch.

The native probe times inside one process, after an untimed warmup, so process
startup is excluded.  This runner alternates the trial and bounded-certificate
arms in AB/BA blocks, retains every raw timing, and checks both answers with an
independent deterministic Miller--Rabin implementation valid below ``2^64``.

Scientific run::

    python3 scripts/bench/primality_policy_sweep.py \
      --rounds 8 --repeats 200 \
      --output reports/bench-results/hex-primality-policy-issue-9757-chungus2.json

The default ladder includes fixed primes, balanced semiprimes, and adversarial
Cunningham-chain primes spanning both observed crossovers. ``--report FILE``
reproduces the summary without measuring.
"""

from __future__ import annotations

import argparse
import json
import os
import platform
from pathlib import Path
import shlex
import socket
import statistics
import subprocess
import sys

try:
    import idle_core
except ModuleNotFoundError:  # imported as ``scripts.bench.*`` by unit tests
    from scripts.bench import idle_core


ROOT = Path(__file__).resolve().parents[2]
PROBE = ROOT / ".lake" / "build" / "bin" / "hexprimality_policy_probe"
CASES = (
    ("prime-10k", 10_007, True, "fixed-prime"),
    ("semiprime-10k", 10_403, False, "balanced-semiprime"),       # 101 * 103
    ("prime-15k", 15_013, True, "fixed-prime"),
    ("semiprime-15k", 14_351, False, "balanced-semiprime"),       # 113 * 127
    ("prime-20k", 20_011, True, "fixed-prime"),
    ("semiprime-20k", 20_711, False, "balanced-semiprime"),       # 139 * 149
    ("prime-30k", 30_011, True, "fixed-prime"),
    ("semiprime-30k", 29_893, False, "balanced-semiprime"),       # 167 * 179
    ("prime-50k", 50_021, True, "fixed-prime"),
    ("semiprime-50k", 47_897, False, "balanced-semiprime"),       # 211 * 227
    ("prime-70k", 70_001, True, "fixed-prime"),
    ("semiprime-70k", 70_747, False, "balanced-semiprime"),       # 263 * 269
    ("prime-100k", 100_003, True, "fixed-prime"),
    ("semiprime-100k", 99_221, False, "balanced-semiprime"),      # 313 * 317
    ("prime-150k", 150_001, True, "fixed-prime"),
    ("semiprime-150k", 148_987, False, "balanced-semiprime"),     # 383 * 389
    ("prime-300k", 300_007, True, "fixed-prime"),
    ("semiprime-300k", 301_337, False, "balanced-semiprime"),     # 541 * 557
    ("prime-1m", 1_000_003, True, "fixed-prime"),
    ("prime-chain4-1m", 1_014_719, True, "cunningham-chain"),
    ("semiprime-1m", 1_005_973, False, "balanced-semiprime"),     # 997 * 1009
    ("prime-3m", 3_000_017, True, "fixed-prime"),
    ("semiprime-3m", 2_999_743, False, "balanced-semiprime"),     # 1723 * 1741
    ("prime-10m", 10_000_019, True, "fixed-prime"),
    ("prime-chain3-10m", 10_050_959, True, "cunningham-chain"),
    ("semiprime-10m", 10_001_653, False, "balanced-semiprime"),   # 3109 * 3217
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


def host_state(cpu: int) -> dict:
    model = "unknown"
    try:
        for block in Path("/proc/cpuinfo").read_text().split("\n\n"):
            fields = dict(line.split(":", 1) for line in block.splitlines()
                          if ":" in line)
            if fields.get("processor", "").strip() == str(cpu):
                model = fields.get("model name", "unknown").strip()
                break
    except OSError:
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
            "family": case["family"],
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
    parser.add_argument("--rounds", type=int, default=8)
    parser.add_argument("--repeats", type=int, default=200)
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
    if args.rounds < 6 or args.rounds % 2 != 0 or args.repeats < 1:
        parser.error("--rounds must be even and at least 6; repeats must be positive")
    dirty = git(["status", "--porcelain", "--untracked-files=all"])
    if dirty and not args.allow_dirty:
        parser.error("worktree is dirty; commit first or use --allow-dirty for diagnostics")

    cpu = idle_core.resolve(args.cpu)
    idle_core.pin_self(cpu)
    state_before = host_state(cpu)
    subprocess.run(["lake", "build", "hexprimality_policy_probe"], cwd=ROOT, check=True)
    cases = []
    for name, n, expected, family in CASES:
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
        cases.append({"name": name, "n": n, "prime": expected,
                      "family": family, "blocks": blocks})
        print(f"measured {name}", file=sys.stderr)

    record = {
        "schema": "hex-primality-decision-policy/1",
        "measurement": "warm in-process wall time; counterbalanced process order",
        "oracle": "deterministic Miller-Rabin bases for unsigned 64-bit integers",
        "environment": {
            "hostname": socket.gethostname(), "platform": platform.platform(),
            "python": platform.python_version(), "commit": git(["rev-parse", "HEAD"]),
            "dirty": bool(dirty), "dirty_status": dirty,
            "lean": lean_version(), "command": shlex.join(sys.argv),
            "state_before": state_before, "state_after": host_state(cpu),
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
