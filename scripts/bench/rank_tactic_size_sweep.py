#!/usr/bin/env python3
"""Proof time against dimension for the `rank` tactic and Mathlib's `eval_rank`.

For each family (full rank, rank ``n - 2``, rank ``n / 2``, rank ``2``) and
each dimension, one seeded ``n × n`` integer literal with entries in
``[-9, 9]`` is proved by both tactics in a scratch file under
``set_option profiler true``, and the sum of the profiler's cumulative
categories (elaboration of the literal, tactic execution, interpretation of
tactic code, kernel type checking, linting) is recorded as the proof time,
with the kernel's ``type checking`` share kept separately; imports are not
counted. One sample per point. Dimensions grow
geometrically, since the growth is regular; a family stops for a tactic at
the first dimension whose proof time exceeds ``--cap`` seconds (default 10),
and no run is allowed more than the cap beyond the import baseline. The
record goes to
``reports/bench-results/hex-rank-mathlib-tactic-size-<sha>-<host>.json`` and
is plotted by ``scripts/plots/hex-rank-mathlib-tactic-size.py``.

Host activity is recorded as context, not filtered; pin with ``--cpu``.
"""

from __future__ import annotations

import argparse
import json
import os
import platform
import random
import socket
import subprocess
import sys
import tempfile
import time
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]

FAMILIES = {
    "full": ("full rank", lambda n: n),
    "deficient": ("rank n - 2", lambda n: n - 2),
    "half": ("rank n / 2", lambda n: n // 2),
    "low": ("rank 2", lambda n: 2),
}
SIZES = [8, 12, 16, 24, 32, 48, 64, 96, 128, 192, 256]
TOOLS = {
    "eval_rank": ("Mathlib.Tactic.NormRank", "eval_rank"),
    "rank": ("HexRankMathlib", "rank"),
}


def matrix(family: str, n: int, seed: int) -> list[list[int]]:
    rng = random.Random(seed * 1000003 + n)
    r = FAMILIES[family][1](n)
    if r == n:
        return [[rng.randint(-9, 9) for _ in range(n)] for _ in range(n)]
    left = [[rng.randint(-3, 3) for _ in range(r)] for _ in range(n)]
    right = [[rng.randint(-3, 3) for _ in range(n)] for _ in range(r)]
    return [[sum(left[i][k] * right[k][j] for k in range(r)) for j in range(n)]
            for i in range(n)]


def literal(m: list[list[int]]) -> str:
    return "!![" + "; ".join(", ".join(str(x) for x in row) for row in m) + "]"


def run_lean(path: Path, timeout: float, cpu: int | None) -> tuple[float | None, bool, dict[str, float]]:
    """Wall time, success, and the profiler's cumulative categories in seconds."""
    cmd = ["lake", "lean", str(path)]
    if cpu is not None:
        cmd = ["taskset", "-c", str(cpu)] + cmd
    start = time.monotonic()
    try:
        proc = subprocess.run(cmd, cwd=ROOT, capture_output=True, text=True, timeout=timeout)
    except subprocess.TimeoutExpired:
        return None, False, {}
    out = proc.stdout + proc.stderr
    profile: dict[str, float] = {}
    if "cumulative profiling times:" in out:
        for line in out.split("cumulative profiling times:", 1)[1].splitlines()[1:]:
            if not line.startswith("\t"):
                break
            name, value = line.strip().rsplit(" ", 1)
            profile[name] = float(value[:-2]) / 1000 if value.endswith("ms") else float(value[:-1])
    return time.monotonic() - start, proc.returncode == 0 and "error" not in out, profile


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__.split("\n", 1)[0])
    parser.add_argument("--cap", type=float, default=10.0,
                        help="stop a family at the first proof over this many seconds; no run may exceed it")
    parser.add_argument("--seed", type=int, default=2026)
    parser.add_argument("--cpu", type=int, help="logical CPU for the timed processes")
    parser.add_argument("--output", type=Path)
    args = parser.parse_args(argv)
    sha = subprocess.run(["git", "rev-parse", "--short=12", "HEAD"], cwd=ROOT,
                         capture_output=True, text=True, check=True).stdout.strip()
    host = socket.gethostname()
    output = args.output or ROOT / "reports" / "bench-results" / f"hex-rank-mathlib-tactic-size-{sha}-{host}.json"
    toolchain = (ROOT / "lean-toolchain").read_text().strip()
    points: list[dict[str, object]] = []
    with tempfile.TemporaryDirectory(prefix="rank-size-") as tmp:
        tmpdir = Path(tmp)
        baseline: dict[str, float] = {}
        for tool, (imp, _) in TOOLS.items():
            path = tmpdir / f"base_{tool}.lean"
            path.write_text(f"import {imp}\nexample : True := trivial\n")
            samples = [run_lean(path, 600.0, args.cpu)[0] for _ in range(2)]
            baseline[tool] = min(s for s in samples if s is not None)
            print(f"[baseline] {tool} {baseline[tool]:.2f}s", flush=True)
        for family in FAMILIES:
            stopped: set[str] = set()
            for n in SIZES:
                if len(stopped) == len(TOOLS):
                    break
                m = matrix(family, n, args.seed)
                r = FAMILIES[family][1](n)
                for tool, (imp, tactic) in TOOLS.items():
                    if tool in stopped:
                        continue
                    path = tmpdir / f"{family}_{n}_{tool}.lean"
                    path.write_text(f"import {imp}\nset_option maxRecDepth 100000\n"
                                    f"set_option maxHeartbeats 0\nset_option profiler true\n"
                                    f"set_option profiler.threshold 1000000\n"
                                    f"example : Matrix.rank (R := ℤ) {literal(m)} = {r} := by {tactic}\n")
                    wall, ok, profile = run_lean(path, baseline[tool] + args.cap + 1.0, args.cpu)
                    point: dict[str, object] = {"family": family, "n": n, "rank": r, "tool": tool}
                    if wall is None:
                        point.update({"status": "timeout"})
                        stopped.add(tool)
                    else:
                        proof = sum(profile.values())
                        point.update({"status": "ok" if ok else "failed", "wall_s": wall,
                                      "proof_s": proof, "kernel_s": profile.get("type checking", 0.0),
                                      "profile_s": profile})
                        if proof > args.cap or not ok:
                            stopped.add(tool)
                    points.append(point)
                    print(f"[point] {family} n={n} {tool} {point}", flush=True)
    record = {
        "schema": "hex-rank-mathlib-tactic-size-v1",
        "description": __doc__.strip(),
        "commit": sha,
        "host": host,
        "cpu_model": platform.processor() or None,
        "toolchain": toolchain,
        "seed": args.seed,
        "cap_s": args.cap,
        "cpu": args.cpu,
        "load_average_at_end": os.getloadavg(),
        "baseline_s": baseline,
        "families": {k: v[0] for k, v in FAMILIES.items()},
        "points": points,
    }
    output.parent.mkdir(parents=True, exist_ok=True)
    output.write_text(json.dumps(record, indent=2, sort_keys=True) + "\n")
    print(output)
    return 0


if __name__ == "__main__":
    sys.exit(main())
