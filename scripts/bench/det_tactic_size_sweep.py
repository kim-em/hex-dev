#!/usr/bin/env python3
"""Proof time against dimension for the `det` tactic and Mathlib's `eval_det`.

For each family (dense 8-bit entries, singular of rank ``n - 1``, dense
64-bit entries) and each dimension, one seeded ``n × n`` integer literal is
proved by both tactics in a scratch file under ``set_option profiler true``,
and the sum of the profiler's cumulative categories (elaboration of the
literal, tactic execution, interpretation of tactic code, kernel type
checking, linting) is recorded as the proof time, with the kernel's ``type
checking`` share kept separately; imports are not counted. Each point is
the median of ``--samples`` runs (default 3), the samples kept in the
record. A family stops for a tactic at the first dimension whose median
exceeds ``--cap`` seconds (default 10), and no run is allowed more than the
cap beyond the import baseline. The record goes to
``reports/bench-results/hex-bareiss-mathlib-tactic-size-<sha>-<host>.json``.

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
from fractions import Fraction
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]

FAMILIES = {
    "dense": "dense, 8-bit entries",
    "singular": "singular, rank n - 1",
    "large": "dense, 64-bit entries",
}
SIZES = {
    "dense": [4, 6, 8, 10, 12, 14, 16, 20, 24, 28, 32, 40, 48],
    "singular": [4, 6, 8, 10, 12, 14, 16, 20, 24, 28, 32, 40, 48],
    "large": [4, 6, 8, 10, 12, 14, 16, 20, 24],
}
TOOLS = {
    "eval_det": ("Mathlib.Tactic.NormDet", "eval_det"),
    "det": ("HexBareissMathlib", "det"),
}


def matrix(family: str, n: int, seed: int) -> list[list[int]]:
    rng = random.Random(seed * 1000003 + n)
    if family == "dense":
        return [[rng.randint(-128, 127) for _ in range(n)] for _ in range(n)]
    if family == "large":
        return [[rng.randint(-(1 << 63), (1 << 63) - 1) for _ in range(n)] for _ in range(n)]
    left = [[rng.randint(-9, 9) for _ in range(n - 1)] for _ in range(n)]
    right = [[rng.randint(-9, 9) for _ in range(n)] for _ in range(n - 1)]
    return [[sum(left[i][k] * right[k][j] for k in range(n - 1)) for j in range(n)]
            for i in range(n)]


def det(m: list[list[int]]) -> int:
    n = len(m)
    a = [[Fraction(x) for x in row] for row in m]
    d = Fraction(1)
    for c in range(n):
        p = next((r for r in range(c, n) if a[r][c] != 0), None)
        if p is None:
            return 0
        if p != c:
            a[c], a[p] = a[p], a[c]
            d = -d
        d *= a[c][c]
        for r in range(c + 1, n):
            f = a[r][c] / a[c][c]
            a[r] = [x - f * y for x, y in zip(a[r], a[c])]
    assert d.denominator == 1
    return d.numerator


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
                        help="stop a family at the first median over this many seconds; no run may exceed it")
    parser.add_argument("--samples", type=int, default=3, help="runs per point; the median is reported")
    parser.add_argument("--seed", type=int, default=2026)
    parser.add_argument("--cpu", type=int, help="logical CPU for the timed processes")
    parser.add_argument("--output", type=Path)
    args = parser.parse_args(argv)
    sha = subprocess.run(["git", "rev-parse", "--short=12", "HEAD"], cwd=ROOT,
                         capture_output=True, text=True, check=True).stdout.strip()
    host = socket.gethostname()
    output = args.output or ROOT / "reports" / "bench-results" / f"hex-bareiss-mathlib-tactic-size-{sha}-{host}.json"
    toolchain = (ROOT / "lean-toolchain").read_text().strip()
    points: list[dict[str, object]] = []
    with tempfile.TemporaryDirectory(prefix="det-size-") as tmp:
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
            for n in SIZES[family]:
                if len(stopped) == len(TOOLS):
                    break
                m = matrix(family, n, args.seed)
                d = det(m)
                for tool, (imp, tactic) in TOOLS.items():
                    if tool in stopped:
                        continue
                    path = tmpdir / f"{family}_{n}_{tool}.lean"
                    path.write_text(f"import {imp}\nset_option maxRecDepth 100000\n"
                                    f"set_option maxHeartbeats 0\nset_option profiler true\n"
                                    f"set_option profiler.threshold 1000000\n"
                                    f"example : Matrix.det (R := ℤ) {literal(m)} = {d} := by {tactic}\n")
                    point: dict[str, object] = {"family": family, "n": n, "tool": tool}
                    samples: list[dict[str, object]] = []
                    for _ in range(args.samples):
                        wall, ok, profile = run_lean(path, baseline[tool] + args.cap + 1.0, args.cpu)
                        if wall is None:
                            samples.append({"status": "timeout"})
                            break
                        samples.append({"status": "ok" if ok else "failed", "wall_s": wall,
                                        "proof_s": sum(profile.values()),
                                        "kernel_s": profile.get("type checking", 0.0),
                                        "profile_s": profile})
                        if not ok:
                            break
                    point["samples"] = samples
                    if all(sample["status"] == "ok" for sample in samples):
                        proofs = sorted(float(sample["proof_s"]) for sample in samples)
                        kernels = sorted(float(sample["kernel_s"]) for sample in samples)
                        point.update({"status": "ok", "proof_s": proofs[len(proofs) // 2],
                                      "kernel_s": kernels[len(kernels) // 2],
                                      "proof_min_s": proofs[0], "proof_max_s": proofs[-1]})
                        if point["proof_s"] > args.cap:
                            stopped.add(tool)
                    else:
                        point["status"] = samples[-1]["status"]
                        stopped.add(tool)
                    points.append(point)
                    print(f"[point] {family} n={n} {tool} {point}", flush=True)
    record = {
        "schema": "hex-bareiss-mathlib-tactic-size-v1",
        "description": __doc__.strip(),
        "commit": sha,
        "host": host,
        "cpu_model": platform.processor() or None,
        "toolchain": toolchain,
        "seed": args.seed,
        "cap_s": args.cap,
        "samples_per_point": args.samples,
        "cpu": args.cpu,
        "load_average_at_end": os.getloadavg(),
        "baseline_s": baseline,
        "families": FAMILIES,
        "points": points,
    }
    output.parent.mkdir(parents=True, exist_ok=True)
    output.write_text(json.dumps(record, indent=2, sort_keys=True) + "\n")
    print(output)
    return 0


if __name__ == "__main__":
    sys.exit(main())
