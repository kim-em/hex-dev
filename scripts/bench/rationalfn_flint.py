#!/usr/bin/env python3
"""Informational persistent FLINT comparison; conversion is outside C timing.

Build rationalfn_flint.c against FLINT, then pass its executable and a fixture
file. No SymPy dependency: canonical output conversion uses Fraction only.
"""
import argparse
from collections import defaultdict
from fractions import Fraction
import hashlib
import json
from math import lcm
import os
from pathlib import Path
import platform
import statistics
import subprocess
import sys

OPS = {"normalize", "add", "sub", "mul", "div", "inv", "neg", "pow",
       "derivative", "equal", "eval"}
ROOT = Path(__file__).resolve().parents[2]


def git_state():
    """Identify the coordinator's checkout, independently of the caller's cwd."""
    git = lambda *args: subprocess.check_output(
        ["git", *args], cwd=ROOT, text=True).strip()
    return {"commit": git("rev-parse", "HEAD"),
            "git_dirty": bool(git("status", "--porcelain"))}


def integer_pair(pair):
    polys = [[Fraction(*c) for c in pair[key]] for key in ("num", "den")]
    scale = lcm(*(c.denominator for p in polys for c in p))
    return [[int(c * scale) for c in p] for p in polys]


def encode(pair):
    return " ".join(str(len(p)) + " " + " ".join(map(str, p)) for p in integer_pair(pair))


def decode(line):
    fields = iter(line.split())
    kind, elapsed = next(fields), next(fields)
    seconds = None if kind == "rejected" else float(elapsed)
    sizes = None
    if kind in {"none", "rejected"}:
        result = None
    elif kind == "bool":
        result = bool(int(next(fields)))
    elif kind == "value":
        result = [int(next(fields)), int(next(fields))]
    elif kind == "pair":
        polys = [[int(next(fields)) for _ in range(int(next(fields)))] for _ in range(2)]
        sizes = {"flint_lengths": list(map(len, polys)),
                 "flint_bits": [max((abs(c).bit_length() for c in p), default=0) for p in polys]}
        leading = polys[1][-1]
        canonical = [[Fraction(c, leading) for c in p] for p in polys]
        result = dict(zip(("num", "den"),
                          [[[c.numerator, c.denominator] for c in p] for p in canonical]))
        sizes["hex_lengths"] = list(map(len, canonical))
        sizes["hex_bits"] = [max((max(abs(c.numerator).bit_length(),
                                      c.denominator.bit_length()) for c in p), default=0)
                             for p in canonical]
    else:
        raise ValueError(f"bad driver response: {line}")
    if list(fields):
        raise ValueError("unexpected trailing driver output")
    return result, seconds, sizes


def main():
    # Controlled coefficient-height fixtures exceed Python's decimal-input
    # guard; these are local generated algebraic test inputs, not a web service.
    if hasattr(sys, "set_int_max_str_digits"):
        sys.set_int_max_str_digits(0)
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("driver")
    parser.add_argument("fixtures")
    parser.add_argument("--repeats", type=int, default=100)
    parser.add_argument("--rows", action="store_true", help="emit timings and both representation sizes")
    parser.add_argument("--json", action="store_true", help="emit one traceable JSON report")
    parser.add_argument("--trials", type=int, default=1)
    args = parser.parse_args()
    if not 1 <= args.repeats <= 1000000:
        parser.error("repeats must be between 1 and 1000000")
    if not 1 <= args.trials <= 100:
        parser.error("trials must be between 1 and 100")
    times = defaultdict(list)
    rows = []
    count = 0
    with subprocess.Popen([args.driver], stdin=subprocess.PIPE, stdout=subprocess.PIPE,
                          text=True, bufsize=1) as driver:
        try:
            with open(args.fixtures) as fixtures:
                for number, line in enumerate(fixtures, 1):
                    row = json.loads(line)
                    if row["domain"] != "QQ" or row["operation"] not in OPS:
                        continue
                    op = row["operation"]
                    operands = row["operands"]
                    a = operands[0]
                    b = operands[1] if len(operands) > 1 else {"num": [], "den": [[1, 1]]}
                    point = row.get("point", [0, 1])
                    request = (f"{op} {args.repeats} {row.get('exponent', 0)} "
                               f"{point[0]} {point[1]} {encode(a)} {encode(b)}\n")
                    samples = []
                    for _ in range(args.trials):
                        driver.stdin.write(request)
                        driver.stdin.flush()
                        response = driver.stdout.readline()
                        if not response:
                            raise RuntimeError(f"driver stopped at fixture {number}")
                        actual, seconds, sizes = decode(response)
                        if actual != row["expected"]:
                            raise AssertionError(f"fixture {number}: {actual} != {row['expected']}")
                        samples.append(seconds)
                        if seconds is not None:
                            times[op].append(seconds)
                    count += 1
                    result = {"fixture": number, "operation": op,
                              "intermediate_hex_sizes": row.get("intermediate_hex_sizes"),
                              "benchmark": row.get("benchmark"), "parameter": row.get("parameter"),
                              "seconds": seconds, "samples_seconds": samples, "sizes": sizes,
                              "input_hex_lengths": [[len(pair[k]) for k in ("num", "den")]
                                                    for pair in operands],
                              "input_flint_bits": [[max((abs(c).bit_length() for c in p), default=0)
                                                    for p in integer_pair(pair)] for pair in operands],
                              "input_hex_bits": [[max((max(abs(c[0]).bit_length(), c[1].bit_length())
                                                       for c in pair[k]), default=0)
                                                  for k in ("num", "den")] for pair in operands]}
                    rows.append(result)
                    if args.rows and not args.json:
                        print(json.dumps(result))
        finally:
            driver.stdin.close()
        if driver.wait() != 0:
            raise RuntimeError("FLINT driver failed")
    if not count:
        raise RuntimeError("no comparable fixtures")
    if args.json:
        digest = lambda path: hashlib.sha256(Path(path).read_bytes()).hexdigest()
        print(json.dumps({"rows": rows, "checked_cases": count, "repeats": args.repeats,
                          "trials": args.trials, "host": platform.node(),
                          "platform": platform.platform(),
                          "cpu_affinity": sorted(os.sched_getaffinity(0))
                          if hasattr(os, "sched_getaffinity") else None,
                          **git_state(),
                          "driver_sha256": digest(args.driver), "fixtures_sha256": digest(args.fixtures),
                          "coordinator_sha256": digest(__file__),
                          "driver_source_sha256": digest(Path(__file__).with_suffix(".c"))}, indent=2))
        return
    print(f"PASS: {count} full QQ results agree with FLINT")
    for op, samples in sorted(times.items()):
        print(f"{op}: {len(samples)} cases, median {statistics.median(samples) * 1e6:.3f} us")


if __name__ == "__main__":
    main()
