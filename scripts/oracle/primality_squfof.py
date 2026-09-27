#!/usr/bin/env python3
"""Independent integer-division oracle for the compiled SQUFOF splitter."""

from __future__ import annotations

import argparse
import json
import subprocess
from pathlib import Path


def prime64(n: int) -> bool:
    if n < 2:
        return False
    for p in (2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37):
        if n % p == 0:
            return n == p
    d = n - 1
    s = 0
    while d % 2 == 0:
        d //= 2
        s += 1
    # Deterministic Miller--Rabin bases for unsigned 64-bit inputs.
    for a in (2, 325, 9375, 28178, 450775, 9780504, 1795265022):
        if a % n == 0:
            continue
        x = pow(a, d, n)
        if x in (1, n - 1):
            continue
        for _ in range(s - 1):
            x = x * x % n
            if x == n - 1:
                break
        else:
            return False
    return True


def check_divisor(sample: dict) -> None:
    n = int(sample["n"])
    d = int(sample["divisor"])
    if sample["status"] == "factor":
        assert 1 < d < n and n % d == 0, sample
    else:
        assert d == 0, sample
    if sample.get("arm") in ("squfof", "reverse"):
        assert sample["attempts"] <= min(sample["multipliers"], 16), sample
        assert sample["steps"] <= sample["attempts"] * sample["stepCap"], sample
        assert sample["peakQueue"] <= sample["queueCapacity"], sample
        if "attemptsDetail" in sample:
            details = sample["attemptsDetail"]
            assert len(details) == sample["attempts"], sample
            assert sum(a["steps"] for a in details) == sample["steps"], sample
            assert max((a["peakQueue"] for a in details), default=0) == sample["peakQueue"], sample
            assert all(a["steps"] == a["forwardSteps"] + a["reverseSteps"] for a in details), sample
            assert all(a["steps"] + a["remaining"] == sample["stepCap"]
                       for a in details if a["steps"] > 0), sample
            assert all(not a["stop"].endswith("arithmetic") for a in details), sample


def read_jsonl(path: Path) -> list[dict]:
    return [json.loads(line) for line in path.read_text().splitlines() if line]


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--exe", type=Path, default=Path(".lake/build/bin/hexprimality_squfof_measure"))
    parser.add_argument("--corpus", type=Path, default=Path("conformance-fixtures/HexPrimality/squfof-corpus.jsonl"))
    parser.add_argument("--samples", type=Path, action="append", default=[])
    args = parser.parse_args()
    corpus = read_jsonl(args.corpus)
    checked = 0
    default_completed = 0
    for row in corpus:
        n = row["n"]
        if "p" in row:
            assert row["p"] * row["q"] == n, row
        if row["kind"] == "semiprime":
            assert prime64(row["p"]) and prime64(row["q"]), row
        command = [str(args.exe), str(n), "squfof", "262144", "16", "128", "1", "8", "262144"]
        sample = json.loads(subprocess.check_output(command, text=True))
        check_divisor(sample)
        if row["kind"] in ("semiprime", "trace"):
            assert sample["status"] == "factor", (row, sample)
        if row["kind"] == "prime":
            assert sample["status"] != "factor", (row, sample)
            assert prime64(n), row
        default = json.loads(subprocess.check_output(
            [str(args.exe), str(n), "squfof", "65536", "16", "128", "1", "8", "262144"],
            text=True))
        check_divisor(default)
        if row["kind"] == "semiprime":
            default_completed += default["status"] == "factor"
        diagnosis = json.loads(subprocess.check_output(
            [str(args.exe), str(n), "diagnose", "65536", "16", "128", "1", "8", "262144"],
            text=True))
        assert len(diagnosis["attemptsDetail"]) == 16, (row, diagnosis)
        assert all(not a["stop"].endswith("arithmetic") for a in diagnosis["attemptsDetail"]), (row, diagnosis)
        assert all(a["steps"] == a["forwardSteps"] + a["reverseSteps"]
                   and a["steps"] <= 65536 and a["peakQueue"] <= 128
                   for a in diagnosis["attemptsDetail"]), (row, diagnosis)
        checked += 1
    for path in args.samples:
        for sample in read_jsonl(path):
            if sample.get("type") == "sample":
                check_divisor(sample)
                checked += 1
    semiprimes = sum(row["kind"] == "semiprime" for row in corpus)
    print(f"checked {checked} corpus and native-sample divisor records; "
          f"default-cap completion {default_completed}/{semiprimes} semiprimes; "
          f"all {len(corpus) * 16} multiplier diagnostics without arithmetic stops")


if __name__ == "__main__":
    main()
