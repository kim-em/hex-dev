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
        checked += 1
    for path in args.samples:
        for sample in read_jsonl(path):
            if sample.get("type") == "sample":
                check_divisor(sample)
                checked += 1
    print(f"checked {checked} corpus and native-sample divisor records")


if __name__ == "__main__":
    main()
