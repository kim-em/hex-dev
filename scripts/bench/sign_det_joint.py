#!/usr/bin/env python3
"""Validate literal inputs and finite dimensions of actual joint re-encoding tables."""
import argparse
import hashlib
import json
import math
import os
from pathlib import Path
import platform
from fractions import Fraction
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT))
from scripts.bench.sign_det_compare import archive_sources
from scripts.bench.sign_det_sparse import source_hashes
from scripts.bench.structural_tactic_sweep import acquire_cpu

DEGREES = [3, 7, 15, 31, 63]


def monomial(degree, coefficient):
    return [[0, 1]]*degree + [[coefficient, 1]]


def derivatives(degree):
    return [monomial(k, math.factorial(degree)//math.factorial(k))
            for k in reversed(range(degree))]


def inventory(words):
    """Candidate sizes follow complete child restrictions before solving."""
    arity = len(words[0])
    if arity <= 1:
        return 3, 3
    mid = arity//2
    left = [w[:mid] for w in words]
    right = [w[mid:] for w in words]
    size = len(set(map(tuple, left))) * len(set(map(tuple, right)))
    lslots, lmax = inventory(left)
    rslots, rmax = inventory(right)
    return size + lslots + rslots, max(size, lmax, rmax)


def expected(n, side):
    if type(n) is not int or n < 3 or n % 2 != 1 or side not in ("left", "right"):
        raise ValueError("invalid joint family parameter")
    source = monomial(n, 1)
    source[0] = [-1 if side == "left" else 1, 1]
    head = monomial(2*n, 1)
    head[0], head[-1] = [1, 2], [-1, 2]
    target = [monomial(k, -math.factorial(2*n)//(2*math.factorial(k)))
              for k in reversed(range(2*n))]
    queries = target + [source] + derivatives(n)
    if len({json.dumps(q) for q in queries}) != len(queries):
        raise ValueError("joint query polynomials are not distinct")
    # Exact evaluation at both known real roots of X^(2n)-1. No Tarski query.
    words = [[(v > 0)-(v < 0) for q in queries
              for v in [sum(Fraction(*c)*(x**k) for k, c in enumerate(q))]] for x in (1, -1)]
    table = [[w, 1] for w in words]
    slots, max_columns = inventory(words)
    s = 3*n+1
    return {"degree": n, "side": side, "context": 10377, "source": source,
            "sourceIndices": list(range(1, n+1)),
            "sourceSigns": [1]*n if side == "left" else [(-1)**(n-i) for i in range(1, n+1)],
            "head": head, "queries": queries, "table": table, "directTable": table,
            "order": "gt", "reducedQueryWitnessBits": (math.factorial(2*n)//2).bit_length(),
            "querySlots": slots, "maxColumns": max_columns, "maxSupport": 2,
            "treeNodes": 2*s-1, "graphNodes": 2*s-1, "graphEdges": 2*s-2}


RECORDED = {"maxInverseBits", "maxDenominatorBits",
            "directQueryWitnessBits", "reducedGraphBytes", "directGraphBytes"}


def validate(path, degrees=DEGREES):
    rows = [json.loads(line) for line in path.read_text().splitlines()]
    schedule = [(n, side) for n in degrees for side in ("left", "right")]
    if len(rows) != len(schedule):
        raise ValueError("missing joint observations")
    for row, (n, side) in zip(rows, schedule, strict=True):
        oracle = expected(n, side)
        if set(row) != set(oracle) | RECORDED:
            raise ValueError("changed joint observation fields")
        for key, value in oracle.items():
            if json.dumps(row[key]) != json.dumps(value):
                raise ValueError(f"joint literal or dimension differs: {key}")
        if any(type(row[k]) is not int or row[k] <= 0 for k in RECORDED):
            raise ValueError("invalid recorded bit or byte count")
    return len(rows)


def collect(output):
    """Retain the complete untimed inventory and its verified source closure."""
    revision = subprocess.check_output(["git", "rev-parse", "HEAD"], cwd=ROOT, text=True).strip()
    if subprocess.check_output(["git", "status", "--porcelain"], cwd=ROOT, text=True):
        raise ValueError("commit source changes before collecting the joint inventory")
    subprocess.run(["lake", "build", "--no-build", "hexsigndet_bench"], cwd=ROOT, check=True)
    executable = ROOT / ".lake/build/bin/hexsigndet_bench"
    output = output.resolve()
    output.mkdir(parents=True, exist_ok=False)
    cpu, lease = acquire_cpu()
    os.sched_setaffinity(0, {cpu})
    sources = source_hashes()
    for relative in ("scripts/bench/sign_det_joint.py", "scripts/bench/test_sign_det_joint.py",
                     "scripts/bench/sign_det_compare.py"):
        sources[relative] = hashlib.sha256((ROOT / relative).read_bytes()).hexdigest()
    metadata = {"schema": "hex-sign-det-joint-inventory-v1", "kind": "untimed-input-inventory",
                "scientific_timing_samples": 0, "revision": revision, "source_sha256": sources,
                "binary_sha256": hashlib.sha256(executable.read_bytes()).hexdigest(),
                "host": platform.node(), "platform": platform.platform(), "cpu": cpu,
                "affinity": sorted(os.sched_getaffinity(0)), "load_before": os.getloadavg(),
                "command": [str(executable), "inspect-joint"], "state": "running"}
    try:
        archive_sources(output, metadata)
        (output / "metadata.json").write_text(json.dumps(metadata, indent=2) + "\n")
        with (output / "inventory.jsonl").open("w") as stdout, (output / "stderr.log").open("w") as stderr:
            result = subprocess.run(metadata["command"], cwd=ROOT, stdout=stdout, stderr=stderr)
        metadata["exit_code"] = result.returncode
        metadata["load_after"] = os.getloadavg()
        metadata["inventory_sha256"] = hashlib.sha256((output / "inventory.jsonl").read_bytes()).hexdigest()
        result.check_returncode()
        metadata["validated_rows"] = validate(output / "inventory.jsonl")
        for relative, expected_hash in sources.items():
            if hashlib.sha256((ROOT / relative).read_bytes()).hexdigest() != expected_hash:
                raise ValueError("source changed during collection: " + relative)
        metadata["revision_after"] = subprocess.check_output(
            ["git", "rev-parse", "HEAD"], cwd=ROOT, text=True).strip()
        metadata["binary_sha256_after"] = hashlib.sha256(executable.read_bytes()).hexdigest()
        if (metadata["revision_after"] != revision or
                metadata["binary_sha256_after"] != metadata["binary_sha256"]):
            raise ValueError("source revision or executable changed during collection")
        metadata["state"] = "complete"
    except Exception as error:
        metadata["state"] = "failed"
        metadata["error"] = str(error)
        raise
    finally:
        (output / "metadata.json").write_text(json.dumps(metadata, indent=2) + "\n")
        lease.close()
    return metadata["validated_rows"]


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("inventory", type=Path, nargs="?")
    parser.add_argument("--collect", type=Path, help="collect the complete untimed inventory outside the source tree")
    parser.add_argument("--degree", type=int, action="append", help="validate an explicit development subset")
    args = parser.parse_args()
    if args.collect is not None:
        if args.inventory is not None or args.degree is not None:
            parser.error("--collect cannot be combined with an inventory or development subset")
        if args.collect.resolve().is_relative_to(ROOT):
            parser.error("collect outside the source tree")
        count = collect(args.collect)
    else:
        if args.inventory is None:
            parser.error("provide an inventory or --collect")
        count = validate(args.inventory, args.degree or DEGREES)
    print(f"{count} joint rows validated")
