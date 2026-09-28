#!/usr/bin/env python3
"""Collect an untimed maximal-support input inventory with verified source provenance.

This records no scientific timings and supplies no Phase-4 scaling verdict.
Every completed command output is retained, including failures.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import os
from pathlib import Path
import platform
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT))
from scripts.bench.sign_det_compare import archive_sources
from scripts.bench.sign_det_sparse import source_hashes
from scripts.bench.structural_tactic_sweep import acquire_cpu

PARAMS = (1, 2, 3)


def validate_inventory(path):
    rows = [json.loads(line) for line in path.read_text().splitlines()]
    if [row.get("queries") for row in rows] != list(PARAMS):
        raise ValueError("missing, extra or reordered maximal-support inputs")
    for row, queries in zip(rows, PARAMS, strict=True):
        roots = 3**queries
        expected = {"family": "maximal-ternary-support", "queries": queries,
                    "rootCount": roots, "realizedSupport": roots,
                    "headDegree": roots, "maxColumns": roots,
                    "treeNodes": 2*queries-1, "graphNodes": 2*queries-1,
                    "graphEdges": 2*(queries-1)}
        if any(row.get(key) != value for key, value in expected.items()):
            raise ValueError("wrong maximal-support dimensions at query count " + str(queries))
        for key in ("headDegree", "queryDegree", "headCoefficientBits",
                    "queryCoefficientBits", "remainderCoefficientBits", "querySlots",
                    "rootCount", "realizedSupport", "maxColumns", "treeNodes",
                    "graphNodes", "graphEdges", "queries"):
            if type(row.get(key)) is not int or row[key] < 0:
                raise ValueError("invalid inventory size: " + key)
        for key in ("inputHash", "tableHash"):
            if type(row.get(key)) is not int or not 0 <= row[key] < 2**64:
                raise ValueError("invalid inventory hash: " + key)
    return rows


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    status = subprocess.check_output(["git", "status", "--porcelain"], cwd=ROOT, text=True)
    if status:
        raise ValueError("commit source changes before collecting an archived inventory")
    executable = ROOT / ".lake/build/bin/hexsigndet_bench"
    if not executable.exists():
        raise ValueError("build hexsigndet_bench first")
    out = args.output.resolve()
    out.mkdir(parents=True, exist_ok=False)
    cpu, lease = acquire_cpu()
    os.sched_setaffinity(0, {cpu})
    sources = source_hashes()
    for relative in ("scripts/bench/sign_det_maximal.py", "scripts/bench/sign_det_compare.py"):
        sources[relative] = hashlib.sha256((ROOT / relative).read_bytes()).hexdigest()
    metadata = {"schema": "hex-sign-det-maximal-inventory-v1",
                "kind": "untimed-input-inventory", "scientific_timing_samples": 0,
                "revision": subprocess.check_output(["git", "rev-parse", "HEAD"], cwd=ROOT, text=True).strip(),
                "source_sha256": sources,
                "binary_sha256": hashlib.sha256(executable.read_bytes()).hexdigest(),
                "host": platform.node(), "platform": platform.platform(),
                "cpu": cpu, "affinity": sorted(os.sched_getaffinity(0)),
                "load_start": os.getloadavg(),
                "command": [str(executable), "inspect-maximal"], "state": "running"}
    record = out / "metadata.json"
    try:
        archive_sources(out, metadata)
        record.write_text(json.dumps(metadata, indent=2) + "\n")
        with (out / "inventory.jsonl").open("w") as stdout, (out / "stderr.log").open("w") as stderr:
            result = subprocess.run(metadata["command"], cwd=ROOT, stdout=stdout, stderr=stderr)
        metadata["exit_code"] = result.returncode
        metadata["load_after"] = os.getloadavg()
        metadata["inventory_sha256"] = hashlib.sha256((out / "inventory.jsonl").read_bytes()).hexdigest()
        result.check_returncode()
        rows = validate_inventory(out / "inventory.jsonl")
        for relative, expected in sources.items():
            if hashlib.sha256((ROOT / relative).read_bytes()).hexdigest() != expected:
                raise ValueError("source changed during inventory collection: " + relative)
        metadata["validation"] = {"inputs": len(rows), "maximal_support": True}
        metadata["state"] = "complete"
    except Exception as error:
        metadata["state"] = "failed"
        metadata["error"] = str(error)
        raise
    finally:
        record.write_text(json.dumps(metadata, indent=2) + "\n")
        lease.close()
    print(out, flush=True)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
