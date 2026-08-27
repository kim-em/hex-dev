#!/usr/bin/env python3
"""Kernel microbenchmark for the integer dense polynomial product (issue #9142).

Runs `hexpolyz_kronecker_crossover`, which times schoolbook convolution and all
four forced multipoint Kronecker kernels over a degree by coefficient-width
grid, including wide packed integers. It writes one durable JSON record with
environment metadata. The record is the evidence behind the integer kernel
dispatcher; see `HexPolyZ/SPEC/hex-poly-z.md`.

This is a manual diagnostic driver, not a CI job and not a hex-internal
benchmark harness, so the one-harness rule stays intact (see
SPEC/benchmarking.md addendum).

The driver pins the measured process to one core. `--cpu auto` (the default)
picks a core that is currently idle on itself and on its SMT siblings, because
several measurement drivers may run at once on a shared host and pinning them
all to a fixed core makes each measure the others. See
`scripts/bench/idle_core.py`.

Run::

    lake build hexpolyz_kronecker_crossover
    python3 scripts/bench/kronecker_crossover.py \\
        --output reports/bench-results/hexbz-kronecker-crossover.json
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

sys.path.insert(0, str(Path(__file__).resolve().parent))
import idle_core  # noqa: E402

ROOT = Path(__file__).resolve().parents[2]
EXE = ROOT / ".lake" / "build" / "bin" / "hexpolyz_kronecker_crossover"

SCHEMA = "hexbz-kronecker-crossover/2"


def sha256(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as handle:
        for chunk in iter(lambda: handle.read(1 << 20), b""):
            digest.update(chunk)
    return digest.hexdigest()


def git_commit() -> str:
    result = subprocess.run(
        ["git", "rev-parse", "HEAD"], cwd=ROOT, text=True,
        stdout=subprocess.PIPE, stderr=subprocess.DEVNULL,
    )
    return result.stdout.strip() or "unknown"


def crossovers(cells: list[dict]) -> dict[str, int | None]:
    """Smallest swept degree at which Kronecker wins, per coefficient width."""
    out: dict[str, int | None] = {}
    for cell in cells:
        if cell["signed"]:
            continue
        key = str(cell["bits"])
        if cell["ratio"] >= 1.0:
            best = out.get(key)
            if best is None or cell["n"] < best:
                out[key] = cell["n"]
        else:
            out.setdefault(key, None)
    return out


def fastest_ks(cells: list[dict]) -> dict[str, str]:
    """Fastest forced KS kernel at each measured degree/width/sign cell."""
    fields = ["ks1_nanos", "ks2_nanos", "ks3_nanos", "ks4_nanos"]
    return {
        f'{cell["n"]}:{cell["bits"]}:{str(cell["signed"]).lower()}':
            min(fields, key=lambda field: cell[field]).removesuffix("_nanos")
        for cell in cells
    }


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", required=True, type=Path)
    parser.add_argument("--cpu", default="auto",
                        help="core to pin to, or 'auto' (default) to pick an idle one")
    args = parser.parse_args()

    if not EXE.exists():
        print(f"missing {EXE}; run `lake build hexpolyz_kronecker_crossover`",
              file=sys.stderr)
        return 2

    cpu = idle_core.pick() if args.cpu == "auto" else int(args.cpu)
    cmd = ["taskset", "-c", str(cpu), str(EXE)]
    completed = subprocess.run(cmd, cwd=ROOT, text=True, stdout=subprocess.PIPE)
    if completed.returncode != 0:
        print(completed.stdout, file=sys.stderr)
        return completed.returncode
    payload = json.loads(completed.stdout)

    record = {
        "schema": SCHEMA,
        "config": {
            "exe": EXE.name,
            "exe_sha256": sha256(EXE),
            "size_cutoff": payload["size_cutoff"],
            "bit_cutoff": payload["bit_cutoff"],
        },
        "env": {
            "commit": git_commit(),
            "host": platform.node(),
            "machine": platform.machine(),
            "cpu": cpu,
            "cpu_count": os.cpu_count(),
            "platform": platform.platform(),
        },
        "cells": payload["cells"],
        "crossover_degree_by_bits": crossovers(payload["cells"]),
        "fastest_ks_by_degree_bits_sign": fastest_ks(payload["cells"]),
    }
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(record, indent=1, sort_keys=True) + "\n")
    print(f"wrote {args.output}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
