#!/usr/bin/env python3
"""Persistent-subprocess nauty 2.9.3 bench comparator driver.

Companion to ``Hex/BenchOracle/Nauty.lean`` (see
``SPEC/benchmarking.md`` §External comparators, process call). Reuses
the conformance oracle's hash-verified nauty source acquisition and C
shim (``graphiso_nauty_shim.c``): the shim binary is built once when
the driver starts; each request then runs one canonicalization through
a fresh shim process, which keeps the per-call overhead to one small
process spawn on top of the canonical search itself.

Protocol: one JSON object per stdin line,

    {"family": "nauty", "op": "canon", "n": N, "k": K,
     "colors": [c0, ...], "adj": ["0101...", ...]}

answered by one JSON line,

    {"ok": true, "result": {"lab": [...], "tri": "0101...",
                            "nodes": M}}

or ``{"ok": false, "error": "..."}``. An empty line or EOF terminates
the driver.
"""
from __future__ import annotations

import json
import subprocess
import sys
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parent.parent.parent
sys.path.insert(0, str(REPO_ROOT))

from scripts.oracle.graphiso_nauty import _build_shim  # noqa: E402


def _run_case(shim: Path, request: dict) -> dict:
    n = int(request["n"])
    k = int(request["k"])
    colors = request["colors"]
    adj = request["adj"]
    if len(colors) != n or len(adj) != n:
        raise ValueError("colors/adj length mismatch with n")
    lines = [f"{n} {k}", " ".join(str(int(c)) for c in colors)]
    for row in adj:
        if len(row) != n:
            raise ValueError("adjacency row length mismatch with n")
        lines.append(row)
    payload = "\n".join(lines) + "\n-1 -1\n"
    proc = subprocess.run(
        [str(shim)], input=payload, capture_output=True, text=True,
        check=True,
    )
    answers = [ln for ln in proc.stdout.splitlines() if ln.startswith("lab")]
    if len(answers) != 1:
        raise ValueError(f"shim produced {len(answers)} answers for 1 case")
    head, tri_part = answers[0].split(" | tri ")
    tri, nodes_part = tri_part.split(" | nodes ")
    return {
        "lab": [int(x) for x in head.split()[1:]],
        "tri": tri.strip(),
        "nodes": int(nodes_part),
    }


def main() -> int:
    shim = _build_shim()
    for line in sys.stdin:
        line = line.strip()
        if not line:
            break
        try:
            request = json.loads(line)
            if request.get("op") != "canon":
                raise ValueError(f"unknown op: {request.get('op')}")
            result = _run_case(shim, request)
            reply = {"ok": True, "result": result}
        except Exception as exc:  # noqa: BLE001
            reply = {"ok": False, "error": f"{type(exc).__name__}: {exc}"}
        sys.stdout.write(json.dumps(reply) + "\n")
        sys.stdout.flush()
    return 0


if __name__ == "__main__":
    sys.exit(main())
