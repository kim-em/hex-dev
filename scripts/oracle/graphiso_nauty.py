#!/usr/bin/env python3
"""External nauty 2.9.3 oracle for ``HexGraphIso``.

Rebuilds each original coloured graph from its fixture record and runs the
pinned dense-nauty configuration through the project-owned C shim
(``graphiso_nauty_shim.c``), compiled against the vendored nauty 2.9.3
source in ``vendor/nauty-2.9.3`` (unmodified files from the pinned
archive, hash-recorded in that directory's README and version-controlled
here). The oracle independently computes and compares the ordered
colour-cell sizes, the canonical upper-triangle adjacency bits, and every
entry of ``canonlab``; the Lean answer is never canonicalized before
comparison. The visited-node counter is also compared, pinning the whole
search traversal rather than only its result.

The compiled shim binary is cached in ``HEX_NAUTY_CACHE`` or
``~/.cache/hex-nauty``, keyed by the SHA-256 of the shim source together
with every vendored file it links, so a stale or foreign binary is never
reused. A compile failure, nauty error, or output mismatch fails the run.
"""
from __future__ import annotations

import hashlib
import os
import subprocess
import sys
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parent.parent.parent
DEFAULT_FIXTURE = (
    REPO_ROOT / "conformance-fixtures" / "HexGraphIso" / "graphiso.jsonl"
)

sys.path.insert(0, str(REPO_ROOT))

from scripts.oracle.common import (  # noqa: E402
    OracleMismatch,
    read_fixtures,
)

SHIM_SOURCE = Path(__file__).resolve().parent / "graphiso_nauty_shim.c"


def _cache_dir() -> Path:
    override = os.environ.get("HEX_NAUTY_CACHE")
    base = Path(override) if override else Path.home() / ".cache" / "hex-nauty"
    base.mkdir(parents=True, exist_ok=True)
    return base


VENDOR_DIR = REPO_ROOT / "vendor" / "nauty-2.9.3"
VENDOR_SOURCES = ["nauty.c", "nautil.c", "naugraph.c", "schreier.c",
                  "naurng.c"]
VENDOR_HEADERS = ["nauty.h", "naututil.h", "nausparse.h", "schreier.h",
                  "naurng.h", "sorttemplates.c"]


def _build_shim() -> Path:
    cache = _cache_dir()
    digest = hashlib.sha256()
    digest.update(SHIM_SOURCE.read_bytes())
    for name in VENDOR_SOURCES + VENDOR_HEADERS:
        digest.update(name.encode())
        digest.update((VENDOR_DIR / name).read_bytes())
    shim = cache / f"graphiso_shim-{digest.hexdigest()[:16]}"
    if shim.exists():
        return shim
    for required in ("COPYRIGHT", "LICENSE-2.0.txt"):
        if not (VENDOR_DIR / required).exists():
            raise OracleMismatch(f"vendored nauty is missing {required}")
    subprocess.run(
        ["cc", "-O2", "-I", str(VENDOR_DIR), "-o", str(shim),
         str(SHIM_SOURCE)]
        + [str(VENDOR_DIR / src) for src in VENDOR_SOURCES],
        check=True,
    )
    return shim


def _shim_input(record: dict) -> str:
    n = record["n"]
    k = record["k"]
    adj = [[0] * n for _ in range(n)]
    for a, b in record["edges"]:
        adj[a][b] = adj[b][a] = 1
    lines = [f"{n} {k}", " ".join(str(c) for c in record["colors"])]
    for i in range(n):
        lines.append("".join(str(adj[i][j]) for j in range(n)))
    return "\n".join(lines) + "\n"


def _check(record: dict, shim_line: str | None) -> None:
    n = record["n"]
    k = record["k"]
    case = record["case"]
    # independently recomputed ordered colour-cell sizes
    sizes = [0] * k
    for c in record["colors"]:
        sizes[c] += 1
    if sizes != record["cellSizes"]:
        raise OracleMismatch(
            f"{case}: cellSizes {record['cellSizes']} != recomputed {sizes}"
        )
    if n == 0:
        if record["canonLab"] != [] or record["canonTri"] != "":
            raise OracleMismatch(f"{case}: nonempty answer for the empty graph")
        return
    assert shim_line is not None
    head, tri_part = shim_line.split(" | tri ")
    tri, nodes_part = tri_part.split(" | nodes ")
    lab = [int(x) for x in head.split()[1:]]
    tri = tri.strip()
    nodes = int(nodes_part)
    if lab != record["canonLab"]:
        raise OracleMismatch(f"{case}: canonLab {record['canonLab']} != nauty {lab}")
    if tri != record["canonTri"]:
        raise OracleMismatch(f"{case}: canonTri {record['canonTri']} != nauty {tri}")
    if nodes != record["numnodes"]:
        raise OracleMismatch(f"{case}: numnodes {record['numnodes']} != nauty {nodes}")


def main() -> int:
    shim = _build_shim()
    records = [r for r in read_fixtures() if r["kind"] == "graphiso"]
    if not records:
        print("graphiso oracle: no graphiso records on stdin", file=sys.stderr)
        return 1
    payload = "".join(_shim_input(r) for r in records if r["n"] >= 1)
    payload += "-1 -1\n"
    proc = subprocess.run(
        [str(shim)], input=payload, capture_output=True, text=True, check=True,
    )
    lines = [line for line in proc.stdout.splitlines() if line.startswith("lab")]
    expected = sum(1 for r in records if r["n"] >= 1)
    if len(lines) != expected:
        raise OracleMismatch(
            f"shim produced {len(lines)} answers for {expected} cases"
        )
    it = iter(lines)
    checked = 0
    for record in records:
        line = next(it) if record["n"] >= 1 else None
        _check(record, line)
        checked += 1
    print(f"graphiso oracle: {checked} cases checked against nauty 2.9.3")
    return 0


if __name__ == "__main__":
    try:
        sys.exit(main())
    except OracleMismatch as exc:
        print(f"FAIL: {exc}", file=sys.stderr)
        sys.exit(1)
