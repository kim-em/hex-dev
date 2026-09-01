#!/usr/bin/env python3
"""External nauty 2.9.3 oracle for ``HexGraphIso``.

Rebuilds each original coloured graph from its fixture record and runs the
pinned dense-nauty configuration through the project-owned C shim
(``graphiso_nauty_shim.c``), compiled against the hash-verified nauty
2.9.3 source. The oracle independently computes and compares the ordered
colour-cell sizes, the canonical upper-triangle adjacency bits, and every
entry of ``canonlab``; the Lean answer is never canonicalized before
comparison. The visited-node counter is also compared, pinning the whole
search traversal rather than only its result.

The nauty tarball is restored from the content-addressed cache directory
(``HEX_NAUTY_CACHE`` or ``~/.cache/hex-nauty``), keyed by its SHA-256; the
ANU URL is the provenance source and a fallback download location, not the
only cache-cold location. A missing artifact, hash mismatch, compile
failure, nauty error, or output mismatch fails the run. The mirrored
archive retains its ``COPYRIGHT`` and ``LICENSE-2.0.txt`` files.
"""
from __future__ import annotations

import hashlib
import os
import subprocess
import sys
import tarfile
import urllib.request
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

NAUTY_URL = "https://users.cecs.anu.edu.au/~bdm/nauty/nauty2_9_3.tar.gz"
NAUTY_SHA256 = "9fc4edae04f88a0f5883985be3b39cf7f898fd6cc96e96b9ee25452743cc1b5b"
SHIM_SOURCE = Path(__file__).resolve().parent / "graphiso_nauty_shim.c"


def _cache_dir() -> Path:
    env = os.environ.get("HEX_NAUTY_CACHE")
    if env:
        return Path(env)
    return Path.home() / ".cache" / "hex-nauty"


def _fetch_tarball(cache: Path) -> Path:
    cache.mkdir(parents=True, exist_ok=True)
    tarball = cache / "nauty2_9_3.tar.gz"
    if not tarball.exists():
        print(f"graphiso oracle: downloading {NAUTY_URL}", file=sys.stderr)
        with urllib.request.urlopen(NAUTY_URL, timeout=120) as resp:
            tarball.write_bytes(resp.read())
    digest = hashlib.sha256(tarball.read_bytes()).hexdigest()
    if digest != NAUTY_SHA256:
        tarball.unlink()
        raise OracleMismatch(
            f"nauty tarball SHA-256 mismatch: got {digest}, want {NAUTY_SHA256}"
        )
    return tarball


def _build_shim() -> Path:
    cache = _cache_dir()
    shim_hash = hashlib.sha256(SHIM_SOURCE.read_bytes()).hexdigest()[:16]
    shim = cache / f"graphiso_shim-{shim_hash}"
    if shim.exists():
        return shim
    tarball = _fetch_tarball(cache)
    src = cache / "nauty2_9_3"
    if not (src / "nauty.h").exists():
        with tarfile.open(tarball) as tf:
            tf.extractall(cache)
    for required in ("COPYRIGHT", "LICENSE-2.0.txt"):
        if not (src / required).exists():
            raise OracleMismatch(f"nauty archive is missing {required}")
    objs = ["nauty.o", "nautil.o", "naugraph.o", "schreier.o", "naurng.o"]
    if not all((src / o).exists() for o in objs):
        subprocess.run(
            ["./configure", "--quiet"], cwd=src, check=True,
            stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL,
        )
        subprocess.run(
            ["make"] + objs, cwd=src, check=True,
            stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL,
        )
    subprocess.run(
        ["cc", "-O2", "-I", str(src), "-o", str(shim), str(SHIM_SOURCE)]
        + [str(src / o) for o in objs],
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
