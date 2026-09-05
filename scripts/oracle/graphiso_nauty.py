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
comparison. The visited-node counter is also compared, so the fixture
pins how much of the tree the two programs walked and not only the
answer they reached.

``graphisoautos`` records pin the automorphism surface. They carry every
field of a ``graphiso`` record as well, so a consumer reading the whole
stream for canonical forms needs no knowledge of the second kind, and
the canonical checks above run on them too. The shim
collects nauty's own generator list through ``options.userautomproc``,
so the comparison is against the traversal's emissions rather than a
recomputation. nauty emits a generator at every code-1 leaf and at
every code-2 leaf that grows the orbit partition; the Lean trace
records both kinds unconditionally, so nauty's list must appear in the
Lean list as an ordered subsequence, of exactly ``numGenerators``
entries; when the two lists are the same length, which is every case on
the current corpus, they must agree entry by entry. The recorded list
itself is pinned by the committed fixture, so a change in the traversal
shows up as a fixture diff even where the subsequence relation would
tolerate it. The orbit array, the orbit count and the group order are
compared exactly; the order comparison refuses a case whose order has
reached ``10 ** 10``, where nauty's ``grpsize1`` is no longer an exact
integer.

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


def _parse(line: str) -> dict:
    """Split one shim answer into its labelled sections."""
    head, rest = line.split(" | tri ")
    tri, rest = rest.split(" | nodes ")
    nodes, rest = rest.split(" | gens ")
    gens, rest = rest.split(" | orbits ")
    orbits, rest = rest.split(" | norbits ")
    norbits, grp = rest.split(" | grp ")
    gen_fields = gens.split()
    ngens = int(gen_fields[0])
    flat = [int(x) for x in gen_fields[1:]]
    n = len(head.split()) - 1
    if ngens * n != len(flat):
        raise OracleMismatch(
            f"shim emitted {len(flat)} generator entries for {ngens} "
            f"generators on {n} vertices"
        )
    g1, g2 = grp.split()
    return {
        "lab": [int(x) for x in head.split()[1:]],
        "tri": tri.strip(),
        "nodes": int(nodes),
        "gens": [flat[t * n:(t + 1) * n] for t in range(ngens)],
        "orbits": [int(x) for x in orbits.split()],
        "norbits": int(norbits),
        "grpsize1": float(g1),
        "grpsize2": int(g2),
    }


def _is_subsequence(small: list, big: list) -> bool:
    it = iter(big)
    return all(any(x == y for y in it) for x in small)


def _check_autos(record: dict, answer: dict) -> None:
    case = record["case"]
    if answer["orbits"] != record["orbits"]:
        raise OracleMismatch(
            f"{case}: orbits {record['orbits']} != nauty {answer['orbits']}"
        )
    if answer["norbits"] != record["numOrbits"]:
        raise OracleMismatch(
            f"{case}: numOrbits {record['numOrbits']} != nauty "
            f"{answer['norbits']}"
        )
    # nauty carries the group order as grpsize1 * 10 ** grpsize2, and
    # normalizes out of the double only once the product reaches 1e10
    # (nauty.h MULTIPLY). Below that the double is an exact integer and
    # the comparison is exact; above it the mantissa has been divided and
    # no integer can be recovered, so refuse rather than compare with a
    # tolerance that would accept a wrong order. Every corpus case is
    # well below the threshold; a case that is not has to be reconsidered
    # here rather than silently weakened.
    if answer["grpsize2"] != 0:
        raise OracleMismatch(
            f"{case}: nauty reports the group order as "
            f"{answer['grpsize1']} * 10 ** {answer['grpsize2']}, past the "
            f"range where it is an exact integer; the automorphism corpus "
            f"must stay below 10 ** 10"
        )
    order = int(round(answer["grpsize1"]))
    if order != record["order"]:
        raise OracleMismatch(
            f"{case}: order {record['order']} != nauty {order}"
        )
    if len(answer["gens"]) != record["numGenerators"]:
        raise OracleMismatch(
            f"{case}: numGenerators {record['numGenerators']} != nauty "
            f"{len(answer['gens'])}"
        )
    if len(record["gens"]) == len(answer["gens"]):
        # the usual case: nothing was suppressed, so the lists must agree
        # entry by entry rather than only up to a subsequence
        if record["gens"] != answer["gens"]:
            raise OracleMismatch(
                f"{case}: generators {record['gens']} != nauty "
                f"{answer['gens']}"
            )
    elif len(record["gens"]) < len(answer["gens"]):
        raise OracleMismatch(
            f"{case}: recorded {len(record['gens'])} generators, fewer than "
            f"the {len(answer['gens'])} nauty emitted"
        )
    elif not _is_subsequence(answer["gens"], record["gens"]):
        raise OracleMismatch(
            f"{case}: nauty generators {answer['gens']} are not a "
            f"subsequence of the recorded trace {record['gens']}"
        )
    for gen in record["gens"]:
        if sorted(gen) != list(range(record["n"])):
            raise OracleMismatch(f"{case}: {gen} is not a permutation")


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
    answer = _parse(shim_line)
    lab = answer["lab"]
    tri = answer["tri"]
    nodes = answer["nodes"]
    if lab != record["canonLab"]:
        raise OracleMismatch(f"{case}: canonLab {record['canonLab']} != nauty {lab}")
    if tri != record["canonTri"]:
        raise OracleMismatch(f"{case}: canonTri {record['canonTri']} != nauty {tri}")
    if nodes != record["numnodes"]:
        raise OracleMismatch(f"{case}: numnodes {record['numnodes']} != nauty {nodes}")


def main() -> int:
    shim = _build_shim()
    records = [r for r in read_fixtures()
               if r["kind"] in ("graphiso", "graphisoautos")]
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
    autos = 0
    for record in records:
        line = next(it) if record["n"] >= 1 else None
        # an automorphism record carries the canonical fields too, so
        # both checks run on it
        _check(record, line)
        if record["kind"] == "graphisoautos":
            assert line is not None
            _check_autos(record, _parse(line))
            autos += 1
        checked += 1
    print(f"graphiso oracle: {checked} cases checked against nauty 2.9.3 "
          f"({autos} automorphism-group cases)")
    return 0


if __name__ == "__main__":
    try:
        sys.exit(main())
    except OracleMismatch as exc:
        print(f"FAIL: {exc}", file=sys.stderr)
        sys.exit(1)
