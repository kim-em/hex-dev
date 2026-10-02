#!/usr/bin/env python3
"""External nauty 2.9.3 oracle for ``HexGraphIso``.

Rebuilds each original coloured graph from its fixture record and runs the
pinned dense or sparse nauty configuration through the project-owned C shim
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
compared exactly; group order is the integer product of the level
indices collected through ``userlevelproc``, without floating-point rounding.
``graphisosparse`` and ``graphisosparseautos`` records use native edge input
and compare ``canonEdges`` instead of a dense upper triangle.

The compiled shim binary is cached in ``HEX_NAUTY_CACHE`` or
``~/.cache/hex-nauty``, keyed by the SHA-256 of the shim source together
with every vendored file it links, so a stale or foreign binary is never
reused. A compile failure, nauty error, or output mismatch fails the run.
"""
from __future__ import annotations

import hashlib
import math
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
VENDOR_SOURCES = ["nauty.c", "nautil.c", "naugraph.c", "nausparse.c", "schreier.c",
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


SPARSE_KINDS = ("graphisosparse", "graphisosparseautos")
KINDS = ("graphiso", "graphisoautos") + SPARSE_KINDS
STAT_FIELDS = ("numorbits", "numgenerators", "numnodes", "numbadleaves",
               "maxlevel", "tctotal", "canupdates")


def _shim_input(record: dict) -> str:
    n = record["n"]
    k = record["k"]
    lines = [f"{n} {k}", " ".join(str(c) for c in record["colors"])]
    if record["kind"] in SPARSE_KINDS:
        edges = sorted({tuple(sorted(edge)) for edge in record["edges"]})
        lines.append(str(len(edges)))
        lines.extend(f"{a} {b}" for a, b in edges)
    else:
        adj = [[0] * n for _ in range(n)]
        for a, b in record["edges"]:
            adj[a][b] = adj[b][a] = 1
        lines.extend("".join(map(str, row)) for row in adj)
    return "\n".join(lines) + "\n"


def _parse(line: str) -> dict:
    """Decode either representation, including exact group order and statistics."""
    sections = {}
    for section in line.split(" | "):
        name, _, value = section.partition(" ")
        if name in sections:
            raise OracleMismatch(f"duplicate shim section {name}")
        sections[name] = value.strip()
    lab = [int(x) for x in sections["lab"].split()]
    n = len(lab)
    gen_fields = [int(x) for x in sections["gens"].split()]
    ngens, flat = gen_fields[0], gen_fields[1:]
    if ngens * n != len(flat):
        raise OracleMismatch("wrong number of generator entries from shim")
    g1, g2 = sections["grp"].split()
    indices = [int(x) for x in sections["indices"].split()]
    if any(i < 1 for i in indices):
        raise OracleMismatch("nonpositive group index from shim")
    stats = [int(x) for x in sections["stats"].split()]
    if len(stats) != len(STAT_FIELDS):
        raise OracleMismatch("wrong number of search statistics from shim")
    answer = {
        "lab": lab, "nodes": int(sections["nodes"]),
        "gens": [flat[t * n:(t + 1) * n] for t in range(ngens)],
        "orbits": [int(x) for x in sections["orbits"].split()],
        "norbits": int(sections["norbits"]),
        "grpsize1": float(g1), "grpsize2": int(g2),
        "indices": indices, "order": math.prod(indices),
        "stats": dict(zip(STAT_FIELDS, stats)),
    }
    if "tri" in sections:
        answer["tri"] = sections["tri"]
    elif "edges" in sections:
        count, *flat_edges = map(int, sections["edges"].split())
        if len(flat_edges) != 2 * count:
            raise OracleMismatch("wrong number of canonical edge entries from shim")
        answer["edges"] = [flat_edges[i:i+2] for i in range(0, len(flat_edges), 2)]
    else:
        raise OracleMismatch("missing canonical adjacency from shim")
    return answer


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
    order = answer["order"]
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
    edges = {tuple(sorted(edge)) for edge in record["edges"]}
    colors = record["colors"]
    for gen in record["gens"]:
        if sorted(gen) != list(range(record["n"])):
            raise OracleMismatch(f"{case}: {gen} is not a permutation")
        if any(colors[i] != colors[gen[i]] for i in range(record["n"])) or {
                tuple(sorted((gen[a], gen[b]))) for a, b in edges} != edges:
            raise OracleMismatch(f"{case}: {gen} is not a colour-preserving automorphism")


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
        if record["canonLab"] != [] or record.get("canonTri", "") != "" or record.get("canonEdges", []) != []:
            raise OracleMismatch(f"{case}: nonempty answer for the empty graph")
        if record["numnodes"] != 1:
            raise OracleMismatch(f"{case}: incorrect empty-graph node count")
        if record["kind"] in SPARSE_KINDS and record["stats"] != dict(
                zip(STAT_FIELDS, [0, 0, 1, 0, 1, 0, 1])):
            raise OracleMismatch(f"{case}: incorrect empty sparse statistics")
        return
    assert shim_line is not None
    answer = _parse(shim_line)
    lab = answer["lab"]
    nodes = answer["nodes"]
    if lab != record["canonLab"]:
        raise OracleMismatch(f"{case}: canonLab {record['canonLab']} != nauty {lab}")
    if record["kind"] in SPARSE_KINDS:
        if answer["edges"] != record["canonEdges"]:
            raise OracleMismatch(f"{case}: canonical edges differ from sparse nauty")
        if record["stats"] != answer["stats"]:
            raise OracleMismatch(f"{case}: sparse search statistics differ from nauty")
    elif answer["tri"] != record["canonTri"]:
        raise OracleMismatch(f"{case}: canonTri {record['canonTri']} != nauty {answer['tri']}")
    if nodes != record["numnodes"]:
        raise OracleMismatch(f"{case}: numnodes {record['numnodes']} != nauty {nodes}")


def check_records(records: list[dict], *, trace: bool = False) -> tuple[int, int]:
    shim = _build_shim()
    checked = autos = 0
    for sparse in (False, True):
        selected = [r for r in records if (r["kind"] in SPARSE_KINDS) == sparse]
        if not selected:
            continue
        payload = "".join(_shim_input(r) for r in selected if r["n"] >= 1) + "-1 -1\n"
        command = [str(shim)] + (["--sparse"] if sparse else []) + (["--trace"] if trace else [])
        proc = subprocess.run(command, input=payload, capture_output=True, text=True, check=True)
        if trace:
            sys.stderr.write(proc.stderr)
        lines = proc.stdout.splitlines()
        expected = sum(r["n"] >= 1 for r in selected)
        if len(lines) != expected:
            raise OracleMismatch(f"shim produced {len(lines)} answers for {expected} cases")
        it = iter(lines)
        for record in selected:
            line = next(it) if record["n"] >= 1 else None
            _check(record, line)
            if record["kind"] in ("graphisoautos", "graphisosparseautos"):
                if line is None:
                    if (record["gens"] != [] or record["orbits"] != [] or
                            record["numOrbits"] != 0 or record["numGenerators"] != 0 or
                            record["order"] != 1):
                        raise OracleMismatch("invalid empty-graph automorphism result")
                else:
                    _check_autos(record, _parse(line))
                autos += 1
            checked += 1
    return checked, autos


def main() -> int:
    records = [r for r in read_fixtures() if r["kind"] in KINDS]
    if not records:
        print("graphiso oracle: no graphiso records on stdin", file=sys.stderr)
        return 1
    checked, autos = check_records(records)
    print(f"graphiso oracle: {checked} cases checked against nauty 2.9.3 "
          f"({autos} automorphism-group cases)")
    return 0


if __name__ == "__main__":
    try:
        sys.exit(main())
    except OracleMismatch as exc:
        print(f"FAIL: {exc}", file=sys.stderr)
        sys.exit(1)
