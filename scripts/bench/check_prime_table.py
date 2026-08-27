#!/usr/bin/env python3
"""Check deterministic regeneration of the committed HexPrimality table.

Runs the standard invocation in ``GeneratePrimeTable.lean`` and compares its
two emitted regions (the bound/table literal and sieve replay) byte-for-byte
with ``HexPrimality/Table.lean``.  Documentation and hand-written lemmas between
the regions are intentionally outside the generated surface.
"""

from __future__ import annotations

import argparse
import difflib
from pathlib import Path
import subprocess
import sys


ROOT = Path(__file__).resolve().parents[2]
TABLE = ROOT / "HexPrimality" / "Table.lean"
GENERATOR = ROOT / "scripts" / "bench" / "GeneratePrimeTable.lean"


def regions(source: str, *, generated: bool) -> tuple[str, str]:
    start = source.index("@[expose]\ndef primeTableBound")
    bound_end = source.index("\n", source.index("def primeTableBound", start))
    table_start = source.index("@[expose]\ndef primeTable :", bound_end)
    if generated:
        split = source.index("\n-- #rebuild_primeTable", start)
        definitions = source[start:bound_end] + "\n\n" + source[table_start:split].rstrip()
        return definitions, source[split + 1:].rstrip()
    split = source.index("\n/-- Adjacent strict ascent", start)
    replay = source.index("-- #rebuild_primeTable", split)
    replay_end = source.index("\nprivate theorem mem_primeTable_iff_bits", replay)
    definitions = source[start:bound_end] + "\n\n" + source[table_start:split].rstrip()
    return definitions, source[replay:replay_end].rstrip()


def rewrite(source: str, generated: str) -> str:
    """Replace only the two generator-owned regions in ``Table.lean``."""
    start = source.index("@[expose]\ndef primeTableBound")
    bound_end = source.index("\n", source.index("def primeTableBound", start))
    table_start = source.index("@[expose]\ndef primeTable :", bound_end)
    table_end = source.index("\n/-- Adjacent strict ascent", table_start)
    replay_start = source.index("-- #rebuild_primeTable", table_end)
    replay_end = source.index("\nprivate theorem mem_primeTable_iff_bits", replay_start)

    generated_start = generated.index("@[expose]\ndef primeTableBound")
    generated_bound_end = generated.index(
        "\n", generated.index("def primeTableBound", generated_start)
    )
    generated_table_start = generated.index(
        "@[expose]\ndef primeTable :", generated_bound_end
    )
    generated_replay_start = generated.index("-- #rebuild_primeTable", generated_table_start)
    return (
        source[:start]
        + generated[generated_start:generated_bound_end]
        + source[bound_end:table_start]
        + generated[generated_table_start:generated_replay_start].rstrip()
        + source[table_end:replay_start]
        + generated[generated_replay_start:].rstrip()
        + source[replay_end:]
    )


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--write", action="store_true",
        help="rewrite the generator-owned regions before checking",
    )
    args = parser.parse_args()
    generated = subprocess.run(
        ["lake", "env", "lean", str(GENERATOR.relative_to(ROOT))],
        cwd=ROOT, check=True, capture_output=True, text=True,
    ).stdout
    source = TABLE.read_text()
    try:
        if args.write:
            source = rewrite(source, generated)
            TABLE.write_text(source)
        expected = regions(generated, generated=True)
        actual = regions(source, generated=False)
    except ValueError as error:
        print(f"prime-table layout marker missing: {error}", file=sys.stderr)
        return 2
    labels = ("bound/table literal", "sieve replay")
    ok = True
    for label, want, got in zip(labels, expected, actual):
        if want == got:
            continue
        ok = False
        print(f"{label} differs from standard generator:", file=sys.stderr)
        print("".join(difflib.unified_diff(
            got.splitlines(keepends=True), want.splitlines(keepends=True),
            fromfile="committed", tofile="generated",
        )), file=sys.stderr)
    if not ok:
        return 1
    print("committed prime table matches deterministic generator output")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
