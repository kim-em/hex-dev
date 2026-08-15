#!/usr/bin/env python3
"""Generate the package-owned full FKS2 Table4Ext data and proof shards.

The input must be the pinned PNT+ checkout.  Tuple spelling is normalized only
by removing insignificant whitespace and a trailing comma; every generated
tuple and per-shard SHA-256 digest is checked by ``pnt_inventory.py``.
"""

from __future__ import annotations

import argparse
import hashlib
import re
from pathlib import Path


PNT_COMMIT = "21998bb6196b56789f72a52656a781a75e134eb0"
SOURCE_DIR = Path("PrimeNumberTheoremAnd/IEANTN/FKS2Tables")
DATA_DIR = Path("HexInterval/Experiment")
PROOF_DIR = Path("HexIntervalMathlib/Experiment")
CELL_RE = re.compile(r"^\s*(⟨.*⟩),?\s*$")


def cells(path: Path) -> list[str]:
    result: list[str] = []
    for line in path.read_text(encoding="utf-8").splitlines():
        match = CELL_RE.match(line)
        if match:
            result.append(re.sub(r"\s+", "", match.group(1)))
    return result


def digest(rows: list[str]) -> str:
    return hashlib.sha256(("\n".join(rows) + "\n").encode()).hexdigest()


def data_module(shard: int, rows: list[str]) -> str:
    name = f"{shard:02}"
    proof_chunk = 10 if shard == 13 else 20
    chunks = [rows[i:i + proof_chunk] for i in range(0, len(rows), proof_chunk)]
    cases: list[str] = []
    for index, chunk in enumerate(chunks):
        body = ",\n".join(f"      {row}" for row in chunk)
        cases.append(f"  | {index} => [\n{body}\n    ]")
    return f'''/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexInterval.Experiment.PntFks2ShardData

@[expose] public section

/-!
# Generated pinned PNT+ FKS2 shard {name} cells

All {len(rows)} tuples are copied exactly from pinned PNT+ shard {name} at
commit `{PNT_COMMIT}`.  The bounded proof chunks contain {proof_chunk} cells.
The source-correlation checker authenticates every tuple and the shard digest.
-/

namespace Hex.Interval.Experiment.PntFks2Family

open PntFks2Shard

def proofChunk{name} : Nat → List Cell
{chr(10).join(cases)}
  | _ => []

def proofChunkCount{name} : Nat := {len(chunks)}

def cells{name} : List Cell :=
  (List.range proofChunkCount{name}).flatMap proofChunk{name}

end Hex.Interval.Experiment.PntFks2Family
'''


def proof_module(shard: int, rows: list[str]) -> str:
    name = f"{shard:02}"
    proof_chunk = 10 if shard == 13 else 20
    alternatives = " | ".join("rfl" for _ in range(proof_chunk))
    return f'''/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexIntervalMathlib.Experiment.PntFks2Shard
public import HexInterval.Experiment.PntFks2FamilyData{name}

@[expose] public section

/-! # Kernel certificate for pinned FKS2 shard {name} -/

namespace Hex.Interval.Experiment.PntFks2Family

open PntFks2Shard

set_option maxRecDepth 100000 in
set_option maxHeartbeats 20000000 in
theorem chunk{name}_valid (index : Nat) (valid : index < proofChunkCount{name})
    (cell : Cell) (member : cell ∈ proofChunk{name} index) : CellValid cell := by
  norm_num [proofChunkCount{name}] at valid
  interval_cases index <;>
    simp only [proofChunk{name}, List.mem_cons, List.not_mem_nil, or_false] at member <;>
    rcases member with {alternatives} <;>
    simp only [CellValid, qmul_value, qpow_value, qpow128_value,
      taylorUpper_value] <;>
    norm_num [Q.value, cq128, aq]

/-- Exact source-shaped executable check for pinned shard {name}. -/
theorem cells{name}_checked : cells{name}.all checkCell = true := by
  exact List.all_eq_true.mpr fun cell member => by
    rw [cells{name}, List.mem_flatMap] at member
    obtain ⟨index, indexMember, cellMember⟩ := member
    exact check_of_valid cell (chunk{name}_valid index
      (List.mem_range.mp indexMember) cell cellMember)

/-- Arbitrary-membership semantic wrapper for pinned shard {name}. -/
theorem cells{name}_holds (cell : Cell) (member : cell ∈ cells{name}) :
    CellHolds cell :=
  cellHolds_of_check cell (List.all_eq_true.mp cells{name}_checked cell member)

end Hex.Interval.Experiment.PntFks2Family
'''


def aggregate(digests: list[str], counts: list[int]) -> str:
    imports = "\n".join(
        f"public import HexInterval.Experiment.PntFks2FamilyData{i:02}"
        for i in range(14) if i != 11
    )
    records = ",\n".join(
        f'  ⟨{i}, {counts[i]}, "{digests[i]}"⟩' for i in range(14)
    )
    cases = "\n".join(
        f"  | {i} => " + ("PntFks2Shard.cells11" if i == 11 else f"cells{i:02}")
        for i in range(14)
    )
    return f'''/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

{imports}

@[expose] public section

/-! # Source-correlated full pinned PNT+ FKS2 family data -/

namespace Hex.Interval.Experiment.PntFks2Family

open PntFks2Shard

structure ShardRecord where
  shard : Nat
  cells : Nat
  digest : String
  deriving DecidableEq, Repr

/-- SHA-256 digests of the normalized tuples in each exact source shard. -/
def shardRecords : List ShardRecord := [
{records}
]

def shardCount : Nat := 14
def familyCellCount : Nat := 13590
def runtimeChunkSize : Nat := 20
def familyChunkCount : Nat := 680

def shardCells : Nat → List Cell
{cases}
  | _ => []

/-- All source cells in exact shard and declaration order. -/
def allCells : List Cell := (List.range shardCount).flatMap shardCells

def chunkShard (index : Nat) : Nat := index / 50
def chunkLocal (index : Nat) : Nat := index % 50

/-- Runtime chunks are twenty cells, except the final ten-cell chunk. -/
def familyChunk (index : Nat) : List Cell :=
  (shardCells (chunkShard index)).drop (chunkLocal index * runtimeChunkSize)
    |>.take runtimeChunkSize

end Hex.Interval.Experiment.PntFks2Family
'''


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--source", type=Path, required=True)
    parser.add_argument("--repo", type=Path, default=Path.cwd())
    args = parser.parse_args()
    source_commit = __import__("subprocess").check_output(
        ["git", "rev-parse", "HEAD"], cwd=args.source, text=True).strip()
    if source_commit != PNT_COMMIT:
        raise SystemExit(f"wrong PNT+ source commit: {source_commit}")

    all_rows: list[list[str]] = []
    digests: list[str] = []
    for shard in range(14):
        path = args.source / SOURCE_DIR / f"Table4ExtData_{shard:02}.lean"
        rows = cells(path)
        expected = 590 if shard == 13 else 1000
        if len(rows) != expected:
            raise SystemExit(f"shard {shard:02}: expected {expected}, found {len(rows)}")
        all_rows.append(rows)
        digests.append(digest(rows))
        if shard != 11:
            (args.repo / DATA_DIR / f"PntFks2FamilyData{shard:02}.lean").write_text(
                data_module(shard, rows), encoding="utf-8")
            (args.repo / PROOF_DIR / f"PntFks2FamilyProof{shard:02}.lean").write_text(
                proof_module(shard, rows), encoding="utf-8")

    (args.repo / DATA_DIR / "PntFks2FamilyData.lean").write_text(
        aggregate(digests, [len(rows) for rows in all_rows]), encoding="utf-8")


if __name__ == "__main__":
    main()
