#!/usr/bin/env python3
"""Generate ordinary-kernel proofs for the six disjoint FKS2 xpow bands."""

from pathlib import Path


ROOT = Path(__file__).resolve().parents[2]
BANDS = ((0, 70), (70, 27), (97, 27), (124, 136), (260, 1088), (1348, 2398))


def split_band(
    start: int, count: int,
) -> tuple[tuple[int, int, int] | None, list[int], tuple[int, int, int] | None]:
    """Split a band into at most two partial pieces and full 20-cell chunks."""
    cursor = start
    remaining = count
    first = None
    if cursor % 20:
        length = min(20 - cursor % 20, remaining)
        first = (cursor // 20, cursor % 20, length)
        cursor += length
        remaining -= length
    interior = list(range(cursor // 20, cursor // 20 + remaining // 20))
    cursor += 20 * len(interior)
    remaining -= 20 * len(interior)
    last = (cursor // 20, 0, remaining) if remaining else None
    return first, interior, last


def source_chunk(global_chunk: int, offset: int, length: int) -> str:
    shard = global_chunk // 50
    local = global_chunk % 50
    expression = f"proofChunk{shard:02d} {local}"
    if offset:
        expression = f"({expression}).drop {offset}"
    if length != 20 - offset:
        expression = f"({expression}).take {length}"
    return expression


def partial_proof(index: int, name: str, piece: tuple[int, int, int] | None) -> str:
    if piece is None:
        proof = f"  simp [proofBand{index:02d}{name}] at member"
    else:
        chunk, offset, length = piece
        shard = chunk // 50
        alternatives = " | ".join("rfl" for _ in range(length))
        operations = []
        if offset:
            operations.append("List.drop")
        if length != 20 - offset:
            operations.append("List.take")
        operation_text = "".join(f", {operation}" for operation in operations)
        proof = f'''  simp only [proofBand{index:02d}{name}, proofChunk{shard:02d}{operation_text},
    List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with {alternatives} <;>
    simp only [UpperValid, Prefix.reducedQ, qmul_value, qpow128_value,
      taylorUpper_value, divInt_value] <;>
    norm_num [prefixes, Q.value]'''
    return f'''private theorem band{index:02d}_{name.lower()}Valid
    (cell : Cell) (member : cell ∈ proofBand{index:02d}{name}) :
    UpperValid prefixes[{index}] cell := by
{proof}
'''


def render(index: int, start: int, count: int) -> str:
    first, interior, last = split_band(start, count)
    pieces = ([first] if first else []) + [(chunk, 0, 20) for chunk in interior] + (
        [last] if last else []
    )
    shards = sorted({chunk // 50 for chunk, _, _ in pieces})
    imports = "\n".join(
        f"public import HexInterval.Experiment.PntFks2FamilyData{shard:02d}"
        for shard in shards
    )
    cases = "\n".join(
        f"  | {piece_index} => {source_chunk(chunk, 0, 20)}"
        for piece_index, chunk in enumerate(interior)
    )
    unfolds = ", ".join(f"proofChunk{shard:02d}" for shard in shards)
    alternatives = " | ".join("rfl" for _ in range(20))
    first_expr = "[]" if first is None else source_chunk(*first)
    last_expr = "[]" if last is None else source_chunk(*last)
    first_proof = partial_proof(index, "First", first)
    last_proof = partial_proof(index, "Last", last)
    if not interior:
        chunk_proof = f"  simp [proofBand{index:02d}ChunkCount] at valid"
    else:
        if len(interior) == 1:
            chunk_prelude = (
                f"  simp [proofBand{index:02d}ChunkCount] at valid\n"
                "  subst chunk"
            )
        else:
            chunk_prelude = (
                f"  norm_num [proofBand{index:02d}ChunkCount] at valid\n"
                "  interval_cases chunk"
            )
        chunk_proof = f'''{chunk_prelude} <;>
    simp only [proofBand{index:02d}Chunk, {unfolds}, List.mem_cons,
      List.not_mem_nil, or_false] at member <;>
    rcases member with {alternatives} <;>
    simp only [UpperValid, Prefix.reducedQ, qmul_value, qpow128_value,
      taylorUpper_value, divInt_value] <;>
    norm_num [prefixes, Q.value]'''
    boundary_index = start + count
    member_name = "_member" if not interior else "member"
    boundary_chunk = boundary_index // 20
    boundary_shard = boundary_chunk // 50
    boundary_local = boundary_chunk % 50
    boundary_offset = boundary_index % 20
    return f'''/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexIntervalMathlib.Experiment.PntFks2Xpow
{imports}

@[expose] public section

/-! # Ordinary-kernel certificate for FKS2 inverse-power band {index} -/

namespace Hex.Interval.Experiment.PntFks2Xpow

open PntFks2Shard
open PntFks2Family

def proofBand{index:02d}First : List Cell := {first_expr}

def proofBand{index:02d}Chunk : Nat → List Cell
{cases}
  | _ => []

def proofBand{index:02d}ChunkCount : Nat := {len(interior)}

def proofBand{index:02d}Last : List Cell := {last_expr}

def proofBand{index:02d}Cells : List Cell :=
  proofBand{index:02d}First ++
    (List.range proofBand{index:02d}ChunkCount).flatMap proofBand{index:02d}Chunk ++
    proofBand{index:02d}Last

set_option maxRecDepth 100000 in
theorem proofBand{index:02d}_cells : proofBand{index:02d}Cells = bands[{index}].cells := by
  rfl

set_option maxRecDepth 100000 in
theorem proofBoundary{index:02d}_cell :
    PntFks2Family.allCells[{boundary_index}]? =
      (proofChunk{boundary_shard:02d} {boundary_local})[{boundary_offset}]? := by
  rfl

theorem boundary{index:02d}_lowerValid (cell : Cell)
    (found : (proofChunk{boundary_shard:02d} {boundary_local})[{boundary_offset}]? = some cell) :
    LowerValid prefixes[{index}] cell := by
  norm_num [proofChunk{boundary_shard:02d}] at found
  subst cell
  simp only [LowerValid,
    Prefix.reducedQ, qmul_value, qpow128_value, sumTerms_value, divInt_value]
  norm_num [prefixes, Q.value]

{first_proof}
{last_proof}

set_option maxRecDepth 100000 in
set_option maxHeartbeats 40000000 in
set_option linter.unusedSimpArgs false in
set_option linter.unnecessarySeqFocus false in
private theorem band{index:02d}_chunkValid (chunk : Nat)
    (valid : chunk < proofBand{index:02d}ChunkCount) (cell : Cell)
    ({member_name} : cell ∈ proofBand{index:02d}Chunk chunk) :
    UpperValid prefixes[{index}] cell := by
{chunk_proof}

set_option maxRecDepth 100000 in
theorem band{index:02d}_upperValid (cell : Cell) (member : cell ∈ bands[{index}].cells) :
    UpperValid prefixes[{index}] cell := by
  rw [← proofBand{index:02d}_cells, proofBand{index:02d}Cells] at member
  rcases List.mem_append.mp member with member | member
  · rcases List.mem_append.mp member with member | member
    · exact band{index:02d}_firstValid cell member
    · rw [List.mem_flatMap] at member
      obtain ⟨chunk, chunkMember, cellMember⟩ := member
      exact band{index:02d}_chunkValid chunk (List.mem_range.mp chunkMember) cell cellMember
  · exact band{index:02d}_lastValid cell member

end Hex.Interval.Experiment.PntFks2Xpow

end
'''


def main() -> None:
    output = ROOT / "HexIntervalMathlib" / "Experiment"
    for index, (start, count) in enumerate(BANDS):
        path = output / f"PntFks2XpowProof{index:02d}.lean"
        path.write_text(render(index, start, count))


if __name__ == "__main__":
    main()
