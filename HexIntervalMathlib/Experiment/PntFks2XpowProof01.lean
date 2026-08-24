/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexIntervalMathlib.Experiment.PntFks2Xpow
public import HexInterval.Experiment.PntFks2FamilyData00

@[expose] public section

/-! # Ordinary-kernel certificate for FKS2 inverse-power band 1 -/

namespace Hex.Interval.Experiment.PntFks2Xpow

open PntFks2Shard
open PntFks2Family

def proofBand01First : List Cell := (proofChunk00 3).drop 10

def proofBand01Chunk : Nat → List Cell

  | _ => []

def proofBand01ChunkCount : Nat := 0

def proofBand01Last : List Cell := (proofChunk00 4).take 17

def proofBand01Cells : List Cell :=
  proofBand01First ++
    (List.range proofBand01ChunkCount).flatMap proofBand01Chunk ++
    proofBand01Last

set_option maxRecDepth 100000 in
theorem proofBand01_cells : proofBand01Cells = bands[1].cells := by
  rfl

set_option maxRecDepth 100000 in
theorem proofBoundary01_cell :
    PntFks2Family.allCells[97]? =
      (proofChunk00 4)[17]? := by
  rfl

theorem boundary01_lowerValid (cell : Cell)
    (found : (proofChunk00 4)[17]? = some cell) :
    LowerValid prefixes[1] cell := by
  norm_num [proofChunk00] at found
  subst cell
  simp only [LowerValid,
    Prefix.reducedQ, qmul_value, qpow128_value, sumTerms_value, divInt_value]
  norm_num [prefixes, Q.value]

private theorem band01_firstValid
    (cell : Cell) (member : cell ∈ proofBand01First) :
    UpperValid prefixes[1] cell := by
  simp only [proofBand01First, proofChunk00, List.drop,
    List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp only [UpperValid, Prefix.reducedQ, qmul_value, qpow128_value,
      taylorUpper_value, divInt_value] <;>
    norm_num [prefixes, Q.value]

private theorem band01_lastValid
    (cell : Cell) (member : cell ∈ proofBand01Last) :
    UpperValid prefixes[1] cell := by
  simp only [proofBand01Last, proofChunk00, List.take,
    List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp only [UpperValid, Prefix.reducedQ, qmul_value, qpow128_value,
      taylorUpper_value, divInt_value] <;>
    norm_num [prefixes, Q.value]


set_option maxRecDepth 100000 in
set_option maxHeartbeats 40000000 in
set_option linter.unusedSimpArgs false in
set_option linter.unnecessarySeqFocus false in
private theorem band01_chunkValid (chunk : Nat)
    (valid : chunk < proofBand01ChunkCount) (cell : Cell)
    (_member : cell ∈ proofBand01Chunk chunk) :
    UpperValid prefixes[1] cell := by
  simp [proofBand01ChunkCount] at valid

set_option maxRecDepth 100000 in
theorem band01_upperValid (cell : Cell) (member : cell ∈ bands[1].cells) :
    UpperValid prefixes[1] cell := by
  rw [← proofBand01_cells, proofBand01Cells] at member
  rcases List.mem_append.mp member with member | member
  · rcases List.mem_append.mp member with member | member
    · exact band01_firstValid cell member
    · rw [List.mem_flatMap] at member
      obtain ⟨chunk, chunkMember, cellMember⟩ := member
      exact band01_chunkValid chunk (List.mem_range.mp chunkMember) cell cellMember
  · exact band01_lastValid cell member

end Hex.Interval.Experiment.PntFks2Xpow

end
