/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexIntervalMathlib.Experiment.PntFks2Xpow
public import HexInterval.Experiment.PntFks2FamilyData00

@[expose] public section

/-! # Ordinary-kernel certificate for FKS2 inverse-power band 0 -/

namespace Hex.Interval.Experiment.PntFks2Xpow

open PntFks2Shard
open PntFks2Family

def proofBand00First : List Cell := []

def proofBand00Chunk : Nat → List Cell
  | 0 => proofChunk00 0
  | 1 => proofChunk00 1
  | 2 => proofChunk00 2
  | _ => []

def proofBand00ChunkCount : Nat := 3

def proofBand00Last : List Cell := (proofChunk00 3).take 10

def proofBand00Cells : List Cell :=
  proofBand00First ++
    (List.range proofBand00ChunkCount).flatMap proofBand00Chunk ++
    proofBand00Last

set_option maxRecDepth 100000 in
theorem proofBand00_cells : proofBand00Cells = bands[0].cells := by
  rfl

set_option maxRecDepth 100000 in
theorem proofBoundary00_cell :
    PntFks2Family.allCells[70]? =
      (proofChunk00 3)[10]? := by
  rfl

theorem boundary00_lowerValid (cell : Cell)
    (found : (proofChunk00 3)[10]? = some cell) :
    LowerValid prefixes[0] cell := by
  norm_num [proofChunk00] at found
  subst cell
  simp only [LowerValid,
    Prefix.reducedQ, qmul_value, qpow128_value, sumTerms_value, divInt_value]
  norm_num [prefixes, Q.value]

private theorem band00_firstValid
    (cell : Cell) (member : cell ∈ proofBand00First) :
    UpperValid prefixes[0] cell := by
  simp [proofBand00First] at member

private theorem band00_lastValid
    (cell : Cell) (member : cell ∈ proofBand00Last) :
    UpperValid prefixes[0] cell := by
  simp only [proofBand00Last, proofChunk00, List.take,
    List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp only [UpperValid, Prefix.reducedQ, qmul_value, qpow128_value,
      taylorUpper_value, divInt_value] <;>
    norm_num [prefixes, Q.value]


set_option maxRecDepth 100000 in
set_option maxHeartbeats 40000000 in
set_option linter.unusedSimpArgs false in
set_option linter.unnecessarySeqFocus false in
private theorem band00_chunkValid (chunk : Nat)
    (valid : chunk < proofBand00ChunkCount) (cell : Cell)
    (member : cell ∈ proofBand00Chunk chunk) :
    UpperValid prefixes[0] cell := by
  norm_num [proofBand00ChunkCount] at valid
  interval_cases chunk <;>
    simp only [proofBand00Chunk, proofChunk00, List.mem_cons,
      List.not_mem_nil, or_false] at member <;>
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp only [UpperValid, Prefix.reducedQ, qmul_value, qpow128_value,
      taylorUpper_value, divInt_value] <;>
    norm_num [prefixes, Q.value]

set_option maxRecDepth 100000 in
theorem band00_upperValid (cell : Cell) (member : cell ∈ bands[0].cells) :
    UpperValid prefixes[0] cell := by
  rw [← proofBand00_cells, proofBand00Cells] at member
  rcases List.mem_append.mp member with member | member
  · rcases List.mem_append.mp member with member | member
    · exact band00_firstValid cell member
    · rw [List.mem_flatMap] at member
      obtain ⟨chunk, chunkMember, cellMember⟩ := member
      exact band00_chunkValid chunk (List.mem_range.mp chunkMember) cell cellMember
  · exact band00_lastValid cell member

end Hex.Interval.Experiment.PntFks2Xpow

end
