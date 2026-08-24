/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexIntervalMathlib.Experiment.PntFks2Xpow
public import HexInterval.Experiment.PntFks2FamilyData00

@[expose] public section

/-! # Ordinary-kernel certificate for FKS2 inverse-power band 2 -/

namespace Hex.Interval.Experiment.PntFks2Xpow

open PntFks2Shard
open PntFks2Family

def proofBand02First : List Cell := (proofChunk00 4).drop 17

def proofBand02Chunk : Nat → List Cell
  | 0 => proofChunk00 5
  | _ => []

def proofBand02ChunkCount : Nat := 1

def proofBand02Last : List Cell := (proofChunk00 6).take 4

def proofBand02Cells : List Cell :=
  proofBand02First ++
    (List.range proofBand02ChunkCount).flatMap proofBand02Chunk ++
    proofBand02Last

set_option maxRecDepth 100000 in
theorem proofBand02_cells : proofBand02Cells = bands[2].cells := by
  rfl

set_option maxRecDepth 100000 in
theorem proofBoundary02_cell :
    PntFks2Family.allCells[124]? =
      (proofChunk00 6)[4]? := by
  rfl

theorem boundary02_lowerValid (cell : Cell)
    (found : (proofChunk00 6)[4]? = some cell) :
    LowerValid prefixes[2] cell := by
  norm_num [proofChunk00] at found
  subst cell
  simp only [LowerValid,
    Prefix.reducedQ, qmul_value, qpow128_value, sumTerms_value, divInt_value]
  norm_num [prefixes, Q.value]

private theorem band02_firstValid
    (cell : Cell) (member : cell ∈ proofBand02First) :
    UpperValid prefixes[2] cell := by
  simp only [proofBand02First, proofChunk00, List.drop,
    List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl <;>
    simp only [UpperValid, Prefix.reducedQ, qmul_value, qpow128_value,
      taylorUpper_value, divInt_value] <;>
    norm_num [prefixes, Q.value]

private theorem band02_lastValid
    (cell : Cell) (member : cell ∈ proofBand02Last) :
    UpperValid prefixes[2] cell := by
  simp only [proofBand02Last, proofChunk00, List.take,
    List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl <;>
    simp only [UpperValid, Prefix.reducedQ, qmul_value, qpow128_value,
      taylorUpper_value, divInt_value] <;>
    norm_num [prefixes, Q.value]


set_option maxRecDepth 100000 in
set_option maxHeartbeats 40000000 in
set_option linter.unusedSimpArgs false in
set_option linter.unnecessarySeqFocus false in
private theorem band02_chunkValid (chunk : Nat)
    (valid : chunk < proofBand02ChunkCount) (cell : Cell)
    (member : cell ∈ proofBand02Chunk chunk) :
    UpperValid prefixes[2] cell := by
  simp [proofBand02ChunkCount] at valid
  subst chunk <;>
    simp only [proofBand02Chunk, proofChunk00, List.mem_cons,
      List.not_mem_nil, or_false] at member <;>
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp only [UpperValid, Prefix.reducedQ, qmul_value, qpow128_value,
      taylorUpper_value, divInt_value] <;>
    norm_num [prefixes, Q.value]

set_option maxRecDepth 100000 in
theorem band02_upperValid (cell : Cell) (member : cell ∈ bands[2].cells) :
    UpperValid prefixes[2] cell := by
  rw [← proofBand02_cells, proofBand02Cells] at member
  rcases List.mem_append.mp member with member | member
  · rcases List.mem_append.mp member with member | member
    · exact band02_firstValid cell member
    · rw [List.mem_flatMap] at member
      obtain ⟨chunk, chunkMember, cellMember⟩ := member
      exact band02_chunkValid chunk (List.mem_range.mp chunkMember) cell cellMember
  · exact band02_lastValid cell member

end Hex.Interval.Experiment.PntFks2Xpow

end
