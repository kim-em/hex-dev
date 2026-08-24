/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexIntervalMathlib.Experiment.PntFks2Xpow
public import HexInterval.Experiment.PntFks2FamilyData00

@[expose] public section

/-! # Ordinary-kernel certificate for FKS2 inverse-power band 3 -/

namespace Hex.Interval.Experiment.PntFks2Xpow

open PntFks2Shard
open PntFks2Family

def proofBand03First : List Cell := (proofChunk00 6).drop 4

def proofBand03Chunk : Nat → List Cell
  | 0 => proofChunk00 7
  | 1 => proofChunk00 8
  | 2 => proofChunk00 9
  | 3 => proofChunk00 10
  | 4 => proofChunk00 11
  | 5 => proofChunk00 12
  | _ => []

def proofBand03ChunkCount : Nat := 6

def proofBand03Last : List Cell := []

def proofBand03Cells : List Cell :=
  proofBand03First ++
    (List.range proofBand03ChunkCount).flatMap proofBand03Chunk ++
    proofBand03Last

set_option maxRecDepth 100000 in
theorem proofBand03_cells : proofBand03Cells = bands[3].cells := by
  rfl

set_option maxRecDepth 100000 in
theorem proofBoundary03_cell :
    PntFks2Family.allCells[260]? =
      (proofChunk00 13)[0]? := by
  rfl

theorem boundary03_lowerValid (cell : Cell)
    (found : (proofChunk00 13)[0]? = some cell) :
    LowerValid prefixes[3] cell := by
  norm_num [proofChunk00] at found
  subst cell
  simp only [LowerValid,
    Prefix.reducedQ, qmul_value, qpow128_value, sumTerms_value, divInt_value]
  norm_num [prefixes, Q.value]

private theorem band03_firstValid
    (cell : Cell) (member : cell ∈ proofBand03First) :
    UpperValid prefixes[3] cell := by
  simp only [proofBand03First, proofChunk00, List.drop,
    List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp only [UpperValid, Prefix.reducedQ, qmul_value, qpow128_value,
      taylorUpper_value, divInt_value] <;>
    norm_num [prefixes, Q.value]

private theorem band03_lastValid
    (cell : Cell) (member : cell ∈ proofBand03Last) :
    UpperValid prefixes[3] cell := by
  simp [proofBand03Last] at member


set_option maxRecDepth 100000 in
set_option maxHeartbeats 40000000 in
set_option linter.unusedSimpArgs false in
set_option linter.unnecessarySeqFocus false in
private theorem band03_chunkValid (chunk : Nat)
    (valid : chunk < proofBand03ChunkCount) (cell : Cell)
    (member : cell ∈ proofBand03Chunk chunk) :
    UpperValid prefixes[3] cell := by
  norm_num [proofBand03ChunkCount] at valid
  interval_cases chunk <;>
    simp only [proofBand03Chunk, proofChunk00, List.mem_cons,
      List.not_mem_nil, or_false] at member <;>
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp only [UpperValid, Prefix.reducedQ, qmul_value, qpow128_value,
      taylorUpper_value, divInt_value] <;>
    norm_num [prefixes, Q.value]

set_option maxRecDepth 100000 in
theorem band03_upperValid (cell : Cell) (member : cell ∈ bands[3].cells) :
    UpperValid prefixes[3] cell := by
  rw [← proofBand03_cells, proofBand03Cells] at member
  rcases List.mem_append.mp member with member | member
  · rcases List.mem_append.mp member with member | member
    · exact band03_firstValid cell member
    · rw [List.mem_flatMap] at member
      obtain ⟨chunk, chunkMember, cellMember⟩ := member
      exact band03_chunkValid chunk (List.mem_range.mp chunkMember) cell cellMember
  · exact band03_lastValid cell member

end Hex.Interval.Experiment.PntFks2Xpow

end
