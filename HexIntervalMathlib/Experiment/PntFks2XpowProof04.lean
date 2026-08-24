/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexIntervalMathlib.Experiment.PntFks2Xpow
public import HexInterval.Experiment.PntFks2FamilyData00
public import HexInterval.Experiment.PntFks2FamilyData01

@[expose] public section

/-! # Ordinary-kernel certificate for FKS2 inverse-power band 4 -/

namespace Hex.Interval.Experiment.PntFks2Xpow

open PntFks2Shard
open PntFks2Family

def proofBand04First : List Cell := []

def proofBand04Chunk : Nat → List Cell
  | 0 => proofChunk00 13
  | 1 => proofChunk00 14
  | 2 => proofChunk00 15
  | 3 => proofChunk00 16
  | 4 => proofChunk00 17
  | 5 => proofChunk00 18
  | 6 => proofChunk00 19
  | 7 => proofChunk00 20
  | 8 => proofChunk00 21
  | 9 => proofChunk00 22
  | 10 => proofChunk00 23
  | 11 => proofChunk00 24
  | 12 => proofChunk00 25
  | 13 => proofChunk00 26
  | 14 => proofChunk00 27
  | 15 => proofChunk00 28
  | 16 => proofChunk00 29
  | 17 => proofChunk00 30
  | 18 => proofChunk00 31
  | 19 => proofChunk00 32
  | 20 => proofChunk00 33
  | 21 => proofChunk00 34
  | 22 => proofChunk00 35
  | 23 => proofChunk00 36
  | 24 => proofChunk00 37
  | 25 => proofChunk00 38
  | 26 => proofChunk00 39
  | 27 => proofChunk00 40
  | 28 => proofChunk00 41
  | 29 => proofChunk00 42
  | 30 => proofChunk00 43
  | 31 => proofChunk00 44
  | 32 => proofChunk00 45
  | 33 => proofChunk00 46
  | 34 => proofChunk00 47
  | 35 => proofChunk00 48
  | 36 => proofChunk00 49
  | 37 => proofChunk01 0
  | 38 => proofChunk01 1
  | 39 => proofChunk01 2
  | 40 => proofChunk01 3
  | 41 => proofChunk01 4
  | 42 => proofChunk01 5
  | 43 => proofChunk01 6
  | 44 => proofChunk01 7
  | 45 => proofChunk01 8
  | 46 => proofChunk01 9
  | 47 => proofChunk01 10
  | 48 => proofChunk01 11
  | 49 => proofChunk01 12
  | 50 => proofChunk01 13
  | 51 => proofChunk01 14
  | 52 => proofChunk01 15
  | 53 => proofChunk01 16
  | _ => []

def proofBand04ChunkCount : Nat := 54

def proofBand04Last : List Cell := (proofChunk01 17).take 8

def proofBand04Cells : List Cell :=
  proofBand04First ++
    (List.range proofBand04ChunkCount).flatMap proofBand04Chunk ++
    proofBand04Last

set_option maxRecDepth 100000 in
theorem proofBand04_cells : proofBand04Cells = bands[4].cells := by
  rfl

set_option maxRecDepth 100000 in
theorem proofBoundary04_cell :
    PntFks2Family.allCells[1348]? =
      (proofChunk01 17)[8]? := by
  rfl

theorem boundary04_lowerValid (cell : Cell)
    (found : (proofChunk01 17)[8]? = some cell) :
    LowerValid prefixes[4] cell := by
  norm_num [proofChunk01] at found
  subst cell
  simp only [LowerValid,
    Prefix.reducedQ, qmul_value, qpow128_value, sumTerms_value, divInt_value]
  norm_num [prefixes, Q.value]

private theorem band04_firstValid
    (cell : Cell) (member : cell ∈ proofBand04First) :
    UpperValid prefixes[4] cell := by
  simp [proofBand04First] at member

private theorem band04_lastValid
    (cell : Cell) (member : cell ∈ proofBand04Last) :
    UpperValid prefixes[4] cell := by
  simp only [proofBand04Last, proofChunk01, List.take,
    List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp only [UpperValid, Prefix.reducedQ, qmul_value, qpow128_value,
      taylorUpper_value, divInt_value] <;>
    norm_num [prefixes, Q.value]


set_option maxRecDepth 100000 in
set_option maxHeartbeats 40000000 in
set_option linter.unusedSimpArgs false in
set_option linter.unnecessarySeqFocus false in
private theorem band04_chunkValid (chunk : Nat)
    (valid : chunk < proofBand04ChunkCount) (cell : Cell)
    (member : cell ∈ proofBand04Chunk chunk) :
    UpperValid prefixes[4] cell := by
  norm_num [proofBand04ChunkCount] at valid
  interval_cases chunk <;>
    simp only [proofBand04Chunk, proofChunk00, proofChunk01, List.mem_cons,
      List.not_mem_nil, or_false] at member <;>
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp only [UpperValid, Prefix.reducedQ, qmul_value, qpow128_value,
      taylorUpper_value, divInt_value] <;>
    norm_num [prefixes, Q.value]

set_option maxRecDepth 100000 in
theorem band04_upperValid (cell : Cell) (member : cell ∈ bands[4].cells) :
    UpperValid prefixes[4] cell := by
  rw [← proofBand04_cells, proofBand04Cells] at member
  rcases List.mem_append.mp member with member | member
  · rcases List.mem_append.mp member with member | member
    · exact band04_firstValid cell member
    · rw [List.mem_flatMap] at member
      obtain ⟨chunk, chunkMember, cellMember⟩ := member
      exact band04_chunkValid chunk (List.mem_range.mp chunkMember) cell cellMember
  · exact band04_lastValid cell member

end Hex.Interval.Experiment.PntFks2Xpow

end
