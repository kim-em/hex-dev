/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexIntervalMathlib.Experiment.PntFks2Xpow
public import HexInterval.Experiment.PntFks2FamilyData01
public import HexInterval.Experiment.PntFks2FamilyData02
public import HexInterval.Experiment.PntFks2FamilyData03

@[expose] public section

/-! # Ordinary-kernel certificate for FKS2 inverse-power band 5 -/

namespace Hex.Interval.Experiment.PntFks2Xpow

open PntFks2Shard
open PntFks2Family

def proofBand05First : List Cell := (proofChunk01 17).drop 8

def proofBand05Chunk : Nat → List Cell
  | 0 => proofChunk01 18
  | 1 => proofChunk01 19
  | 2 => proofChunk01 20
  | 3 => proofChunk01 21
  | 4 => proofChunk01 22
  | 5 => proofChunk01 23
  | 6 => proofChunk01 24
  | 7 => proofChunk01 25
  | 8 => proofChunk01 26
  | 9 => proofChunk01 27
  | 10 => proofChunk01 28
  | 11 => proofChunk01 29
  | 12 => proofChunk01 30
  | 13 => proofChunk01 31
  | 14 => proofChunk01 32
  | 15 => proofChunk01 33
  | 16 => proofChunk01 34
  | 17 => proofChunk01 35
  | 18 => proofChunk01 36
  | 19 => proofChunk01 37
  | 20 => proofChunk01 38
  | 21 => proofChunk01 39
  | 22 => proofChunk01 40
  | 23 => proofChunk01 41
  | 24 => proofChunk01 42
  | 25 => proofChunk01 43
  | 26 => proofChunk01 44
  | 27 => proofChunk01 45
  | 28 => proofChunk01 46
  | 29 => proofChunk01 47
  | 30 => proofChunk01 48
  | 31 => proofChunk01 49
  | 32 => proofChunk02 0
  | 33 => proofChunk02 1
  | 34 => proofChunk02 2
  | 35 => proofChunk02 3
  | 36 => proofChunk02 4
  | 37 => proofChunk02 5
  | 38 => proofChunk02 6
  | 39 => proofChunk02 7
  | 40 => proofChunk02 8
  | 41 => proofChunk02 9
  | 42 => proofChunk02 10
  | 43 => proofChunk02 11
  | 44 => proofChunk02 12
  | 45 => proofChunk02 13
  | 46 => proofChunk02 14
  | 47 => proofChunk02 15
  | 48 => proofChunk02 16
  | 49 => proofChunk02 17
  | 50 => proofChunk02 18
  | 51 => proofChunk02 19
  | 52 => proofChunk02 20
  | 53 => proofChunk02 21
  | 54 => proofChunk02 22
  | 55 => proofChunk02 23
  | 56 => proofChunk02 24
  | 57 => proofChunk02 25
  | 58 => proofChunk02 26
  | 59 => proofChunk02 27
  | 60 => proofChunk02 28
  | 61 => proofChunk02 29
  | 62 => proofChunk02 30
  | 63 => proofChunk02 31
  | 64 => proofChunk02 32
  | 65 => proofChunk02 33
  | 66 => proofChunk02 34
  | 67 => proofChunk02 35
  | 68 => proofChunk02 36
  | 69 => proofChunk02 37
  | 70 => proofChunk02 38
  | 71 => proofChunk02 39
  | 72 => proofChunk02 40
  | 73 => proofChunk02 41
  | 74 => proofChunk02 42
  | 75 => proofChunk02 43
  | 76 => proofChunk02 44
  | 77 => proofChunk02 45
  | 78 => proofChunk02 46
  | 79 => proofChunk02 47
  | 80 => proofChunk02 48
  | 81 => proofChunk02 49
  | 82 => proofChunk03 0
  | 83 => proofChunk03 1
  | 84 => proofChunk03 2
  | 85 => proofChunk03 3
  | 86 => proofChunk03 4
  | 87 => proofChunk03 5
  | 88 => proofChunk03 6
  | 89 => proofChunk03 7
  | 90 => proofChunk03 8
  | 91 => proofChunk03 9
  | 92 => proofChunk03 10
  | 93 => proofChunk03 11
  | 94 => proofChunk03 12
  | 95 => proofChunk03 13
  | 96 => proofChunk03 14
  | 97 => proofChunk03 15
  | 98 => proofChunk03 16
  | 99 => proofChunk03 17
  | 100 => proofChunk03 18
  | 101 => proofChunk03 19
  | 102 => proofChunk03 20
  | 103 => proofChunk03 21
  | 104 => proofChunk03 22
  | 105 => proofChunk03 23
  | 106 => proofChunk03 24
  | 107 => proofChunk03 25
  | 108 => proofChunk03 26
  | 109 => proofChunk03 27
  | 110 => proofChunk03 28
  | 111 => proofChunk03 29
  | 112 => proofChunk03 30
  | 113 => proofChunk03 31
  | 114 => proofChunk03 32
  | 115 => proofChunk03 33
  | 116 => proofChunk03 34
  | 117 => proofChunk03 35
  | 118 => proofChunk03 36
  | _ => []

def proofBand05ChunkCount : Nat := 119

def proofBand05Last : List Cell := (proofChunk03 37).take 6

def proofBand05Cells : List Cell :=
  proofBand05First ++
    (List.range proofBand05ChunkCount).flatMap proofBand05Chunk ++
    proofBand05Last

set_option maxRecDepth 100000 in
theorem proofBand05_cells : proofBand05Cells = bands[5].cells := by
  rfl

set_option maxRecDepth 100000 in
theorem proofBoundary05_cell :
    PntFks2Family.allCells[3746]? =
      (proofChunk03 37)[6]? := by
  rfl

theorem boundary05_lowerValid (cell : Cell)
    (found : (proofChunk03 37)[6]? = some cell) :
    LowerValid prefixes[5] cell := by
  norm_num [proofChunk03] at found
  subst cell
  simp only [LowerValid,
    Prefix.reducedQ, qmul_value, qpow128_value, sumTerms_value, divInt_value]
  norm_num [prefixes, Q.value]

private theorem band05_firstValid
    (cell : Cell) (member : cell ∈ proofBand05First) :
    UpperValid prefixes[5] cell := by
  simp only [proofBand05First, proofChunk01, List.drop,
    List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp only [UpperValid, Prefix.reducedQ, qmul_value, qpow128_value,
      taylorUpper_value, divInt_value] <;>
    norm_num [prefixes, Q.value]

private theorem band05_lastValid
    (cell : Cell) (member : cell ∈ proofBand05Last) :
    UpperValid prefixes[5] cell := by
  simp only [proofBand05Last, proofChunk03, List.take,
    List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp only [UpperValid, Prefix.reducedQ, qmul_value, qpow128_value,
      taylorUpper_value, divInt_value] <;>
    norm_num [prefixes, Q.value]


set_option maxRecDepth 100000 in
set_option maxHeartbeats 40000000 in
set_option linter.unusedSimpArgs false in
set_option linter.unnecessarySeqFocus false in
private theorem band05_chunkValid (chunk : Nat)
    (valid : chunk < proofBand05ChunkCount) (cell : Cell)
    (member : cell ∈ proofBand05Chunk chunk) :
    UpperValid prefixes[5] cell := by
  norm_num [proofBand05ChunkCount] at valid
  interval_cases chunk <;>
    simp only [proofBand05Chunk, proofChunk01, proofChunk02, proofChunk03, List.mem_cons,
      List.not_mem_nil, or_false] at member <;>
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp only [UpperValid, Prefix.reducedQ, qmul_value, qpow128_value,
      taylorUpper_value, divInt_value] <;>
    norm_num [prefixes, Q.value]

set_option maxRecDepth 100000 in
theorem band05_upperValid (cell : Cell) (member : cell ∈ bands[5].cells) :
    UpperValid prefixes[5] cell := by
  rw [← proofBand05_cells, proofBand05Cells] at member
  rcases List.mem_append.mp member with member | member
  · rcases List.mem_append.mp member with member | member
    · exact band05_firstValid cell member
    · rw [List.mem_flatMap] at member
      obtain ⟨chunk, chunkMember, cellMember⟩ := member
      exact band05_chunkValid chunk (List.mem_range.mp chunkMember) cell cellMember
  · exact band05_lastValid cell member

end Hex.Interval.Experiment.PntFks2Xpow

end
