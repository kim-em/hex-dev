/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexIntervalMathlib.Experiment.PntFks2Shard
public import HexInterval.Experiment.PntFks2FamilyData04

@[expose] public section

/-! # Kernel certificate for pinned FKS2 shard 04 -/

namespace Hex.Interval.Experiment.PntFks2Family

open PntFks2Shard

set_option maxRecDepth 100000 in
set_option maxHeartbeats 20000000 in
theorem chunk04_valid (index : Nat) (valid : index < proofChunkCount04)
    (cell : Cell) (member : cell ∈ proofChunk04 index) : CellValid cell := by
  norm_num [proofChunkCount04] at valid
  interval_cases index <;>
    simp only [proofChunk04, List.mem_cons, List.not_mem_nil, or_false] at member <;>
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp only [CellValid, qmul_value, qpow_value, qpow128_value,
      taylorUpper_value] <;>
    norm_num [Q.value, cq128, aq]

/-- Exact source-shaped executable check for pinned shard 04. -/
theorem cells04_checked : cells04.all checkCell = true := by
  exact List.all_eq_true.mpr fun cell member => by
    rw [cells04, List.mem_flatMap] at member
    obtain ⟨index, indexMember, cellMember⟩ := member
    exact check_of_valid cell (chunk04_valid index
      (List.mem_range.mp indexMember) cell cellMember)

/-- Arbitrary-membership semantic wrapper for pinned shard 04. -/
theorem cells04_holds (cell : Cell) (member : cell ∈ cells04) :
    CellHolds cell :=
  cellHolds_of_check cell (List.all_eq_true.mp cells04_checked cell member)

end Hex.Interval.Experiment.PntFks2Family
