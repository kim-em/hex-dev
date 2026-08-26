/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexIntervalMathlib.Experiment.PntFks2Shard
public import HexInterval.Experiment.PntFks2FamilyData08

@[expose] public section

/-! # Kernel certificate for pinned FKS2 shard 08 -/

namespace Hex.Interval.Experiment.PntFks2Family

open PntFks2Shard

set_option maxRecDepth 100000 in
set_option maxHeartbeats 20000000 in
theorem chunk08_valid (index : Nat) (valid : index < proofChunkCount08)
    (cell : Cell) (member : cell ∈ proofChunk08 index) : CellValid cell := by
  norm_num [proofChunkCount08] at valid
  interval_cases index <;>
    simp only [proofChunk08, List.mem_cons, List.not_mem_nil, or_false] at member <;>
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp only [CellValid, qmul_value, qpow_value, qpow128_value,
      taylorUpper_value] <;>
    norm_num [Q.value, cq128, aq]

/-- Exact source-shaped executable check for pinned shard 08. -/
theorem cells08_checked : cells08.all checkCell = true := by
  exact List.all_eq_true.mpr fun cell member => by
    rw [cells08, List.mem_flatMap] at member
    obtain ⟨index, indexMember, cellMember⟩ := member
    exact check_of_valid cell (chunk08_valid index
      (List.mem_range.mp indexMember) cell cellMember)

/-- Arbitrary-membership semantic wrapper for pinned shard 08. -/
theorem cells08_holds (cell : Cell) (member : cell ∈ cells08) :
    CellHolds cell :=
  cellHolds_of_check cell (List.all_eq_true.mp cells08_checked cell member)

end Hex.Interval.Experiment.PntFks2Family
