/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexGraphIso.Nauty.Sparse.Refine
public import HexGraphIso.Nauty.Sparse.SortProps
import Std.Tactic.Do

public section

namespace Hex.GraphIso.Nauty.Sparse

/-- Storage unaffected by dividing a cell using already computed counts.
The label, partition, and index contents may change, but keep their allocation. -/
structure CountFrame (s t : RefineSt n) : Prop where
  lab_size : t.lab.size = s.lab.size
  ptn_size : t.ptn.size = s.ptn.size
  starts_size : t.cellstart.size = s.cellstart.size
  ends_size : t.cellend.size = s.cellend.size
  hits : t.hits = s.hits
  marks : t.marks = s.marks
  vmarks : t.vmarks = s.vmarks
  stamp : t.stamp = s.stamp
  indexed : t.indexed = s.indexed

open Std.Do
set_option mvcgen.warning false
set_option maxHeartbeats 2000000

/-- All branches of the actual count splitter retain their count and mark
arrays, generation, cache flag, and label/partition/index allocations. -/
theorem splitCounts_frame (level first : Nat) (distance : Bool) (s : RefineSt n) :
    CountFrame s (splitCounts level first distance s) := by
  unfold splitCounts CountSort.firstRun CountSort.minima CountSort.finish
  simp only [Id.run]
  apply Id.of_wp_run_eq rfl (fun t : RefineSt n => CountFrame s t)
  mvcgen
  all_goals first
    | exact (⇓⟨_, state⟩ => ⌜CountFrame s state.1⌝)
    | exact (⇓⟨_, state⟩ => ⌜state.2.2.2.2.size = s.lab.size⌝)
    | exact (⇓⟨_, state⟩ => ⌜state.size = s.cellstart.size⌝)
    | exact (⇓⟨_, _⟩ => ⌜True⌝)
    | skip
  all_goals
    simp_all +zetaDelta [RefineSt.hash, RefineSt.push] <;>
      grind [CountFrame, Sort.indirect_size]

end Hex.GraphIso.Nauty.Sparse
