/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexGraphIso.Nauty.Sparse.DistanceState
import Std.Tactic.Do

public section

namespace Hex.GraphIso.Nauty.Sparse

open Std.Do
set_option mvcgen.warning false

/-- The literal distance-cell loop reaches the end of the partition and
establishes constant distance keys and the fragment activation rule everywhere. -/
theorem split_distances (level : Nat) (s : RefineSt n) (h : RefineSt.Valid level s)
    (hv : ∀ v, v < n → s.hits[v]! ≤ n) :
    let t : RefineSt n := Id.run do
      let mut state := s
      let mut first := 0
      for _ in [0:n] do
        if first >= n then break
        let last := state.cellend[first]!
        if first < last then state := splitCounts level first true state
        first := last + 1
      return state
    DistanceState level s t n := by
  apply Id.of_wp_run_eq rfl (fun t : RefineSt n => DistanceState level s t n)
  mvcgen
  case inv1 =>
    exact (⇓⟨cursor, state⟩ => ⌜DistanceState level s state.1 state.2 ∧ cursor.prefix.length ≤ state.2⌝)
  all_goals simp +zetaDelta [Std.Legacy.Range.toList] at *
  case vc1.step.isTrue =>
    rename_i hin hb
    exact ⟨hin.1, hb⟩
  case vc2.step.isFalse.isTrue =>
    rename_i hin hf
    have hcell := hin.1.cell hf
    exact ⟨hin.1.counts h hv hf, by omega⟩
  case vc3.step.isFalse.isFalse =>
    rename_i hin hf hc
    have hcell := hin.1.cell hf
    have he := Nat.le_antisymm hc hcell.2.1
    simpa only [he] using And.intro (hin.1.singleton hf he) hin.2
  case vc4.pre => exact DistanceState.initial h
  case vc5.post.success =>
    rename_i hin
    have he := Nat.le_antisymm hin.1.bound hin.2
    simpa only [he] using hin.1

end Hex.GraphIso.Nauty.Sparse
