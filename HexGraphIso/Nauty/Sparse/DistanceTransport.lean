/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexGraphIso.Nauty.Sparse.DistanceEquiv

public section

namespace Hex.GraphIso.Nauty.Sparse

/-- The complete literal distance-cell loop preserves all refinement
observations under renaming, given transported native distances. -/
theorem split_distances_equiv (σ : Renaming n) (level : Nat) (s t : RefineSt n)
    (hs : RefineSt.Valid level s) (ht : RefineSt.Valid level t)
    (hv : ∀ v, v < n → s.hits[v]! ≤ n) (hw : ∀ v, v < n → t.hits[v]! ≤ n)
    (hkeys : ∀ v, v < n → t.hits[σ v]! = s.hits[v]!)
    (he : RefineSt.Equiv σ level s t) :
    let run (s : RefineSt n) := Id.run do
      let mut state := s
      let mut first := 0
      for _ in [0:n] do
        if first >= n then break
        let last := state.cellend[first]!
        if first < last then state := splitCounts level first true state
        first := last + 1
      return state
    RefineSt.Equiv σ level (run s) (run t) := by
  let step (_ : Nat) (x : RefineSt n × Nat) : Id (ForInStep (RefineSt n × Nat)) :=
    if x.2 ≥ n then .done x else
      let last := x.1.cellend[x.2]!
      if x.2 < last then .yield (splitCounts level x.2 true x.1, last + 1)
      else .yield (x.1, last + 1)
  have hr := Loop.range_rel n step step (DistanceState.Rel σ level s t) (by
    intro _x a b h
    rcases a with ⟨a, first⟩
    rcases b with ⟨b, other⟩
    rcases h with ⟨ha, hb, hpos, he⟩
    dsimp only at hpos
    subst other
    exact DistanceState.step_rel σ level first s t a b hs ht hv hw hkeys ha hb he)
    (show DistanceState.Rel σ level s t (s, 0) (t, 0) from
      ⟨DistanceState.initial hs, DistanceState.initial ht, rfl, he⟩)
  exact hr.2.2.2

end Hex.GraphIso.Nauty.Sparse
