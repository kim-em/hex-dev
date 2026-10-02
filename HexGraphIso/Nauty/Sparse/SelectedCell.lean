/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexGraphIso.Nauty.Sparse.MaxTarget
public import HexGraphIso.Nauty.Sparse.CodePrepare
import all HexGraphIso.Nauty.Sparse.Search
import all HexGraphIso.Nauty.Sparse.Classify
import all HexGraphIso.Nauty.Search.State

public section

namespace Hex.GraphIso.Nauty.Sparse

/-- An enabled native target dispatch returns all three fields of its
actual cached selection, including the saved hint in a negative branch. -/
theorem chooseTarget_fields {g : Graph n} {tcLevel level numcells : Nat}
    {st : State n} (first : Bool) (hc : numcells < n)
    (ho : first = true ∨ st.eqlevFirst = level ∨ 0 ≤ st.compCanon) :
    let t := chooseTarget first g tcLevel level numcells st
    let hint := if !first && st.compCanon < 0 then st.firsttc[level]! else -1
    let c := maketargetCached g st.lab st.ptn level tcLevel hint st.canong.scratch
    (t.1.toNat, t.2.1, t.2.2.1) = (c.1, c.2.1, c.2.2.1) := by
  have hg : (if first then numcells != n
      else numcells < n && (st.eqlevFirst == level || st.compCanon >= 0)) = true := by
    cases first with
    | true => simp [show numcells ≠ n by omega]
    | false =>
      rcases ho with he | he | he
      · cases he
      · simp [hc, he]
      · simp [hc, he]
  dsimp only
  simp only [chooseTarget, hg, ite_true, Id.run_pure, apply_ite Id.run,
    apply_ite Prod.fst, apply_ite Prod.snd, ite_self]
  rfl

/-- Every enabled cached selection is exactly a complete nonsingleton
window of the actual equitable parent, even when the target is hinted. -/
theorem Ready.selected_cell {G : GraphIso.Sparse.Colored n k}
    {tcLevel level numcells : Nat} {st : State n} (h : Ready G level numcells st)
    (hn : 0 < n) (hl : 1 ≤ level) (hc : numcells < n) (first : Bool)
    (ho : first = true ∨ st.eqlevFirst = level ∨ 0 ≤ st.compCanon) :
    let t := chooseTarget first (.ofGraph G.graph) tcLevel level numcells st
    IsCell st.ptn level t.1.toNat t.2.2.1 ∧ 1 < t.2.2.1 ∧ t.1.toNat + t.2.2.1 ≤ n ∧
      t.2.1 = windowSet n st.lab t.1.toNat t.2.2.1 := by
  let hint := if !first && st.compCanon < 0 then st.firsttc[level]! else -1
  have he := chooseTarget_fields (g := .ofGraph G.graph) (tcLevel := tcLevel) first hc ho
  have hw := h.cached_cell hn hl hc tcLevel hint
  have hs := h.target_window hn hl hc tcLevel hint
  have ht := congrArg (fun t : Nat × VSet n × Nat =>
    IsCell st.ptn level t.1 t.2.2 ∧ 1 < t.2.2 ∧ t.1 + t.2.2 ≤ n ∧
      t.2.1 = windowSet n st.lab t.1 t.2.2) he
  rw [ht]
  exact ⟨hw.1, hw.2.1, hw.2.2, hs⟩

/-- An internal classification after target selection certifies that the
selection guard was enabled. A disabled guard leaves the rejected code
and first-reference level unchanged and is classified as bad. -/
theorem chooseTarget_open {g : Graph n} {tcLevel level numcells : Nat} {st : State n}
    (hi : (classify g level numcells
      (chooseTarget false g tcLevel level numcells st).2.2.2).1 = .internal) :
    st.eqlevFirst = level ∨ 0 ≤ st.compCanon := by
  by_cases he : st.eqlevFirst = level
  · exact Or.inl he
  by_cases hp : 0 ≤ st.compCanon
  · exact Or.inr hp
  have hn : st.compCanon < 0 := by omega
  simp [chooseTarget, he, hp, classify_eq, hn] at hi

end Hex.GraphIso.Nauty.Sparse
