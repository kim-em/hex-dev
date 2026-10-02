/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexGraphIso.Nauty.Sparse.CanonControl
public import HexGraphIso.Nauty.Sparse.Controls
public import HexGraphIso.Nauty.Sparse.ComparisonOps
public import HexGraphIso.Nauty.Policy.Generic.ExitBound
public import HexGraphIso.Nauty.Policy.Filters
import all HexGraphIso.Nauty.Policy.Generic.ExitBound
import all HexGraphIso.Nauty.Policy.Controls
import all HexGraphIso.Nauty.Search.Generic
import all HexGraphIso.Nauty.Search.State

public section

namespace Hex.GraphIso.Nauty.Sparse

/-- Actual off-path preparation retains both saved ancestors and the cheap
boundary. Its leaf therefore returns strictly above the entered node. -/
theorem prepared_bound {g : Graph n} {tcLevel level numcells target : Nat}
    {short : Bool} {st : State n} (hf : st.gcaFirst < level) (hc : st.gcaCanon < level)
    (hb : st.noncheaplevel ≤ level) :
    let p := prepareOther g tcLevel level numcells st
    let c := classify g level p.1 p.2.2.2.2.2
    (leafExit c.1 level c.2).1 = .unwind target short → target < level := by
  intro p c he
  apply leafExit_bound (st := c.2) (leaf := c.1) ?_ ?_ ?_ he
  · change (classify g level p.1 p.2.2.2.2.2).2.gcaFirst < level
    rw [(classify_controls g level p.1 p.2.2.2.2.2).1]
    change (chooseTarget false g tcLevel level _ (compareCodes level _ _)).2.2.2.gcaFirst < level
    rw [(chooseTarget_controls false g tcLevel level _ _).1]
    have hr := (gcaPolicy g 0 tcLevel).compare level
      (visit g level numcells st).2.1 (visit g level numcells st).2.2
    change (compareCodes level _ _).gcaFirst = st.gcaFirst at hr
    rw [hr]
    exact hf
  · change (classify g level p.1 p.2.2.2.2.2).2.gcaCanon < level
    rw [classify_ancestor]
    change (chooseTarget false g tcLevel level _ (compareCodes level _ _)).2.2.2.gcaCanon < level
    rw [chooseTarget_ancestor, compare_canon]
    exact hc
  · change (classify g level p.1 p.2.2.2.2.2).2.noncheaplevel ≤ level
    rw [(classify_controls g level p.1 p.2.2.2.2.2).2]
    change (chooseTarget false g tcLevel level _ (compareCodes level _ _)).2.2.2.noncheaplevel ≤ level
    rw [(chooseTarget_controls false g tcLevel level _ _).2]
    unfold compareCodes
    simp only [Id.run_pure, apply_ite Id.run, apply_ite SearchState.noncheaplevel, ite_self]
    exact hb

/-- A complete off-path node unwinds to a strict ancestor. This bound
comes from the actual native leaf rules and generic sweep control flow. -/
theorem node_bound (g : Graph n) (inf tcLevel fuel level numcells : Nat) (st : State n)
    (hl : 1 ≤ level) (hf : st.gcaFirst < level) (hc : st.gcaCanon < level)
    (hb : st.noncheaplevel ≤ level) :
    ∀ target short, (Generic.node false g inf tcLevel fuel level numcells st).1 =
      .unwind target short → target < level := by
  cases fuel with
  | zero => simp [Generic.node]
  | succ fuel =>
    rw [Generic.node]
    apply Generic.bound_node (fuel := fuel) ?_ g tcLevel false level numcells st hl
    · intro _
      dsimp only
      intro target short he
      exact prepared_bound hf hc hb he
    · intro first level numcells tc tv1 cursor cell index st _
      exact Generic.sweep_bound first g inf tcLevel fuel (n + 1)
        level numcells tc tv1 cursor cell index st

/-- The first-path terminal rule and sweep also return strictly above
their node, without any installed reference premises. -/
theorem first_node_bound (g : Graph n) (inf tcLevel fuel level numcells : Nat)
    (st : State n) (hl : 1 ≤ level) :
    ∀ target short, (Generic.node true g inf tcLevel fuel level numcells st).1 =
      .unwind target short → target < level := by
  cases fuel with
  | zero => simp [Generic.node]
  | succ fuel =>
    rw [Generic.node]
    apply Generic.bound_node (fuel := fuel) ?_ g tcLevel true level numcells st hl
    · intro he; cases he
    · intro first level numcells tc tv1 cursor cell index st _
      exact Generic.sweep_bound first g inf tcLevel fuel (n + 1)
        level numcells tc tv1 cursor cell index st

/-- A received child return targets this exact parent; it cannot point
strictly between consecutive levels. -/
theorem child_target {g : Graph n} {inf tcLevel fuel level numcells tc tv target : Nat}
    {first childFirst : Bool} {st : State n} {short : Bool}
    (hf : st.gcaFirst ≤ level) (hc : st.gcaCanon ≤ level) (hb : st.noncheaplevel ≤ level + 1)
    (he : (Generic.node childFirst g inf tcLevel fuel (level + 1) (numcells + 1)
      ((policy (n := n)).child first level tc tv st)).1 = .unwind target short)
    (hr : level ≤ target) : target = level := by
  have hbound : target < level + 1 := by
    cases childFirst with
    | true => exact first_node_bound g inf tcLevel fuel (level + 1) (numcells + 1) _ (by omega) _ _ he
    | false =>
      apply node_bound g inf tcLevel fuel (level + 1) (numcells + 1) _ (by omega) _ _ _ target short he
      · cases first <;> change st.gcaFirst < level + 1 <;> omega
      · cases first <;> change st.gcaCanon < level + 1 <;> omega
      · cases first <;> exact hb
  omega

end Hex.GraphIso.Nauty.Sparse
