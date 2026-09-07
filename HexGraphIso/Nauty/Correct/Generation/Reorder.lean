/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexGraphIso.Nauty.Correct.Generation.Coverage
public import HexGraphIso.Nauty.Correct.Generation.RefPath

public section

namespace Hex.GraphIso.Nauty.Generation

variable {n : Nat} {ctx : Ctx n}

private def identity (n : Nat) : Renaming n := ⟨id, fun _ _ h => h, fun _ => Iff.rfl⟩

private theorem identity_rows (hsize : ctx.g.size = n) : RowsMap (identity n) ctx.g ctx.g := by
  refine ⟨hsize, hsize, ?_⟩
  intro v _
  exact (image_id _).symm

private theorem identity_state (st : RefineSt n) : mapSt (identity n) st = st := by
  simp [mapSt, identity]

/-- Cell-equivalent refined states have the same reference occurrences,
including the sequence of target positions. -/
theorem HasLeaf.ofPerm {tcLevel level : Nat} {U V : RefineSt n}
    {targets : List Nat} {key : Key n}
    (hsize : ctx.g.size = n) (hok : IterOk ctx level U) (hperm : StPerm level V U)
    (h : HasLeaf ctx tcLevel level U targets key) : HasLeaf ctx tcLevel level V targets key :=
  h.transport (identity_rows hsize) hok (by rw [identity_state]; exact hperm)

/-- Selecting the same vertex from a reordered target cell preserves the
reference occurrence in the resulting refined child. -/
theorem HasLeaf.reorderChild {tcLevel level tc e oU oV : Nat} {st : RefineSt n}
    {lab : Array Nat} {targets : List Nat} {key : Key n}
    (hsize : ctx.g.size = n) (hok : IterOk ctx level st) (hlvl : level < n)
    (hlab : lab.size = n) (hperm : cellsPerm st.ptn level lab st.lab)
    (hcell : (tc, e) ∈ cells st.ptn level n) (hne : tc < e)
    (hoU : oU ≤ e - tc) (hoV : oV ≤ e - tc)
    (hat : lab[tc + oV]! = st.lab[tc + oU]!)
    (h : HasLeaf ctx tcLevel (level + 1) (childSt ctx level st tc st.lab[tc + oU]!) targets key) :
    HasLeaf ctx tcLevel (level + 1)
      (childSt ctx level { st with lab := lab } tc lab[tc + oV]!) targets key := by
  have hsp : StPerm level { st with lab := lab } (mapSt (identity n) st) := by
    rw [identity_state]
    exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, hok.ok.labSize.trans hlab.symm, hperm⟩
  exact h.transport (identity_rows hsize) (iterOk_child hok hlvl hcell hne hoU)
    (stPerm_child (identity_rows hsize) hsp hok hcell hne hoV hoU hat)

/-- The child reference statement follows the arrays passed to the
executable refinement; bookkeeping fields of its input state play no role. -/
theorem HasLeaf.childFields {tcLevel level tc tv : Nat} {st : RefineSt n}
    {child : SearchSt n} {targets : List Nat} {key : Key n}
    (hlab : child.lab = (breakout n st.lab st.ptn (level + 1) tc tv).1)
    (hptn : child.ptn = st.ptn.set! tc (level + 1))
    (hactive : child.active = VSet.empty.insert tc) :
    HasLeaf ctx tcLevel (level + 1) (childSt ctx level st tc tv) targets key ↔
      HasLeaf ctx tcLevel (level + 1)
        (refine ctx (level + 1) child.lab child.ptn child.active (st.numcells + 1)) targets key := by
  rw [hlab, hptn, hactive]
  rfl

/-- Cell-equivalent refined states have the same reference occurrences,
including the sequence of target positions. -/
theorem RefPath.ofPerm {tcLevel boundary level : Nat} {U V : RefineSt n}
    {targets : List Nat} {key : Key n}
    (hsize : ctx.g.size = n) (hok : IterOk ctx level U) (hperm : StPerm level V U)
    (h : RefPath ctx tcLevel boundary level U targets key) : RefPath ctx tcLevel boundary level V targets key :=
  h.transport (identity_rows hsize) (identity_rows hsize) (by intros; rfl) hok (by rw [identity_state]; exact hperm)

/-- Selecting the same vertex from a reordered target cell preserves the
reference occurrence in the resulting refined child. -/
theorem RefPath.reorderChild {tcLevel boundary level tc e oU oV : Nat} {st : RefineSt n}
    {lab : Array Nat} {targets : List Nat} {key : Key n}
    (hsize : ctx.g.size = n) (hok : IterOk ctx level st) (hlvl : level < n)
    (hlab : lab.size = n) (hperm : cellsPerm st.ptn level lab st.lab)
    (hcell : (tc, e) ∈ cells st.ptn level n) (hne : tc < e)
    (hoU : oU ≤ e - tc) (hoV : oV ≤ e - tc)
    (hat : lab[tc + oV]! = st.lab[tc + oU]!)
    (h : RefPath ctx tcLevel boundary (level + 1) (childSt ctx level st tc st.lab[tc + oU]!) targets key) :
    RefPath ctx tcLevel boundary (level + 1)
      (childSt ctx level { st with lab := lab } tc lab[tc + oV]!) targets key := by
  have hsp : StPerm level { st with lab := lab } (mapSt (identity n) st) := by
    rw [identity_state]
    exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, hok.ok.labSize.trans hlab.symm, hperm⟩
  exact h.transport (identity_rows hsize) (identity_rows hsize) (by intros; rfl) (iterOk_child hok hlvl hcell hne hoU)
    (stPerm_child (identity_rows hsize) hsp hok hcell hne hoV hoU hat)

/-- The child reference statement follows the arrays passed to the
executable refinement; bookkeeping fields of its input state play no role. -/
theorem RefPath.childFields {tcLevel boundary level tc tv : Nat} {st : RefineSt n}
    {child : SearchSt n} {targets : List Nat} {key : Key n}
    (hlab : child.lab = (breakout n st.lab st.ptn (level + 1) tc tv).1)
    (hptn : child.ptn = st.ptn.set! tc (level + 1))
    (hactive : child.active = VSet.empty.insert tc) :
    RefPath ctx tcLevel boundary (level + 1) (childSt ctx level st tc tv) targets key ↔
      RefPath ctx tcLevel boundary (level + 1)
        (refine ctx (level + 1) child.lab child.ptn child.active (st.numcells + 1)) targets key := by
  rw [hlab, hptn, hactive]
  rfl

end Hex.GraphIso.Nauty.Generation
