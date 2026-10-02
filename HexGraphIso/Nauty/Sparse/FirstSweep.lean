/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexGraphIso.Nauty.Sparse.EarlyReturn
import all HexGraphIso.Nauty.Search.Generic
import all HexGraphIso.Nauty.Search.State

public section

namespace Hex.GraphIso.Nauty.Sparse

variable {n : Nat}

/-- Later first-path siblings leave the all-same boundary unchanged,
even if a child returns past the current frame. -/
theorem sweep_same (ctx : Graph n) (inf tcLevel fuel : Nat) :
    ∀ cfuel level numcells tc tv1 cursor cell index (st : State n),
      Generic.Past true tv1 cursor →
      (Generic.sweep true ctx inf tcLevel fuel cfuel level numcells tc tv1 cursor cell index st).2.2.allsamelevel =
        st.allsamelevel := by
  intro cfuel
  induction cfuel with
  | zero =>
    intro level numcells tc tv1 cursor cell index st _
    cases cursor <;> rw [Generic.sweep]
  | succ cfuel ih =>
    intro level numcells tc tv1 cursor cell index st hpast
    cases cursor with
    | none => rw [Generic.sweep]
    | some tv =>
      have htv := hpast rfl tv rfl
      have hf : (true && tv == tv1) = false := by simp only [Bool.true_and, beq_eq_false_iff_ne]; omega
      let raw := Generic.node false ctx inf tcLevel fuel (level + 1) (numcells + 1) ((policy (n := n)).child true level tc tv st)
      have hd : raw.2.allsamelevel = st.allsamelevel := node_same ..
      have hnext : ∀ cell : VSet n, Generic.Past true tv1 (cell.nextElem (some tv)) := by
        intro cell _ v hv
        have hh := (VSet.nextElem_eq_some_iff.mp hv).2.1
        change tv + 1 ≤ v at hh
        omega
      have hh : ∀ cell index, (Generic.sweep true ctx inf tcLevel fuel cfuel level numcells tc tv1
          (cell.nextElem (some tv)) cell index
          ((policy (n := n)).recover inf level { raw.2 with fixedpts := raw.2.fixedpts.erase tv })).2.2.allsamelevel =
          st.allsamelevel := by
        intro cell index
        rw [ih _ _ _ _ _ _ _ _ (hnext cell)]
        change (recoverLevels level (recoverPtn inf level _)).allsamelevel = _
        rw [recover_same]
        exact hd
      rw [Generic.sweep]
      unfold Generic.sweepStep Generic.advance Generic.resume
      simp only [hf, Bool.false_eq_true, ↓reduceIte, Id.run_pure, apply_ite Id.run]
      split
      · dsimp only [raw] at hd hh
        generalize hr : Generic.node false ctx inf tcLevel fuel (level + 1) (numcells + 1)
          ((policy (n := n)).child true level tc tv st) = result at hd hh ⊢
        obtain ⟨exit, out⟩ := result
        cases exit with
        | fuel => exact hd
        | done => exact hh _ _
        | unwind target short =>
          simp only [Id.run_pure, apply_ite Id.run]
          split
          · exact hd
          · cases short <;> exact hh _ _
      · exact ih _ _ _ _ _ _ _ _ (hnext cell)

/-- The guiding child's all-same boundary survives cleanup and the
entire sibling sweep, including an early exit. -/
theorem firstSweep_same {ctx : Graph n} {inf tcLevel fuel cfuel level numcells tc tv index : Nat}
    {cell : VSet n} {st : State n} (horbit : st.orbits[tv]! = tv) :
    (Generic.sweep true ctx inf tcLevel fuel (cfuel + 1) level numcells tc tv (some tv) cell index st).2.2.allsamelevel =
      (Generic.node true ctx inf tcLevel fuel (level + 1) (numcells + 1) ((policy (n := n)).child true level tc tv st)).2.allsamelevel := by
  let raw := Generic.node true ctx inf tcLevel fuel (level + 1) (numcells + 1) ((policy (n := n)).child true level tc tv st)
  have hh : ∀ cell index, (Generic.sweep true ctx inf tcLevel fuel cfuel level numcells tc tv
      (cell.nextElem (some tv)) cell index
      ((policy (n := n)).recover inf level
        { afterChildFirst level tv raw.2 with fixedpts := raw.2.fixedpts.erase tv })).2.2.allsamelevel =
      raw.2.allsamelevel := by
    intro cell index
    rw [sweep_same ctx inf tcLevel fuel cfuel _ _ _ _ _ _ _ _ (by
      intro _ v hv
      have hh := (VSet.nextElem_eq_some_iff.mp hv).2.1
      change tv + 1 ≤ v at hh
      omega)]
    change (recoverLevels level (recoverPtn inf level _)).allsamelevel = _
    rw [recover_same]
    rfl
  dsimp only [raw] at hh
  change Generic.Policy.orbit (n := n) st tv = tv at horbit
  rw [Generic.sweep]
  unfold Generic.sweepStep Generic.advance Generic.resume
  simp only [Bool.not_true, horbit, beq_self_eq_true, Bool.or_true,
    Bool.and_self, Bool.false_and, Bool.true_and, ↓reduceIte]
  generalize hr : Generic.node true ctx inf tcLevel fuel (level + 1) (numcells + 1)
    ((policy (n := n)).child true level tc tv st) = result at hh ⊢
  obtain ⟨exit, out⟩ := result
  cases exit with
  | fuel => rfl
  | done => exact hh _ _
  | unwind target short =>
    simp only [Id.run_pure, apply_ite Id.run]
    split
    · rfl
    · cases short <;> exact hh _ _

end Hex.GraphIso.Nauty.Sparse
