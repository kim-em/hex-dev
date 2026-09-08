/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexGraphIso.Nauty.Policy.FirstBounded
public import HexGraphIso.Nauty.Policy.EarlyReturn
import all HexGraphIso.Nauty.Policy.FirstBounded
import all HexGraphIso.Nauty.Policy.EarlyReturn
import all HexGraphIso.Nauty.Policy.Alignment
import all HexGraphIso.Nauty.Policy.Depth
import all HexGraphIso.Nauty.Policy.Bounds
import all HexGraphIso.Nauty.Policy.First
import all HexGraphIso.Nauty.Policy.Engine
import all HexGraphIso.Nauty.Policy.State
import all HexGraphIso.Nauty.Search.Search

public section

namespace Hex.GraphIso.Nauty.Engine

variable {n : Nat}

/-- Operations at or below a frame retain its lower bound on the
all-same boundary and first-reference agreement. -/
theorem firstFloor (ctx : Ctx n) (inf tcLevel bound : Nat) :
    Generic.BoundedPolicy ctx inf tcLevel bound
      (fun st : Search n => bound ≤ st.allsamelevel ∧ bound ≤ st.eqlevFirst) where
  visit := fun _ _ _ h => h
  compare := by
    intro level code st hl h
    change bound ≤ (compareCodes level code st).allsamelevel ∧
      bound ≤ (compareCodes level code st).eqlevFirst
    rw [compare_same, compareCodes_eqlev]
    split <;> exact ⟨h.1, by omega⟩
  target := by
    intro level numcells st hl h
    change bound ≤ (chooseTarget false ctx tcLevel level numcells st).2.2.2.allsamelevel ∧
      bound ≤ (chooseTarget false ctx tcLevel level numcells st).2.2.2.eqlevFirst
    unfold chooseTarget
    simp only [Bool.false_eq_true, ite_false, Bool.not_false, Bool.true_and,
      Id.run_pure, apply_ite Id.run, apply_ite Prod.snd,
      apply_ite Search.allsamelevel, apply_ite Search.eqlevFirst]
    repeat' split
    all_goals exact ⟨h.1, by first | exact h.2 | omega⟩
  classify := by
    intro level numcells st h
    change bound ≤ (classify ctx level numcells st).2.allsamelevel ∧
      bound ≤ (classify ctx level numcells st).2.eqlevFirst
    rwa [classify_same, classify_eqlev]
  leaf := by
    intro leaf level st _ h
    change bound ≤ (leafExit leaf level st).2.allsamelevel ∧
      bound ≤ (leafExit leaf level st).2.eqlevFirst
    rwa [leafExit_same, leafExit_eqlev]
  cheap := by
    intro first level st _ h
    change bound ≤ (cheapCheck first level st).allsamelevel ∧
      bound ≤ (cheapCheck first level st).eqlevFirst
    unfold cheapCheck
    split <;> exact h
  child := by intro first level tc tv st h; cases first <;> exact h
  leave := fun _ _ h => h
  recover := by
    intro level st hl h
    change bound ≤ (recoverLevels level (recoverPtn inf level st)).allsamelevel ∧
      bound ≤ (recoverLevels level (recoverPtn inf level st)).eqlevFirst
    rw [recover_same, recover_eqlev]
    exact ⟨h.1, by omega⟩
  afterSweep := by
    intro first level size index st hl h
    change bound ≤ (afterSweep first level size index st).allsamelevel ∧
      bound ≤ (afterSweep first level size index st).eqlevFirst
    unfold afterSweep
    split
    · rename_i hc
      have he : st.allsamelevel = level + 1 := by
        simp only [Bool.and_eq_true, beq_iff_eq] at hc
        exact hc.2
      exact ⟨by dsimp only; omega, h.2⟩
    · exact h

/-- The first leaf installs both bounds, and every enclosing first
sweep preserves them down to its own entry level. -/
theorem firstPath_floor {ctx : Ctx n} {inf tcLevel fuel level numcells last : Nat}
    {st leaf : Search n} (hp : Generic.FirstPath ctx tcLevel fuel level numcells st last leaf) :
    level ≤ (node true ctx inf tcLevel fuel level numcells st).2.allsamelevel ∧
      level ≤ (node true ctx inf tcLevel fuel level numcells st).2.eqlevFirst := by
  have hl : level ≤ last := by
    induction hp with
    | leaf => exact Nat.le_refl _
    | step _ _ _ _ ih => omega
  have h := hp.bounded (firstFloor ctx inf tcLevel level) (fun _ _ _ h => h)
    (Nat.le_refl _) (show level ≤ (firstterminal last leaf).allsamelevel ∧
      level ≤ (firstterminal last leaf).eqlevFirst from ⟨hl, hl⟩)
  rwa [← node_eq_generic] at h

/-- Later first-path siblings leave the all-same boundary unchanged,
even if a child returns past the current frame. -/
theorem sweep_same (ctx : Ctx n) (inf tcLevel fuel : Nat) :
    ∀ cfuel level numcells tc tv1 cursor cell index (st : Search n),
      Generic.Past true tv1 cursor →
      (sweep true ctx inf tcLevel fuel cfuel level numcells tc tv1 cursor cell index st).2.2.allsamelevel =
        st.allsamelevel := by
  intro cfuel
  induction cfuel with
  | zero =>
    intro level numcells tc tv1 cursor cell index st _
    cases cursor <;> rw [sweep]
  | succ cfuel ih =>
    intro level numcells tc tv1 cursor cell index st hpast
    cases cursor with
    | none => rw [sweep]
    | some tv =>
      have htv := hpast rfl tv rfl
      have hf : (true && tv == tv1) = false := by simp only [Bool.true_and, beq_eq_false_iff_ne]; omega
      let raw := node false ctx inf tcLevel fuel (level + 1) (numcells + 1) (child true level tc tv st)
      have hd : raw.2.allsamelevel = st.allsamelevel := node_same ..
      have hnext : ∀ cell : VSet n, Generic.Past true tv1 (cell.nextElem (some tv)) := by
        intro cell _ v hv
        have hh := (VSet.nextElem_eq_some_iff.mp hv).2.1
        change tv + 1 ≤ v at hh
        omega
      have hh : ∀ cell index, (sweep true ctx inf tcLevel fuel cfuel level numcells tc tv1
          (cell.nextElem (some tv)) cell index
          (recoverLevels level (recoverPtn inf level { raw.2 with fixedpts := raw.2.fixedpts.erase tv }))).2.2.allsamelevel =
          st.allsamelevel := by
        intro cell index
        rw [ih _ _ _ _ _ _ _ _ (hnext cell), recover_same]
        exact hd
      rw [sweep]
      simp only [hf, Bool.false_eq_true, ↓reduceIte, Id.run_pure, apply_ite Id.run]
      split
      · dsimp only [raw] at hd hh
        generalize hr : node false ctx inf tcLevel fuel (level + 1) (numcells + 1)
          (child true level tc tv st) = result at hd hh ⊢
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
theorem firstSweep_same {ctx : Ctx n} {inf tcLevel fuel cfuel level numcells tc tv index : Nat}
    {cell : VSet n} {st : Search n} (horbit : st.orbits[tv]! = tv) :
    (sweep true ctx inf tcLevel fuel (cfuel + 1) level numcells tc tv (some tv) cell index st).2.2.allsamelevel =
      (node true ctx inf tcLevel fuel (level + 1) (numcells + 1) (child true level tc tv st)).2.allsamelevel := by
  let raw := node true ctx inf tcLevel fuel (level + 1) (numcells + 1) (child true level tc tv st)
  have hh : ∀ cell index, (sweep true ctx inf tcLevel fuel cfuel level numcells tc tv
      (cell.nextElem (some tv)) cell index
      (recoverLevels level (recoverPtn inf level
        { afterChildFirst level tv raw.2 with fixedpts := raw.2.fixedpts.erase tv }))).2.2.allsamelevel =
      raw.2.allsamelevel := by
    intro cell index
    rw [sweep_same ctx inf tcLevel fuel cfuel _ _ _ _ _ _ _ _ (by
      intro _ v hv
      have hh := (VSet.nextElem_eq_some_iff.mp hv).2.1
      change tv + 1 ≤ v at hh
      omega), recover_same]
    rfl
  dsimp only [raw] at hh
  rw [sweep]
  simp only [Bool.not_true, horbit, beq_self_eq_true, Bool.or_true,
    Bool.and_self, ↓reduceIte]
  generalize hr : node true ctx inf tcLevel fuel (level + 1) (numcells + 1)
    (child true level tc tv st) = result at hh ⊢
  obtain ⟨exit, out⟩ := result
  cases exit with
  | fuel => rfl
  | done => exact hh _ _
  | unwind target short =>
    simp only [Id.run_pure, apply_ite Id.run]
    split
    · rfl
    · cases short <;> exact hh _ _

end Hex.GraphIso.Nauty.Engine
