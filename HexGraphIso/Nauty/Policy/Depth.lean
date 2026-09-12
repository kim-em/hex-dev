/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexGraphIso.Nauty.Policy.First.Ref
import all HexGraphIso.Nauty.Policy.First.State
import all HexGraphIso.Nauty.Policy.Instance
import all HexGraphIso.Nauty.Search.Search
import all HexGraphIso.Nauty.Search.State

public section

namespace Hex.GraphIso.Nauty

variable {n : Nat} {κ : Type}

/-- First-code agreement remains above the sentinel after the first leaf. -/
def Depth (last : Nat) (st : SearchState n κ) : Prop :=
  st.eqlevFirst ≤ last ∧ st.firstcode[last + 1]! = codeSentinel

/-- Lowering agreement while preserving the reference preserves its depth bound. -/
theorem Depth.mono {last : Nat} {st out : SearchState n κ} (h : Depth last st)
    (hle : out.eqlevFirst ≤ st.eqlevFirst) (href : out.reference = st.reference) :
    Depth last out := by
  have hcodes := congrArg (fun x : Array Nat × Array Int × Array Nat => x.1) href
  change out.firstcode = st.firstcode at hcodes
  exact ⟨Nat.le_trans hle h.1, by rw [hcodes]; exact h.2⟩

/-- A real refinement code cannot advance agreement through the saved sentinel. -/
theorem compareCodes_depth {last level code : Nat} {st : SearchState n κ}
    (h : Depth last st) (hcode : code < codeSentinel) : Depth last (compareCodes level code st) := by
  have he : (compareCodes level code st).eqlevFirst ≤ last := by
    unfold compareCodes
    simp only [Id.run_pure, apply_ite Id.run, apply_ite SearchState.eqlevFirst, ite_self]
    split
    · rename_i hmatch
      have ha : st.eqlevFirst = level - 1 ∧ code = st.firstcode[level]! := by simpa using hmatch
      have hb := h.1
      have hs := h.2
      by_cases hle : level ≤ last
      · exact hle
      · have hl : level = last + 1 := by omega
        rw [hl, hs] at ha
        omega
    · exact h.1
  have hcodes : (compareCodes level code st).firstcode = st.firstcode := by
    unfold compareCodes
    simp only [Id.run_pure, apply_ite Id.run, apply_ite SearchState.firstcode, ite_self]
  exact ⟨he, by rw [hcodes]; exact h.2⟩

/-- Target selection can only lower first-code agreement. -/
theorem chooseTarget_le (ctx : Ctx n) (tcLevel level numcells : Nat) (st : Search n) :
    (chooseTarget false ctx tcLevel level numcells st).2.2.2.eqlevFirst ≤ st.eqlevFirst := by
  unfold chooseTarget
  simp only [Bool.false_eq_true, ite_false, Bool.not_false, Bool.true_and,
    Id.run_pure, apply_ite Id.run, apply_ite Prod.snd, apply_ite SearchState.eqlevFirst]
  repeat' split
  all_goals simp_all only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq]
  all_goals simp_all
  all_goals omega

/-- Classification preserves the first-code agreement counter. -/
theorem classify_eqlev (ctx : Ctx n) (level numcells : Nat) (st : Search n) :
    (classify ctx level numcells st).2.eqlevFirst = st.eqlevFirst := by
  unfold classify
  simp only [Id.run_pure, apply_ite Id.run, apply_ite Prod.snd, scatter_eq]
  simp only [apply_ite SearchState.eqlevFirst, ite_self]

private theorem admit_eqlev (st : SearchState n κ) : (admit st).eqlevFirst = st.eqlevFirst := by
  unfold admit pushAuto
  simp only [Id.run_pure]
  split <;> rfl

private theorem pruneReturn_eqlev (level : Nat) (st : SearchState n κ) :
    (pruneReturn level st).2.eqlevFirst = st.eqlevFirst := by
  unfold pruneReturn pushAuto
  simp only [Id.run_pure, apply_ite Id.run, apply_ite Prod.snd]
  repeat' split
  all_goals rfl

/-- Leaf actions preserve the first-code agreement counter. -/
theorem leafExit_eqlev (leaf : Leaf) (level : Nat) (st : SearchState n κ) :
    (leafExit leaf level st).2.eqlevFirst = st.eqlevFirst := by
  cases leaf <;> unfold leafExit
  all_goals simp only [Id.run_pure, apply_ite Id.run, apply_ite Prod.snd]
  all_goals repeat' split
  all_goals first
    | rfl
    | exact admit_eqlev _
    | exact pruneReturn_eqlev level _

/-- Recovery can only lower first-code agreement. -/
theorem recover_le (inf level : Nat) (st : SearchState n κ) :
    (Nauty.recover inf level st).eqlevFirst ≤ st.eqlevFirst := by
  unfold Nauty.recover recoverLevels recoverPtn
  simp only [Id.run_bind, Id.run_pure, apply_ite Id.run, apply_ite SearchState.eqlevFirst, ite_self]
  repeat' split
  all_goals omega

/-- The search preserves the sentinel depth bound on off-path calls and later siblings. -/
theorem depthPolicy (ctx : Ctx n) (inf tcLevel last : Nat) :
    Generic.StablePolicy ctx inf tcLevel (Depth (n := n) (κ := Array (VSet n)) last)
      (fun code => code < codeSentinel) where
  code := fun level numcells st => refine_longcode_lt ctx level st.lab st.ptn st.active numcells
  visit := fun _ _ _ h => h
  compare := fun _ _ _ hc h => compareCodes_depth h hc
  target := by
    intro level numcells st h
    exact h.mono (chooseTarget_le ctx tcLevel level numcells st)
      ((referencePolicy ctx inf tcLevel).target level numcells st)
  classify := by
    intro level numcells st h
    exact ⟨h.mono (Nat.le_of_eq (classify_eqlev ctx level numcells st))
      (classify_reference ctx level numcells st), trivial⟩
  leaf := by
    intro leaf level st _ h
    exact h.mono (Nat.le_of_eq (leafExit_eqlev leaf level st)) (leafExit_reference leaf level st)
  cheap := by
    intro first level st h
    change Depth last (cheapCheck first level st)
    unfold cheapCheck
    split <;> exact h
  child := by
    intro first level tc tv st h
    cases first <;> exact h
  leave := fun _ _ h => h
  recover := by
    intro level st h
    exact h.mono (recover_le inf level st) ((referencePolicy ctx inf tcLevel).recover level st)
  afterSweep := by
    intro level size index st h
    change Depth last (afterSweep false level size index st)
    unfold afterSweep
    split <;> exact h

/-- An off-path node cannot extend agreement below the actual first leaf. -/
theorem node_depth {ctx : Ctx n} {inf tcLevel fuel level numcells last : Nat} {st : Search n}
    (h : Depth last st) : Depth last (node false ctx inf tcLevel fuel level numcells st).2 := by
  rw [node_eq_generic]
  exact Generic.node_stable (depthPolicy ctx inf tcLevel last) fuel level numcells st h

/-- Later siblings preserve the same bound, including during a first-path sweep. -/
theorem sweep_depth {ctx : Ctx n} {first : Bool}
    {inf tcLevel fuel cfuel level numcells tc tv1 index last : Nat}
    {cursor : Option Nat} {cell : VSet n} {st : Search n}
    (h : Depth last st) (hpast : Generic.Past first tv1 cursor) :
    Depth last (sweep first ctx inf tcLevel fuel cfuel level numcells tc tv1 cursor cell index st).2.2 := by
  rw [sweep_eq_generic]
  exact Generic.sweep_stable (depthPolicy ctx inf tcLevel last) first fuel cfuel level numcells
    tc tv1 index cursor cell st hpast h

/-- A full first-path call retains the bound installed at its actual first leaf. -/
theorem firstPath_depth {ctx : Ctx n} {inf tcLevel fuel level numcells last : Nat}
    {st leaf : Search n}
    (hpath : Generic.FirstPath ctx tcLevel fuel level numcells st last leaf)
    (hsize : st.firstcode.size = n + 2) (hlast : last ≤ n) :
    Depth last (node true ctx inf tcLevel fuel level numcells st).2 := by
  rw [node_eq_generic]
  apply hpath.stable (depthPolicy ctx inf tcLevel last) (fun _ _ _ h => h) (by
    intro level size index st h
    change Depth last (afterSweep true level size index st)
    unfold afterSweep
    split <;> exact h)
  change last ≤ last ∧ (leaf.firstcode.set! (last + 1) codeSentinel)[last + 1]! = codeSentinel
  exact ⟨Nat.le_refl _, Array.getElem!_set!_self _ _ _
    (by rw [firstPath_codeSize hpath, hsize]; omega)⟩

end Hex.GraphIso.Nauty
