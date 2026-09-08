/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexGraphIso.Nauty.Policy.State
public import HexGraphIso.Nauty.Invariant.Refine
import all HexGraphIso.Nauty.Search.Search
import all HexGraphIso.Nauty.Policy.State

public section

namespace Hex.GraphIso.Nauty.Engine

variable {n k : Nat}

/-- Code comparison changes no partition or leaf-reference array. -/
theorem compareCodes_frame (level code : Nat) (st : Search n) :
    let out := compareCodes level code st
    out.lab = st.lab ∧ out.ptn = st.ptn ∧
      out.firstlab = st.firstlab ∧ out.canonlab = st.canonlab := by
  unfold compareCodes
  simp only [Id.run_pure, apply_ite Id.run, apply_ite Search.lab,
    apply_ite Search.ptn, apply_ite Search.firstlab, apply_ite Search.canonlab, ite_self]
  trivial

/-- Target selection changes no partition or leaf-reference array. -/
theorem chooseTarget_frame (first : Bool) (ctx : Ctx n)
    (tcLevel level numcells : Nat) (st : Search n) :
    let out := (chooseTarget first ctx tcLevel level numcells st).2.2.2
    out.lab = st.lab ∧ out.ptn = st.ptn ∧
      out.firstlab = st.firstlab ∧ out.canonlab = st.canonlab := by
  unfold chooseTarget
  simp only [Id.run_pure, apply_ite Id.run, apply_ite Prod.snd,
    apply_ite Search.lab, apply_ite Search.ptn, apply_ite Search.firstlab,
    apply_ite Search.canonlab, ite_self]
  trivial

/-- Only an internal classification continues the current node. -/
theorem leafExit_done (leaf : Leaf) (level : Nat) (st : Search n) :
    (leafExit leaf level st).1 = .done ↔ leaf = .internal := by
  cases leaf <;> unfold leafExit
  all_goals simp only [Id.run_pure, apply_ite Id.run, apply_ite Prod.fst]
  all_goals repeat' split
  all_goals simp only [pruneReturn, Id.run_pure, apply_ite Id.run,
    apply_ite Prod.fst, reduceCtorEq, iff_self]
  all_goals repeat' split
  all_goals simp

/-- Pruning returns an ancestor level without consuming recursion fuel. -/
theorem pruneReturn_noFuel (level : Nat) (st : Search n) :
    (pruneReturn level st).1 ≠ .fuel := by
  unfold pruneReturn
  simp only [Id.run_pure, apply_ite Id.run, apply_ite Prod.fst]
  split <;> (intro h; cases h)

/-- Leaf actions return control without consuming recursion fuel. -/
theorem leafExit_noFuel (leaf : Leaf) (level : Nat) (st : Search n) :
    (leafExit leaf level st).1 ≠ .fuel := by
  cases leaf <;> unfold leafExit
  all_goals simp only [Id.run_pure, apply_ite Id.run, apply_ite Prod.fst]
  all_goals repeat' split
  all_goals first
    | exact pruneReturn_noFuel level _
    | (intro h; cases h)

/-- The internal classification is exactly a non-discrete node that has
not failed both first-path and canonical comparison. -/
theorem classify_internal (ctx : Ctx n) (level numcells : Nat) (st : Search n) :
    (classify ctx level numcells st).1 = .internal ↔
      ¬ (st.eqlevFirst ≠ level ∧ st.compCanon < 0) ∧ numcells ≠ n := by
  unfold classify
  simp only [Id.run_pure, apply_ite Id.run, apply_ite Prod.fst]
  repeat' split
  all_goals simp_all only [Bool.and_eq_true, bne_iff_ne, decide_eq_true_eq,
    true_and, reduceCtorEq, not_false_eq_true]
  all_goals simp_all

/-- Classification preserves the partition and both saved labellings. -/
theorem classify_frame (ctx : Ctx n) (level numcells : Nat) (st : Search n) :
    let out := (classify ctx level numcells st).2
    out.lab = st.lab ∧ out.ptn = st.ptn ∧
      out.firstlab = st.firstlab ∧ out.canonlab = st.canonlab := by
  unfold classify
  simp only [Id.run_pure, apply_ite Id.run, apply_ite Prod.snd, scatter_eq]
  simp only [apply_ite Search.lab, apply_ite Search.ptn,
    apply_ite Search.firstlab, apply_ite Search.canonlab, ite_self]
  trivial

/-- Admitting a generator does not change the partition or leaf references. -/
theorem admit_frame (st : Search n) :
    (admit st).lab = st.lab ∧ (admit st).ptn = st.ptn ∧
      (admit st).firstlab = st.firstlab ∧ (admit st).canonlab = st.canonlab := by
  unfold admit pushAuto
  simp only [Id.run_pure]
  split <;> exact ⟨rfl, rfl, rfl, rfl⟩

/-- A pruning return changes neither the partition nor the leaf references. -/
theorem pruneReturn_frame (level : Nat) (st : Search n) :
    let out := (pruneReturn level st).2
    out.lab = st.lab ∧ out.ptn = st.ptn ∧
      out.firstlab = st.firstlab ∧ out.canonlab = st.canonlab := by
  unfold pruneReturn pushAuto
  simp only [Id.run_pure, apply_ite Id.run, apply_ite Prod.snd]
  repeat' split
  all_goals exact ⟨rfl, rfl, rfl, rfl⟩

/-- Processing a leaf preserves the current partition and first leaf;
the canonical labelling is retained or replaced by the current labelling. -/
theorem leafExit_frame (leaf : Leaf) (level : Nat) (st : Search n) :
    let out := (leafExit leaf level st).2
    out.lab = st.lab ∧ out.ptn = st.ptn ∧ out.firstlab = st.firstlab ∧
      (out.canonlab = st.canonlab ∨ out.canonlab = st.lab) := by
  cases leaf <;> unfold leafExit
  all_goals simp only [Id.run_pure, apply_ite Id.run, apply_ite Prod.snd]
  all_goals repeat' split
  all_goals first
    | exact ⟨rfl, rfl, rfl, Or.inl rfl⟩
    | (obtain ⟨hl, hp, hf, hc⟩ := admit_frame _
       exact ⟨hl, hp, hf, Or.inl hc⟩)
    | (obtain ⟨hl, hp, hf, hc⟩ := pruneReturn_frame level _
       exact ⟨hl, hp, hf, Or.inl hc⟩)
    | (obtain ⟨hl, hp, hf, hc⟩ := pruneReturn_frame level _
       exact ⟨hl, hp, hf, Or.inr hc⟩)

/-- Changing bookkeeping and optionally installing the current labelling
preserves the partition invariant. -/
theorem frame_ok {G : Colored n k} {level numcells : Nat} {st out : Search n}
    (hok : SearchOk G level numcells st.view)
    (hl : out.lab = st.lab) (hp : out.ptn = st.ptn)
    (hc : out.canonlab = st.canonlab ∨ out.canonlab = st.lab) :
    SearchOk G level numcells out.view := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · change out.lab.size = n
    rw [hl]
    exact hok.labSize
  · change out.ptn.size = n
    rw [hp]
    exact hok.ptnSize
  · change CellsReach G out.lab
    rw [hl]
    exact hok.reach
  · intro q hq
    change out.ptn[q]! ≤ 1
    rw [hp]
    exact hok.init1 q hq
  · intro q hq
    change out.ptn[q]! ≤ level ∨ out.ptn[q]! = n + 2
    rw [hp]
    exact hok.vals q hq
  · change numcells = bcount out.ptn level n
    rw [hp]
    exact hok.count
  · change level ≤ bcount out.ptn level n
    rw [hp]
    exact hok.bc
  · rcases hc with hc | hc
    · change out.canonlab = Array.replicate n 0 ∨
        (out.canonlab.size = n ∧ CellsReach G out.canonlab)
      rw [hc]
      exact hok.canon
    · right
      change out.canonlab.size = n ∧ CellsReach G out.canonlab
      rw [hc]
      exact ⟨hok.labSize, hok.reach⟩

/-- A local operation with unchanged partition and only current-leaf
installations satisfies the call's frame effect. -/
theorem frame_out {G : Colored n k} {B level numcells : Nat} {st out : Search n}
    (hok : SearchOk G level numcells st.view)
    (hl : out.lab = st.lab) (hp : out.ptn = st.ptn)
    (hf : out.firstlab = st.firstlab ∨ out.firstlab = st.lab)
    (hc : out.canonlab = st.canonlab ∨ out.canonlab = st.lab) :
    SearchOut G B level st.view out.view := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact congrArg Array.size hl
  · exact congrArg Array.size hp
  · change CellsReach G out.lab
    rw [hl]
    exact hok.reach
  · intro q _
    exact congrArg (fun ptn => ptn[q]!) hp
  · change cellsPerm st.ptn level st.lab out.lab
    rw [hl]
    exact cellsPerm_refl _ _ _
  · rcases hf with hf | hf
    · exact Or.inl hf
    · right
      change out.firstlab.size = st.lab.size ∧ cellsPerm st.ptn level st.lab out.firstlab
      rw [hf]
      exact ⟨rfl, cellsPerm_refl _ _ _⟩
  · rcases hc with hc | hc
    · exact Or.inl hc
    · right
      change out.canonlab.size = st.lab.size ∧ cellsPerm st.ptn level st.lab out.canonlab
      rw [hc]
      exact ⟨rfl, cellsPerm_refl _ _ _⟩
  · rcases hc with hc | hc
    · exact Or.inl hc
    · right
      change out.canonlab.size = n ∧ CellsReach G out.canonlab
      rw [hc]
      exact ⟨hok.labSize, hok.reach⟩

/-- Classification and the resulting leaf action preserve the partition
invariant, independently of whether the classification is sound. -/
theorem leaf_ok {G : Colored n k} {ctx : Ctx n} {level numcells : Nat}
    {st : Search n} (hok : SearchOk G level numcells st.view) :
    let verdict := classify ctx level numcells st
    SearchOk G level numcells (leafExit verdict.1 level verdict.2).2.view := by
  obtain ⟨hl, hp, _, hc⟩ := classify_frame ctx level numcells st
  have hmid := frame_ok hok hl hp (Or.inl hc)
  obtain ⟨hl', hp', _, hc'⟩ := leafExit_frame (classify ctx level numcells st).1
    level (classify ctx level numcells st).2
  exact frame_ok hmid hl' hp' hc'

/-- The combined leaf operations have only the permitted frame effect. -/
theorem leaf_out {G : Colored n k} {ctx : Ctx n} {B level numcells : Nat}
    {st : Search n} (hok : SearchOk G level numcells st.view) :
    let verdict := classify ctx level numcells st
    SearchOut G B level st.view (leafExit verdict.1 level verdict.2).2.view := by
  obtain ⟨hl, hp, hf, hc⟩ := classify_frame ctx level numcells st
  obtain ⟨hl', hp', hf', hc'⟩ := leafExit_frame (classify ctx level numcells st).1
    level (classify ctx level numcells st).2
  apply frame_out hok (hl'.trans hl) (hp'.trans hp) (Or.inl (hf'.trans hf))
  rcases hc' with hc' | hc'
  · exact Or.inl (hc'.trans hc)
  · exact Or.inr (hc'.trans hl)

end Hex.GraphIso.Nauty.Engine
