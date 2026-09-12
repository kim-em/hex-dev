/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexGraphIso.Nauty.Equitable.Step
import all HexGraphIso.Nauty.Equitable.Step
public import HexGraphIso.Nauty.Spec.SpecIso

public section

namespace Hex.GraphIso.Nauty.Renaming

/-- Restricting an injective, range-preserving renaming to the finite
vertex range gives a surjection of that range. -/
theorem surjective (σ : Renaming n) (v : Fin n) :
    ∃ i : Fin n, σ i.val = v.val := by
  let lab := Array.ofFn fun i : Fin n => σ i.val
  have hget (i : Nat) (hi : i < n) : lab[i]! = σ i := by
    rw [getElem!_pos lab i (by simpa only [lab, Array.size_ofFn] using hi)]
    exact Array.getElem_ofFn ..
  have hbound : LabOk lab n := by
    intro i hi
    have hi' : i < n := by simpa only [lab, Array.size_ofFn] using hi
    rw [hget i hi']
    exact (σ.maps i).mp hi'
  have hinj : LabInj lab n := by
    intro i j hi hj he
    rw [hget i hi, hget j hj] at he
    exact σ.inj i j he
  obtain ⟨i, hi, he⟩ := labInj_surj (lab := lab) (by simp [lab]) hbound hinj v.val v.isLt
  exact ⟨⟨i, hi⟩, (hget i hi).symm.trans he⟩

/-- The finite permutation underlying a vertex renaming. This conversion
is used in proofs connecting shared stabilizers to native graph adjacency. -/
@[expose] def toPerm (σ : Renaming n) : Perm n :=
  Perm.ofFn (fun i : Fin n => ⟨σ i.val, (σ.maps i.val).mp i.isLt⟩)
    (fun i j he => Fin.ext (σ.inj i.val j.val (congrArg Fin.val he)))
    (fun v => by obtain ⟨i, hi⟩ := σ.surjective v; exact ⟨i, Fin.ext hi⟩)

@[simp] theorem get_toPerm (σ : Renaming n) (v : Fin n) :
    (σ.toPerm.get v).val = σ v.val := by simp [toPerm]

/-- On valid label entries, the standard extension of the finite
permutation is exactly the original renaming. -/
theorem map_toPerm (σ : Renaming n) (lab : Array Nat)
    (h : ∀ i, i < lab.size → lab[i]! < n) :
    lab.map (renamingOf σ.toPerm).toFun = lab.map σ.toFun := by
  apply Array.ext (by simp)
  intro i hi hj
  have hin : i < lab.size := by simpa only [Array.size_map] using hi
  have hb := h i hin
  rw [getElem!_pos lab i hin] at hb
  simp only [Array.getElem_map, renamingOf_lt σ.toPerm hb, get_toPerm]

end Hex.GraphIso.Nauty.Renaming
