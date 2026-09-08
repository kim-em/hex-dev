/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexPermGroup.Product.WreathProjection

public section

namespace Hex.Perm.Wreath

@[expose] def single (i : Fin m) (p : Perm n) : Fin m → Perm n := fun j => if j = i then p else Perm.id n

@[expose] def copy (hn : 0 < n) (i : Fin m) (p : Perm n) : Perm (n * m) := perm hn (single i p) (Perm.id m)

@[expose] def lift (hn : 0 < n) (h : Perm m) : Perm (n * m) := perm hn (fun _ => Perm.id n) h

@[simp] theorem copy_id (hn : 0 < n) (i : Fin m) : copy hn i (Perm.id n) = Perm.id (n * m) := by
  have he : single i (Perm.id n) = fun _ => Perm.id n := by funext j; simp [single]
  simp [copy, he]

@[simp] theorem lift_id (hn : 0 < n) : lift (m := m) hn (Perm.id m) = Perm.id (n * m) := perm_id hn

theorem copy_comp (hn : 0 < n) (i : Fin m) (p q : Perm n) :
    copy hn i (p.comp q) = (copy hn i p).comp (copy hn i q) := by
  rw [copy, copy, copy, perm_comp]
  simp only [Perm.inv_id, Perm.get_id, Perm.comp_id]
  congr 1
  funext j
  by_cases hj : j = i <;> simp [single, hj]

theorem copy_inv (hn : 0 < n) (i : Fin m) (p : Perm n) : copy hn i p.inv = (copy hn i p).inv := by
  rw [copy, copy, perm_inv]
  simp only [Perm.inv_id]
  congr 1
  funext j
  by_cases hj : j = i <;> simp [single, inverse, hj]

theorem lift_comp (hn : 0 < n) (h k : Perm m) : lift hn (h.comp k) = (lift hn h).comp (lift hn k) := by
  simp [lift, perm_comp]

theorem lift_inv (hn : 0 < n) (h : Perm m) : lift hn h.inv = (lift hn h).inv := by
  rw [lift, lift, perm_inv]
  congr 1
  funext j
  simp [inverse]

/-- The base permutation followed by the top permutation gives the stated
destination-indexed action. -/
theorem factor (hn : 0 < n) (f : Fin m → Perm n) (h : Perm m) :
    perm hn f h = (perm hn f (Perm.id m)).comp (lift hn h) := by
  simp [lift, perm_comp]

/-- Multiply the base factors in increasing block order. This auxiliary
function is used in the erased generation proof, not to enumerate elements. -/
@[expose] def initial (f : Fin m → Perm n) (k : Nat) : Fin m → Perm n :=
  fun j => if j.val < k then f j else Perm.id n

@[simp] theorem initial_zero (f : Fin m → Perm n) : initial f 0 = fun _ => Perm.id n := by
  funext j
  simp [initial]

@[simp] theorem initial_full (f : Fin m → Perm n) : initial f m = f := by
  funext j
  simp [initial, j.isLt]

theorem initial_succ (hn : 0 < n) (f : Fin m → Perm n) (k : Nat) (hk : k < m) :
    perm hn (initial f (k + 1)) (Perm.id m) =
      (perm hn (initial f k) (Perm.id m)).comp (copy hn ⟨k, hk⟩ (f ⟨k, hk⟩)) := by
  rw [copy, perm_comp]
  simp only [Perm.inv_id, Perm.get_id, Perm.comp_id]
  congr 1
  funext j
  by_cases hj : j = ⟨k, hk⟩
  · subst j
    simp [initial, single]
  · have hv : j.val ≠ k := fun he => hj (Fin.ext he)
    by_cases hl : j.val < k
    · have hs : j.val < k + 1 := by omega
      simp [initial, single, hj, hl, hs]
    · have hs : ¬j.val < k + 1 := by omega
      simp [initial, single, hj, hl, hs]

end Hex.Perm.Wreath
