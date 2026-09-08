/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexPermGroup.Product.WreathPerm

public section

namespace Hex.Perm.Wreath

variable (hn : 0 < n) (r : Perm (n * m))
  (hr : ∃ (f : Fin m → Perm n) (h : Perm m), r = perm hn f h)

/-- Read the destination of each block using its first point. -/
@[expose] def topPoint (j : Fin m) : Fin m := block hn (r.get (index ⟨0, hn⟩ j))

@[simp] theorem topPoint_perm (f : Fin m → Perm n) (h : Perm m) (j : Fin m) :
    topPoint hn (perm hn f h) j = h.get j := by simp [topPoint]

@[expose] def top : Perm m := Perm.ofFn (topPoint hn r)
  (by
    obtain ⟨f, h, rfl⟩ := hr
    intro i j he
    exact h.get_inj (by simpa using he))
  (by
    obtain ⟨f, h, rfl⟩ := hr
    intro j
    exact ⟨h.inv.get j, by simp⟩)

@[simp] theorem top_perm (f : Fin m → Perm n) (h : Perm m) (hr) : top hn (perm hn f h) hr = h := by
  apply Perm.ext
  intro j
  simp [top]

/-- A base factor is read from the block sent to its destination by the top
permutation. This follows the destination-indexed multiplication convention. -/
@[expose] def basePoint (j : Fin m) (i : Fin n) : Fin n :=
  point hn (r.get (index i ((top hn r hr).inv.get j)))

@[simp] theorem basePoint_perm (f : Fin m → Perm n) (h : Perm m) (hr) (j : Fin m) (i : Fin n) :
    basePoint hn (perm hn f h) hr j i = (f j).get i := by simp [basePoint]

@[expose] def base (j : Fin m) : Perm n := Perm.ofFn (basePoint hn r hr j)
  (by
    obtain ⟨f, h, rfl⟩ := hr
    intro i k he
    exact (f j).get_inj (by simpa using he))
  (by
    obtain ⟨f, h, rfl⟩ := hr
    intro i
    exact ⟨(f j).inv.get i, by simp⟩)

@[simp] theorem base_perm (f : Fin m → Perm n) (h : Perm m) (hr) (j : Fin m) :
    base hn (perm hn f h) hr j = f j := by
  apply Perm.ext
  intro i
  simp [base]

theorem reconstruct : perm hn (base hn r hr) (top hn r hr) = r := by
  obtain ⟨f, h, rfl⟩ := hr
  rw [top_perm]
  congr 1
  funext j
  exact base_perm ..

end Hex.Perm.Wreath
