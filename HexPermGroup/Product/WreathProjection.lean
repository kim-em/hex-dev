/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexPermGroup.Product.WreathPerm

public section

namespace Hex.Perm.Wreath

variable (r : Perm (n * m))
  (hr : ∃ (f : Fin m → Perm n) (h : Perm m), r = perm f h)

/-- Read the destination of each block using its first point. Empty blocks
carry no points, so the top permutation is then the identity. -/
@[expose] def topPoint (j : Fin m) : Fin m :=
  if hn : 0 < n then block (r.get (index ⟨0, hn⟩ j)) else j

@[simp] theorem topPoint_perm (hn : 0 < n) (f : Fin m → Perm n) (h : Perm m) (j : Fin m) :
    topPoint (perm f h) j = h.get j := by simp [topPoint, hn]

theorem topPoint_of_not_pos (hn : ¬0 < n) (j : Fin m) : topPoint r j = j := by
  simp [topPoint, hn]

@[expose] def top : Perm m := Perm.ofFn (topPoint r)
  (by
    intro i j he
    by_cases hn : 0 < n
    · obtain ⟨f, h, rfl⟩ := hr
      exact h.get_inj (by simpa [hn] using he)
    · simpa [topPoint_of_not_pos r hn] using he)
  (by
    intro j
    by_cases hn : 0 < n
    · obtain ⟨f, h, rfl⟩ := hr
      exact ⟨h.inv.get j, by simp [hn]⟩
    · exact ⟨j, topPoint_of_not_pos r hn j⟩)

@[simp] theorem top_perm (hn : 0 < n) (f : Fin m → Perm n) (h : Perm m) (hr) : top (perm f h) hr = h := by
  apply Perm.ext
  intro j
  simp [top, hn]

theorem top_of_not_pos (hn : ¬0 < n) : top r hr = Perm.id m := by
  apply Perm.ext
  intro j
  simp [top, topPoint_of_not_pos r hn]

/-- A base factor is read from the block sent to its destination by the top
permutation. This follows the destination-indexed multiplication convention. -/
@[expose] def basePoint (j : Fin m) (i : Fin n) : Fin n :=
  point (r.get (index i ((top r hr).inv.get j)))

@[simp] theorem basePoint_perm (f : Fin m → Perm n) (h : Perm m) (hr) (j : Fin m) (i : Fin n) :
    basePoint (perm f h) hr j i = (f j).get i := by simp [basePoint, i.pos]

@[expose] def base (j : Fin m) : Perm n := Perm.ofFn (basePoint r hr j)
  (by
    obtain ⟨f, h, rfl⟩ := hr
    intro i k he
    exact (f j).get_inj (by simpa using he))
  (by
    obtain ⟨f, h, rfl⟩ := hr
    intro i
    exact ⟨(f j).inv.get i, by simp⟩)

@[simp] theorem base_perm (f : Fin m → Perm n) (h : Perm m) (hr) (j : Fin m) :
    base (perm f h) hr j = f j := by
  apply Perm.ext
  intro i
  simp [base]

theorem reconstruct : perm (base r hr) (top r hr) = r := by
  by_cases hn : 0 < n
  · obtain ⟨f, h, rfl⟩ := hr
    rw [top_perm hn]
    congr 1
    funext j
    exact base_perm ..
  · apply Perm.ext
    intro x
    exact absurd (pos_of_lt_mul x) hn

end Hex.Perm.Wreath
