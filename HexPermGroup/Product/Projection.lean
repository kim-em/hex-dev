/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexPermGroup.Product.Perm

public section

namespace Hex.Perm.Sum

variable (r : Perm (n + m)) (h : ∃ (p : Perm n) (q : Perm m), r = p.sum q)

/-- Restrict to the first consecutive support. The existence proof supplies
only bounds; the executable map reads the original permutation array. -/
@[expose] def leftPoint (i : Fin n) : Fin n :=
  ⟨(r.get (i.castAdd m)).val, by
    obtain ⟨p, q, rfl⟩ := h
    simp⟩

/-- Restrict to the second support and remove its declared offset. -/
@[expose] def rightPoint (i : Fin m) : Fin m :=
  ⟨(r.get (i.natAdd n)).val - n, by
    obtain ⟨p, q, rfl⟩ := h
    simp⟩

@[simp] theorem leftPoint_sum (p : Perm n) (q : Perm m) (h) (i : Fin n) :
    leftPoint (p.sum q) h i = p.get i := by
  apply Fin.ext
  simp [leftPoint]

@[simp] theorem rightPoint_sum (p : Perm n) (q : Perm m) (h) (i : Fin m) :
    rightPoint (p.sum q) h i = q.get i := by
  apply Fin.ext
  simp [rightPoint]

@[expose] def left : Perm n := Perm.ofFn (leftPoint r h)
  (by
    obtain ⟨p, q, rfl⟩ := h
    intro i j he
    exact p.get_inj (by simpa using he))
  (by
    obtain ⟨p, q, rfl⟩ := h
    intro i
    exact ⟨p.inv.get i, by simp⟩)

@[expose] def right : Perm m := Perm.ofFn (rightPoint r h)
  (by
    obtain ⟨p, q, rfl⟩ := h
    intro i j he
    exact q.get_inj (by simpa using he))
  (by
    obtain ⟨p, q, rfl⟩ := h
    intro i
    exact ⟨q.inv.get i, by simp⟩)

@[simp] theorem left_sum (p : Perm n) (q : Perm m) (h) : left (p.sum q) h = p := by
  apply Perm.ext
  intro i
  simp [left]

@[simp] theorem right_sum (p : Perm n) (q : Perm m) (h) : right (p.sum q) h = q := by
  apply Perm.ext
  intro i
  simp [right]

theorem reconstruct : (left r h).sum (right r h) = r := by
  obtain ⟨p, q, rfl⟩ := h
  simp

end Hex.Perm.Sum
