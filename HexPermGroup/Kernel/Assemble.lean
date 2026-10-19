/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexPermGroup.Kernel.Images

public section

namespace Hex.PermGroup.Kernel

variable {n : Nat}

theorem levelsOk_cons_of {L : Level} {rest : List Level} {N : Nat}
    (hl : levelOk n (width n) (ident n (width n)) L rest = true)
    (hN : Nat.mul L.gens.length L.size = N)
    (hp : pairsOk n (width n) (ident n (width n)) L rest 0 N = true)
    (hr : levelsOk n (width n) (ident n (width n)) rest = true) :
    levelsOk n (width n) (ident n (width n)) (L :: rest) = true := by
  subst hN
  simp only [levelsOk, hl, hp, hr, Bool.and_self]

theorem levelsOk_nil : levelsOk n (width n) (ident n (width n)) [] = true := rfl

theorem check_of {inputs : List Nat} {c : Certificate}
    (hi : inputsOk n (width n) (ident n (width n)) inputs c = true)
    (hl : levelsOk n (width n) (ident n (width n)) c = true) : check n inputs c = true := by
  simp only [check, hi, hl, Bool.and_self]


/-- Combine the per-generator packing ties. -/
theorem pack_nil : ([] : List (Perm n)).map pack = [] := rfl

theorem pack_cons {g : Perm n} {gs : List (Perm n)} {x : Nat} {xs : List Nat}
    (h : pack g = x) (t : gs.map pack = xs) : (g :: gs).map pack = x :: xs := by
  simp [h, ← t]

theorem check_list {gs : List (Perm n)} {inputs : List Nat} {c : Certificate}
    (hS : gs.map pack = inputs) (h : check n inputs c = true) :
    check n (gs.toArray.toList.map pack) c = true := by
  simpa [hS] using h

theorem hasOrder_of_check {gs : List (Perm n)} {inputs : List Nat} {c : Certificate}
    {N : Nat} (hS : gs.map pack = inputs) (h : check n inputs c = true)
    (hN : order c = N) : HasOrder gs.toArray N := by
  rw [← hN]
  exact order_of_check (check_list hS h)

theorem generated_of_check {gs : List (Perm n)} {inputs : List Nat} {c : Certificate}
    {g : Perm n} {x : Nat} (hS : gs.map pack = inputs) (h : check n inputs c = true)
    (hx : pack g = x) (hs : Kernel.sift n (width n) (ident n (width n)) c x = true) :
    Generated gs.toArray g :=
  (sift_pack_iff (check_list hS h) g).mp (hx ▸ hs)

theorem not_generated_of_check {gs : List (Perm n)} {inputs : List Nat} {c : Certificate}
    {g : Perm n} {x : Nat} (hS : gs.map pack = inputs) (h : check n inputs c = true)
    (hx : pack g = x) (hs : Kernel.sift n (width n) (ident n (width n)) c x = false) :
    ¬ Generated gs.toArray g := by
  intro hg
  have ht := (sift_pack_iff (check_list hS h) g).mpr hg
  rw [hx, hs] at ht
  exact Bool.false_ne_true ht

end Hex.PermGroup.Kernel
