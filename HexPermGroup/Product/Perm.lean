/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexPermGroup.Conjugate

public section

namespace Hex.Perm

namespace Sum

/-- Consecutive disjoint supports retain the full declared factor degrees. -/
@[expose] def act (p : Perm n) (q : Perm m) : Fin (n + m) → Fin (n + m) :=
  Fin.addCases (fun i => (p.get i).castAdd m) (fun j => (q.get j).natAdd n)

@[simp] theorem act_left (p : Perm n) (q : Perm m) (i : Fin n) :
    act p q (i.castAdd m) = (p.get i).castAdd m := by simp [act]

@[simp] theorem act_right (p : Perm n) (q : Perm m) (i : Fin m) :
    act p q (i.natAdd n) = (q.get i).natAdd n := by simp [act]

@[simp] theorem inv_act (p : Perm n) (q : Perm m) (i : Fin (n + m)) :
    act p.inv q.inv (act p q i) = i := by
  refine Fin.addCases ?_ ?_ i <;> intro j <;> simp

end Sum

/-- The direct sum action of permutations on consecutive disjoint domains. -/
@[expose] def sum (p : Perm n) (q : Perm m) : Perm (n + m) :=
  ofFn (Sum.act p q)
    (fun i j h => by simpa using congrArg (Sum.act p.inv q.inv) h)
    (fun i => ⟨Sum.act p.inv q.inv i, by simpa using Sum.inv_act p.inv q.inv i⟩)

@[simp] theorem sum_left (p : Perm n) (q : Perm m) (i : Fin n) :
    (p.sum q).get (i.castAdd m) = (p.get i).castAdd m := by simp [sum]

@[simp] theorem sum_right (p : Perm n) (q : Perm m) (i : Fin m) :
    (p.sum q).get (i.natAdd n) = (q.get i).natAdd n := by simp [sum]

@[simp] theorem sum_id : (Perm.id n).sum (Perm.id m) = Perm.id (n + m) := by
  apply Perm.ext
  intro i
  refine Fin.addCases ?_ ?_ i <;> intro j <;> simp

theorem sum_comp (p r : Perm n) (q s : Perm m) :
    (p.comp r).sum (q.comp s) = (p.sum q).comp (r.sum s) := by
  apply Perm.ext
  intro i
  refine Fin.addCases ?_ ?_ i <;> intro j <;> simp

theorem sum_inv (p : Perm n) (q : Perm m) : p.inv.sum q.inv = (p.sum q).inv := by
  apply Perm.ext
  intro i
  apply (p.sum q).get_inj
  have he := congrArg (fun r : Perm (n + m) => r.get i) (sum_comp p p.inv q q.inv).symm
  simpa using he

theorem sum_injective {p r : Perm n} {q s : Perm m} (h : p.sum q = r.sum s) : p = r ∧ q = s := by
  constructor
  · apply Perm.ext
    intro i
    have he := congrArg (fun t : Perm (n + m) => (t.get (i.castAdd m)).val) h
    exact Fin.ext (by simpa using he)
  · apply Perm.ext
    intro i
    have he := congrArg (fun t : Perm (n + m) => (t.get (i.natAdd n)).val) h
    apply Fin.ext
    simpa using he

end Hex.Perm
