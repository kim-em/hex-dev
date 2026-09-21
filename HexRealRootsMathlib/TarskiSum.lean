/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRealRoots.Tarski
public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.Basic.Sign.Basic
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Contrapose

public section
namespace HexRealRootsMathlib.Tarski

open Hex Polynomial
variable {R : Type*} [Field R] [LinearOrder R]

/-- Membership in an open interval with possibly infinite endpoints. -/
def InInterval (a b : Endpoint R) (x : R) : Prop :=
  (match a with | .negInf => True | .finite a => a < x | .posInf => False) ∧
  (match b with | .posInf => True | .finite b => x < b | .negInf => False)

/-- The distinct roots in the open interval. This is a semantic finite set,
not an executable root enumeration. -/
noncomputable def rootsIn (p : Polynomial R) (a b : Endpoint R) : Finset R := by
  classical
  exact p.roots.toFinset.filter (InInterval a b)

/-- The mathematical Sturm–Tarski sum. Relating it to the executable query
requires the separately owned signed-remainder theorem. -/
noncomputable def rootSum (p f : Polynomial R) (a b : Endpoint R) : Int :=
  ∑ x ∈ rootsIn p a b, (SignType.sign (f.eval x) : Int)

@[simp] theorem rootSum_zero (p : Polynomial R) (a b : Endpoint R) :
    rootSum p 0 a b = 0 := by simp [rootSum]

@[simp] theorem rootSum_one [IsStrictOrderedRing R] (p : Polynomial R) (a b : Endpoint R) :
    rootSum p 1 a b = (rootsIn p a b).card := by simp [rootSum]

theorem rootSum_singleton (p f : Polynomial R) (a b : Endpoint R) (x : R)
    (h : rootsIn p a b = {x}) : rootSum p f a b = (SignType.sign (f.eval x) : Int) := by
  simp [rootSum, h]

/-- A common root contributes zero to the signed sum. -/
theorem contribution_zero (f : Polynomial R) (x : R) (h : f.IsRoot x) :
    (SignType.sign (f.eval x) : Int) = 0 := by simp [h.eq_zero]

/-- Restricting to nonzero query evaluations removes only zero contributions. -/
theorem rootSum_filter (p f : Polynomial R) (a b : Endpoint R) :
    rootSum p f a b = ∑ x ∈ (rootsIn p a b).filter (fun x => f.eval x ≠ 0),
      (SignType.sign (f.eval x) : Int) := by
  classical
  symm
  apply Finset.sum_filter_of_ne
  intro x _ hx
  contrapose! hx
  simp [hx]

theorem rootSum_eq_zero (p f : Polynomial R) (a b : Endpoint R)
    (h : ∀ x ∈ rootsIn p a b, f.eval x = 0) : rootSum p f a b = 0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp [h x hx]

/-- Divisibility includes zero initial query remainder without a coprimality assumption. -/
theorem rootSum_of_dvd (p f : Polynomial R) (a b : Endpoint R) (h : p ∣ f) :
    rootSum p f a b = 0 := by
  classical
  apply rootSum_eq_zero
  intro x hx
  have hx' : x ∈ p.roots := Multiset.mem_toFinset.mp (Finset.mem_filter.mp hx).1
  obtain ⟨q, rfl⟩ := h
  simp [Polynomial.eval_mul, (Polynomial.isRoot_of_mem_roots hx').eq_zero]

theorem rootsIn_card_le (p : Polynomial R) (a b : Endpoint R) :
    (rootsIn p a b).card ≤ p.natDegree := by
  classical
  exact (Finset.card_filter_le _ _).trans
    ((Multiset.toFinset_card_le _).trans (Polynomial.card_roots' p))

theorem abs_rootSum_le (p f : Polynomial R) (a b : Endpoint R) :
    |rootSum p f a b| ≤ (rootsIn p a b).card := by
  unfold rootSum
  calc
    |∑ x ∈ rootsIn p a b, (SignType.sign (f.eval x) : Int)| ≤
        ∑ x ∈ rootsIn p a b, |(SignType.sign (f.eval x) : Int)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _x ∈ rootsIn p a b, (1 : Int) := by
      apply Finset.sum_le_sum
      intro x _
      cases SignType.sign (f.eval x) <;> norm_num [SignType.cast]
    _ = _ := by simp

theorem abs_rootSum_le_degree (p f : Polynomial R) (a b : Endpoint R) :
    |rootSum p f a b| ≤ p.natDegree :=
  (abs_rootSum_le p f a b).trans (by exact_mod_cast rootsIn_card_le p a b)

@[simp] theorem rootsIn_const (c : R) (a b : Endpoint R) : rootsIn (C c) a b = ∅ := by
  classical
  simp [rootsIn]

@[simp] theorem rootSum_const (c : R) (f : Polynomial R) (a b : Endpoint R) :
    rootSum (C c) f a b = 0 := by simp [rootSum]

end HexRealRootsMathlib.Tarski
