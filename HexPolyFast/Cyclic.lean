/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexPolyFast.Plan

public section

/-!
# Cyclic and negacyclic products

The reference kernels fold an ordinary planned product by congruence classes
of exponents. They allocate exactly the requested `n` coefficient slots and
therefore also serve as independent comparators for transform-based plans.
-/

namespace Hex.DensePoly

universe u

attribute [local instance 1000] Lean.Grind.Semiring.ofNat

variable {R : Type u} [DecidableEq R] [Lean.Grind.CommRing R]

/-- Sum coefficients of `p` whose exponents are congruent to `k` modulo `n`. -/
def cyclicCoeff (n k : Nat) (p : DensePoly R) : R :=
  (List.range ((p.size + n - 1) / n)).foldl
    (fun acc t => acc + p.coeff (k + t * n)) 0

/-- Alternating sum of coefficients in one congruence class, implementing
reduction by `x^n = -1`. -/
def negacyclicCoeff (n k : Nat) (p : DensePoly R) : R :=
  (List.range ((p.size + n - 1) / n)).foldl
    (fun acc t =>
      if t % 2 = 0 then acc + p.coeff (k + t * n)
      else acc - p.coeff (k + t * n)) 0

/-- Cyclic convolution of positive length `n`. -/
def mulCyclic (plan : MulPlan R) (n : Nat) (_hn : 0 < n)
    (a b : DensePoly R) : DensePoly R :=
  let p := mulWith plan a b
  ofList ((List.range n).map fun k => cyclicCoeff n k p)

/-- Negacyclic convolution of positive length `n`. -/
def mulNegacyclic (plan : MulPlan R) (n : Nat) (_hn : 0 < n)
    (a b : DensePoly R) : DensePoly R :=
  let p := mulWith plan a b
  ofList ((List.range n).map fun k => negacyclicCoeff n k p)

/-- Checked cyclic convolution; length zero has no quotient-ring meaning. -/
def mulCyclic? (plan : MulPlan R) (n : Nat) (a b : DensePoly R) :
    Option (DensePoly R) :=
  if hn : 0 < n then some (mulCyclic plan n hn a b) else none

/-- Checked negacyclic convolution; length zero has no quotient-ring meaning. -/
def mulNegacyclic? (plan : MulPlan R) (n : Nat) (a b : DensePoly R) :
    Option (DensePoly R) :=
  if hn : 0 < n then some (mulNegacyclic plan n hn a b) else none

/-- Cyclic products contain at most `n` stored coefficients. -/
theorem size_mulCyclic_le (plan : MulPlan R) (n : Nat) (hn : 0 < n)
    (a b : DensePoly R) : (mulCyclic plan n hn a b).size ≤ n := by
  unfold mulCyclic
  exact Nat.le_trans (size_ofList_le _) (by simp)

/-- Negacyclic products contain at most `n` stored coefficients. -/
theorem size_mulNegacyclic_le (plan : MulPlan R) (n : Nat) (hn : 0 < n)
    (a b : DensePoly R) : (mulNegacyclic plan n hn a b).size ≤ n := by
  unfold mulNegacyclic
  exact Nat.le_trans (size_ofList_le _) (by simp)

/-- Coefficient description of cyclic folding. -/
theorem coeff_mulCyclic (plan : MulPlan R) (n : Nat) (hn : 0 < n)
    (a b : DensePoly R) (i : Nat) :
    (mulCyclic plan n hn a b).coeff i =
      if i < n then cyclicCoeff n i (a * b) else 0 := by
  unfold mulCyclic
  rw [coeff_ofList]
  by_cases hi : i < n
  · rw [_root_.ite_eq_left hi]
    simp [List.getD, hi, mulWith_eq]
  · rw [_root_.ite_eq_right hi, List.getD_eq_getElem?_getD]
    simp [hi]
    rfl

/-- Coefficient description of negacyclic folding. -/
theorem coeff_mulNegacyclic (plan : MulPlan R) (n : Nat) (hn : 0 < n)
    (a b : DensePoly R) (i : Nat) :
    (mulNegacyclic plan n hn a b).coeff i =
      if i < n then negacyclicCoeff n i (a * b) else 0 := by
  unfold mulNegacyclic
  rw [coeff_ofList]
  by_cases hi : i < n
  · rw [_root_.ite_eq_left hi]
    simp [List.getD, hi, mulWith_eq]
  · rw [_root_.ite_eq_right hi, List.getD_eq_getElem?_getD]
    simp [hi]
    rfl

end Hex.DensePoly
