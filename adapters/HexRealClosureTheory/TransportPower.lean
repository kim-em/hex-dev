/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRealClosureTheory.TransportArithmetic

public section

namespace Hex.RealClosure.Transport

variable {E : Type u} {K : Type v} [Zero E] [DecidableEq E] [CommRing K] [DecidableEq K]

/-- Constants commute with coefficient interpretation even when they become zero. -/
theorem polynomial_C (read : E → K) (zero : read 0 = 0) (c : E) :
    polynomial read (Hex.DensePoly.C c) = Hex.DensePoly.C (read c) := by
  apply Hex.DensePoly.ext_coeff
  intro i
  rw [polynomial_coeff read zero, Hex.DensePoly.coeff_C, Hex.DensePoly.coeff_C]
  by_cases first : i = 0
  · simp only [ite_eq_left first]
  · simp only [ite_eq_right first]
    exact zero

variable [One E]

/-- The literal unit polynomial transports from the scalar unit equation. -/
theorem polynomial_one (read : E → K) (zero : read 0 = 0) (one : read 1 = 1) :
    polynomial read (1 : Hex.DensePoly E) = 1 := by
  change polynomial read (Hex.DensePoly.C 1) = Hex.DensePoly.C 1
  rw [polynomial_C read zero, one]

variable [Add E] [Mul E]

/-- Finite scalar obligations along the native binary-power recursion. Each
exponent above one records its actual square and, at odd exponents, its final product. -/
@[expose] def PowerData (read : E → K) (p : Hex.DensePoly E) (n : Nat) : Prop :=
  if n = 0 then True else if n = 1 then True else
    Product read p p ∧ PowerData read (p * p) (n / 2) ∧
      (if n % 2 = 0 then True else Product read ((p * p).natPow (n / 2)) p)
termination_by n
decreasing_by omega

/-- Natural powers transport the actual binary exponentiation tree from its
finite multiplication obligations, without source ring laws. -/
theorem polynomial_natPow (read : E → K) (zero : read 0 = 0) (one : read 1 = 1)
    (p : Hex.DensePoly E) (n : Nat) (data : PowerData read p n) :
    polynomial read (p.natPow n) = (polynomial read p).natPow n := by
  induction n using Nat.strongRecOn generalizing p with
  | ind n ih =>
    conv_lhs => rw [Hex.DensePoly.natPow]
    conv_rhs => rw [Hex.DensePoly.natPow]
    by_cases empty : n = 0
    · rw [ite_eq_left empty, ite_eq_left empty]
      exact polynomial_one read zero one
    · rw [ite_eq_right empty, ite_eq_right empty]
      by_cases unit : n = 1
      · rw [ite_eq_left unit, ite_eq_left unit]
      rw [ite_eq_right unit, ite_eq_right unit]
      rw [PowerData, ite_eq_right empty, ite_eq_right unit] at data
      have square := Ring.polynomial_mul read zero p p data.1.products data.1.sums
      have recursive := ih (n / 2) (by omega) (p * p) data.2.1
      rw [square] at recursive
      by_cases even : n % 2 = 0
      · rw [ite_eq_left even, ite_eq_left even]
        exact recursive
      · rw [ite_eq_right even] at data
        rw [ite_eq_right even, ite_eq_right even]
        rw [Ring.polynomial_mul read zero _ p data.2.2.products data.2.2.sums, recursive]

end Hex.RealClosure.Transport

/-- info: 'Hex.RealClosure.Transport.polynomial_C' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Transport.polynomial_C
/-- info: 'Hex.RealClosure.Transport.polynomial_one' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Transport.polynomial_one
/-- info: 'Hex.RealClosure.Transport.polynomial_natPow' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Transport.polynomial_natPow
