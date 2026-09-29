/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexPolyMathlib.Interpret

public section

namespace Hex.RealClosure.Transport

variable {E : Type u} {K : Type v} [Zero E] [DecidableEq E] [Zero K] [DecidableEq K]

/-- Interpret the stored finite coefficient array and normalize its image.
No field laws or global zero reflection on the source expressions are needed. -/
@[expose] def polynomial (read : E → K) (p : Hex.DensePoly E) : Hex.DensePoly K :=
  Hex.DensePoly.ofCoeffs (p.toArray.map read)

/-- Zero preservation interprets implicit coefficients beyond the stored array. -/
theorem polynomial_coeff (read : E → K) (zero : read 0 = 0)
    (p : Hex.DensePoly E) (i : Nat) :
    (polynomial read p).coeff i = read (p.coeff i) := by
  rw [polynomial, Hex.DensePoly.coeff_ofCoeffs]
  rw [Array.getD_eq_getD_getElem?, Array.getElem?_map]
  cases h : p.toArray[i]? with
  | none =>
    have coefficient : p.coeff i = 0 := by
      rw [← Hex.DensePoly.toArray_getD, Array.getD_eq_getD_getElem?, h]
      rfl
    simp only [Option.map_none, Option.getD_none, coefficient, zero]
    rfl
  | some a =>
    have coefficient : p.coeff i = a := by
      rw [← Hex.DensePoly.toArray_getD, Array.getD_eq_getD_getElem?, h]
      rfl
    simp only [Option.map_some, Option.getD_some, coefficient]

/-- Normalizing either side gives the same interpreted finite array, even
when nonzero source coefficients acquire zero images. -/
theorem polynomial_ofCoeffs (read : E → K) (zero : read 0 = 0) (a : Array E) :
    polynomial read (Hex.DensePoly.ofCoeffs a) = Hex.DensePoly.ofCoeffs (a.map read) := by
  apply Hex.DensePoly.ext_coeff
  intro i
  rw [polynomial_coeff read zero, Hex.DensePoly.coeff_ofCoeffs,
    Hex.DensePoly.coeff_ofCoeffs]
  rw [Array.getD_eq_getD_getElem?, Array.getD_eq_getD_getElem?, Array.getElem?_map]
  cases h : a[i]? with
  | none =>
    simp only [Option.map_none, Option.getD_none]
    exact zero
  | some value =>
    simp only [Option.map_some, Option.getD_some]

/-- Only the stored coefficient zero pattern is needed for polynomial zero reflection. -/
theorem polynomial_zero (read : E → K) (zero : read 0 = 0) (p : Hex.DensePoly E)
    (reflects : ∀ i < p.size, read (p.coeff i) = 0 ↔ p.coeff i = 0) :
    polynomial read p = 0 ↔ p = 0 := by
  constructor
  · intro mapped
    apply Hex.DensePoly.ext_coeff
    intro i
    rw [Hex.DensePoly.coeff_zero]
    by_cases hi : i < p.size
    · apply (reflects i hi).mp
      rw [← polynomial_coeff read zero, mapped, Hex.DensePoly.coeff_zero]
    · exact Hex.DensePoly.coeff_eq_zero_of_size_le p (Nat.le_of_not_gt hi)
  · intro original
    subst p
    apply Hex.DensePoly.ext_coeff
    intro i
    rw [polynomial_coeff read zero, Hex.DensePoly.coeff_zero, zero, Hex.DensePoly.coeff_zero]

/-- Finite zero reflection preserves the actual normalized array length. -/
theorem polynomial_size (read : E → K) (zero : read 0 = 0) (p : Hex.DensePoly E)
    (reflects : ∀ i < p.size, read (p.coeff i) = 0 ↔ p.coeff i = 0) :
    (polynomial read p).size = p.size := by
  have upper : (polynomial read p).size ≤ p.size := by
    simpa only [polynomial, Array.size_map, Hex.DensePoly.toArray_size] using
      Hex.DensePoly.size_ofCoeffs_le (p.toArray.map read)
  apply Nat.le_antisymm upper
  by_cases empty : p.size = 0
  · omega
  · have positive : 0 < p.size := Nat.pos_of_ne_zero empty
    have last : read (p.coeff (p.size - 1)) ≠ 0 :=
      (reflects (p.size - 1) (by omega)).not.mpr
        (Hex.DensePoly.coeff_last_ne_zero_of_pos_size p positive)
    rw [← polynomial_coeff read zero] at last
    by_contra small
    exact last (Hex.DensePoly.coeff_eq_zero_of_size_le _ (by omega))

/-- Degree preservation uses the same finite coefficient pattern. -/
theorem polynomial_degree (read : E → K) (zero : read 0 = 0) (p : Hex.DensePoly E)
    (reflects : ∀ i < p.size, read (p.coeff i) = 0 ↔ p.coeff i = 0) :
    (polynomial read p).natDegree = p.natDegree := by
  rw [Hex.DensePoly.natDegree_eq_size_sub_one, polynomial_size read zero p reflects,
    Hex.DensePoly.natDegree_eq_size_sub_one]

/-- The actual executable zero test is retained by finite coefficient interpretation. -/
theorem polynomial_isZero (read : E → K) (zero : read 0 = 0) (p : Hex.DensePoly E)
    (reflects : ∀ i < p.size, read (p.coeff i) = 0 ↔ p.coeff i = 0) :
    (polynomial read p).isZero = p.isZero := by
  change ((polynomial read p).size == 0) = (p.size == 0)
  rw [polynomial_size read zero p reflects]

/-- Addition uses only the recorded scalar sums and input coefficient zero
patterns. No source ring laws or global arithmetic-preservation law is assumed. -/
theorem polynomial_add [Add E] [Add K] (read : E → K) (zero : read 0 = 0)
    (p q : Hex.DensePoly E)
    (first : ∀ i < p.size, read (p.coeff i) = 0 ↔ p.coeff i = 0)
    (second : ∀ i < q.size, read (q.coeff i) = 0 ↔ q.coeff i = 0)
    (sums : ∀ i < max p.size q.size,
      read (p.coeff i + q.coeff i) = read (p.coeff i) + read (q.coeff i)) :
    polynomial read (p + q) = polynomial read p + polynomial read q := by
  change polynomial read (Hex.DensePoly.add p q) = Hex.DensePoly.add _ _
  rw [Hex.DensePoly.add_eq_addImpl, Hex.DensePoly.addImpl,
    polynomial_ofCoeffs read zero, Hex.DensePoly.add_eq_addImpl, Hex.DensePoly.addImpl]
  congr 1
  apply Array.ext
  · simp only [Array.size_map, Array.size_ofFn,
      polynomial_size read zero p first, polynomial_size read zero q second]
  · intro i hi hi'
    simp only [Array.getElem_map, Array.getElem_ofFn, polynomial_coeff read zero]
    apply sums i
    simpa only [Array.size_map, Array.size_ofFn] using hi

/-- Subtraction transports the recorded scalar differences at their actual
coefficient positions, with no ring laws on the source expressions. -/
theorem polynomial_sub [Sub E] [Sub K] (read : E → K) (zero : read 0 = 0)
    (p q : Hex.DensePoly E)
    (first : ∀ i < p.size, read (p.coeff i) = 0 ↔ p.coeff i = 0)
    (second : ∀ i < q.size, read (q.coeff i) = 0 ↔ q.coeff i = 0)
    (differences : ∀ i < max p.size q.size,
      read (p.coeff i - q.coeff i) = read (p.coeff i) - read (q.coeff i)) :
    polynomial read (p - q) = polynomial read p - polynomial read q := by
  change polynomial read (Hex.DensePoly.sub p q) = Hex.DensePoly.sub _ _
  rw [Hex.DensePoly.sub_eq_subImpl, Hex.DensePoly.subImpl,
    polynomial_ofCoeffs read zero, Hex.DensePoly.sub_eq_subImpl, Hex.DensePoly.subImpl]
  congr 1
  apply Array.ext
  · simp only [Array.size_map, Array.size_ofFn,
      polynomial_size read zero p first, polynomial_size read zero q second]
  · intro i hi hi'
    simp only [Array.getElem_map, Array.getElem_ofFn, polynomial_coeff read zero]
    apply differences i
    simpa only [Array.size_map, Array.size_ofFn] using hi

end Hex.RealClosure.Transport

/-- info: 'Hex.RealClosure.Transport.polynomial_coeff' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Transport.polynomial_coeff

/-- info: 'Hex.RealClosure.Transport.polynomial_ofCoeffs' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Transport.polynomial_ofCoeffs

/-- info: 'Hex.RealClosure.Transport.polynomial_zero' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Transport.polynomial_zero

/-- info: 'Hex.RealClosure.Transport.polynomial_size' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Transport.polynomial_size

/-- info: 'Hex.RealClosure.Transport.polynomial_degree' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Transport.polynomial_degree

/-- info: 'Hex.RealClosure.Transport.polynomial_isZero' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Transport.polynomial_isZero

/-- info: 'Hex.RealClosure.Transport.polynomial_add' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Transport.polynomial_add

/-- info: 'Hex.RealClosure.Transport.polynomial_sub' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Transport.polynomial_sub
