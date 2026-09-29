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
No field laws or global zero reflection on source expressions are needed. -/
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

/-- Nonvanishing of the interpreted top coefficient preserves normalized size. -/
theorem polynomial_size (read : E → K) (zero : read 0 = 0) (p : Hex.DensePoly E)
    (leading : 0 < p.size → read (p.coeff (p.size - 1)) ≠ 0) :
    (polynomial read p).size = p.size := by
  have upper : (polynomial read p).size ≤ p.size := by
    simpa only [polynomial, Array.size_map, Hex.DensePoly.toArray_size] using
      Hex.DensePoly.size_ofCoeffs_le (p.toArray.map read)
  apply Nat.le_antisymm upper
  by_cases empty : p.size = 0
  · omega
  · have positive : 0 < p.size := Nat.pos_of_ne_zero empty
    have last : read (p.coeff (p.size - 1)) ≠ 0 := leading positive
    rw [← polynomial_coeff read zero] at last
    by_contra small
    exact last (Hex.DensePoly.coeff_eq_zero_of_size_le _ (by omega))

/-- Nonvanishing of the top coefficient preserves polynomial zero testing.
Interior coefficients may be nonzero representatives of zero. -/
theorem polynomial_zero (read : E → K) (zero : read 0 = 0) (p : Hex.DensePoly E)
    (leading : 0 < p.size → read (p.coeff (p.size - 1)) ≠ 0) :
    polynomial read p = 0 ↔ p = 0 := by
  rw [← Hex.DensePoly.size_eq_zero_iff, ← Hex.DensePoly.size_eq_zero_iff,
    polynomial_size read zero p leading]

/-- The top-coefficient guard retains the entire stored coefficient array. -/
theorem polynomial_array (read : E → K) (zero : read 0 = 0) (p : Hex.DensePoly E)
    (leading : 0 < p.size → read (p.coeff (p.size - 1)) ≠ 0) :
    (polynomial read p).toArray = p.toArray.map read := by
  apply Array.ext
  · simp only [Hex.DensePoly.toArray_size, Array.size_map,
      polynomial_size read zero p leading]
  · intro i hi hi'
    simp only [Array.getElem_map]
    rw [Array.getElem_eq_getD (h := hi) (0 : K),
      Array.getElem_eq_getD (h := by simpa only [Array.size_map] using hi') (0 : E)]
    change (polynomial read p).coeff i = read (p.coeff i)
    exact polynomial_coeff read zero p i

/-- Degree preservation uses the same top-coefficient guard. -/
theorem polynomial_degree (read : E → K) (zero : read 0 = 0) (p : Hex.DensePoly E)
    (leading : 0 < p.size → read (p.coeff (p.size - 1)) ≠ 0) :
    (polynomial read p).natDegree = p.natDegree := by
  rw [Hex.DensePoly.natDegree_eq_size_sub_one, polynomial_size read zero p leading,
    Hex.DensePoly.natDegree_eq_size_sub_one]

/-- The leading coefficient of the interpreted polynomial is the image
of its stored leading coefficient under the top-coefficient guard. -/
theorem polynomial_leading (read : E → K) (zero : read 0 = 0) (p : Hex.DensePoly E)
    (leading : 0 < p.size → read (p.coeff (p.size - 1)) ≠ 0) :
    (polynomial read p).leadingCoeff = read p.leadingCoeff := by
  by_cases empty : p.size = 0
  · have original := (Hex.DensePoly.size_eq_zero_iff p).mp empty
    rw [original, (polynomial_zero read zero 0 (by simp)).mpr rfl,
      Hex.DensePoly.leadingCoeff_zero, Hex.DensePoly.leadingCoeff_zero]
    exact zero.symm
  · have positive : 0 < p.size := Nat.pos_of_ne_zero empty
    rw [Hex.DensePoly.leadingCoeff_eq_coeff_last _
      (by rw [polynomial_size read zero p leading]; exact positive),
      polynomial_size read zero p leading, polynomial_coeff read zero,
      Hex.DensePoly.leadingCoeff_eq_coeff_last p positive]

/-- The actual executable zero test is retained under the top-coefficient guard. -/
theorem polynomial_isZero (read : E → K) (zero : read 0 = 0) (p : Hex.DensePoly E)
    (leading : 0 < p.size → read (p.coeff (p.size - 1)) ≠ 0) :
    (polynomial read p).isZero = p.isZero := by
  change ((polynomial read p).size == 0) = (p.size == 0)
  rw [polynomial_size read zero p leading]

namespace Guarded

/-- Addition uses only the recorded scalar sums and input leading guards. No source ring laws or global arithmetic-preservation law is assumed. -/
theorem polynomial_add [Add E] [Add K] (read : E → K) (zero : read 0 = 0)
    (p q : Hex.DensePoly E)
    (first : 0 < p.size → read (p.coeff (p.size - 1)) ≠ 0)
    (second : 0 < q.size → read (q.coeff (q.size - 1)) ≠ 0)
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
coefficient positions, under input leading guards, with no ring laws on source expressions. -/
theorem polynomial_sub [Sub E] [Sub K] (read : E → K) (zero : read 0 = 0)
    (p q : Hex.DensePoly E)
    (first : 0 < p.size → read (p.coeff (p.size - 1)) ≠ 0)
    (second : 0 < q.size → read (q.coeff (q.size - 1)) ≠ 0)
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

/-- Scaling needs only the finitely recorded products with the input's
stored coefficients. The interpreted product may normalize to a smaller array. -/
theorem polynomial_scale [Mul E] [Mul K] (read : E → K) (zero : read 0 = 0)
    (scalar : E) (p : Hex.DensePoly E)
    (leading : 0 < p.size → read (p.coeff (p.size - 1)) ≠ 0)
    (products : ∀ i < p.size,
      read (scalar * p.coeff i) = read scalar * read (p.coeff i)) :
    polynomial read (Hex.DensePoly.scale scalar p) =
      Hex.DensePoly.scale (read scalar) (polynomial read p) := by
  rw [Hex.DensePoly.scale_eq_scaleImpl, Hex.DensePoly.scaleImpl,
    polynomial_ofCoeffs read zero, Hex.DensePoly.scale_eq_scaleImpl, Hex.DensePoly.scaleImpl]
  congr 1
  apply Array.ext
  · simp only [Array.size_map, Hex.DensePoly.toArray_size,
      polynomial_size read zero p leading]
  · intro i hi hi'
    simp only [Array.getElem_map]
    rw [Array.getElem_eq_getD (h := by simpa using hi) (0 : E),
      Array.getElem_eq_getD (h := by simpa using hi') (0 : K)]
    change read (scalar * p.coeff i) = read scalar * (polynomial read p).coeff i
    rw [polynomial_coeff read zero]
    exact products i (by simpa using hi)

/-- Differentiation transports only its actual finite cast-times-coefficient
operations. No natural-cast or multiplication law on every expression is assumed. -/
theorem polynomial_derivative [NatCast E] [Mul E] [NatCast K] [Mul K]
    (read : E → K) (zero : read 0 = 0) (p : Hex.DensePoly E)
    (leading : 0 < p.size → read (p.coeff (p.size - 1)) ≠ 0)
    (products : ∀ i < p.size - 1,
      read (((i + 1 : Nat) : E) * p.coeff (i + 1)) =
        ((i + 1 : Nat) : K) * read (p.coeff (i + 1))) :
    polynomial read p.derivative = (polynomial read p).derivative := by
  rw [Hex.DensePoly.derivative_eq_derivativeImpl, Hex.DensePoly.derivativeImpl,
    polynomial_ofCoeffs read zero, Hex.DensePoly.derivative_eq_derivativeImpl,
    Hex.DensePoly.derivativeImpl]
  congr 1
  apply Array.ext
  · simp only [Array.size_map, Array.size_ofFn, polynomial_size read zero p leading]
  · intro i hi hi'
    simp only [Array.getElem_map, Array.getElem_ofFn, polynomial_coeff read zero]
    exact products i (by simpa only [Array.size_map, Array.size_ofFn] using hi)

end Guarded

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

/-- info: 'Hex.RealClosure.Transport.Guarded.polynomial_add' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Transport.Guarded.polynomial_add

/-- info: 'Hex.RealClosure.Transport.Guarded.polynomial_sub' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Transport.Guarded.polynomial_sub

/-- info: 'Hex.RealClosure.Transport.polynomial_leading' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Transport.polynomial_leading

/-- info: 'Hex.RealClosure.Transport.Guarded.polynomial_scale' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Transport.Guarded.polynomial_scale

/-- info: 'Hex.RealClosure.Transport.Guarded.polynomial_derivative' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Transport.Guarded.polynomial_derivative

/-- info: 'Hex.RealClosure.Transport.polynomial_array' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Transport.polynomial_array
