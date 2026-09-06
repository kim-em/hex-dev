/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexNumberField.Roots
public import HexNumberFieldMathlib.AdjoinRoot
public import HexPolyMathlib.Euclid
public import Mathlib.Algebra.Polynomial.FieldDivision

public section

/-!
# Semantics of the fixed-field Yun decomposition

This module relates the executable dense-polynomial Yun loop to root
multiplicities after an injective embedding of the coefficient field.
-/

namespace Hex.PolyQuot.Roots

open scoped QAdjoinField

variable {p : ZPoly} {x : SimpleRoot p}

/-- Interpret an executable fixed-field polynomial after a field embedding. -/
noncomputable def toPolynomialMap [ZPoly.CheckedIrreducible p]
    {K : Type*} [Semiring K]
    (embedding : PolyQuot p x →+* K) (f : DensePoly (PolyQuot p x)) :
    Polynomial K :=
  (HexPolyMathlib.toPolynomial f).map embedding

/-- Unfolding rule for the polynomial interpretation used by the Yun proofs. -/
theorem toPolynomialMap_eq_map [ZPoly.CheckedIrreducible p]
    {K : Type*} [Semiring K]
    (embedding : PolyQuot p x →+* K) (f : DensePoly (PolyQuot p x)) :
    toPolynomialMap embedding f =
      (HexPolyMathlib.toPolynomial f).map embedding := by
  rfl

private theorem rat_smul_natCast [ZPoly.CheckedIrreducible p]
    (n : Nat) (a : PolyQuot p x) :
    (n : Rat) • a = (n : PolyQuot p x) * a := by
  let rep : RefinedIsolation p := Quot.out x
  have hrep : SimpleRoot.mk rep = x := Quot.out_eq x
  apply PolyQuot.toComplex_injective rep hrep
  change PolyQuot.toComplex ((n : Rat) • a) rep hrep =
    PolyQuot.toComplex (((n : Rat) • (1 : PolyQuot p x)) * a) rep hrep
  rw [PolyQuot.map_smul, PolyQuot.map_mul, PolyQuot.map_smul,
    PolyQuot.map_one, mul_one]

private theorem derivative_eq_dense [ZPoly.CheckedIrreducible p]
    (f : DensePoly (PolyQuot p x)) :
    derivative f = f.derivative := by
  apply DensePoly.ext_coeff
  intro n
  unfold derivative
  rw [DensePoly.coeff_ofCoeffs,
    DensePoly.coeff_derivative f n (by exact mul_zero _)]
  by_cases hn : n < f.size - 1
  · simp [hn]
    simpa only [Nat.cast_add, Nat.cast_one] using
      rat_smul_natCast (p := p) (x := x) (n + 1) (f.coeff (n + 1))
  · have hcoeff : f.coeff (n + 1) = 0 :=
      DensePoly.coeff_eq_zero_of_size_le f (by omega)
    simp [hn, hcoeff]
    rfl

/-- The executable fixed-field derivative agrees with the Mathlib derivative
after dense-polynomial transport. -/
theorem toPolynomial_derivative [ZPoly.CheckedIrreducible p]
    (f : DensePoly (PolyQuot p x)) :
    HexPolyMathlib.toPolynomial (derivative f) =
      Polynomial.derivative (HexPolyMathlib.toPolynomial f) := by
  rw [derivative_eq_dense]
  exact HexPolyMathlib.toPolynomial_derivative f

/-- The multiplicity of a root of a polynomial gcd is the minimum of its
multiplicities in the two nonzero inputs. -/
theorem rootMultiplicity_gcd {K : Type*} [Field K] [DecidableEq K]
    (f g : Polynomial K) (hf : f ≠ 0) (hg : g ≠ 0) (z : K) :
    (EuclideanDomain.gcd f g).rootMultiplicity z =
      min (f.rootMultiplicity z) (g.rootMultiplicity z) := by
  classical
  have hgcd : EuclideanDomain.gcd f g ≠ 0 := by
    intro h
    exact hf (EuclideanDomain.gcd_eq_zero_iff.mp h).1
  apply le_antisymm
  · exact le_min
      (Polynomial.rootMultiplicity_le_rootMultiplicity_of_dvd hf
        (EuclideanDomain.gcd_dvd_left f g) z)
      (Polynomial.rootMultiplicity_le_rootMultiplicity_of_dvd
        hg
        (EuclideanDomain.gcd_dvd_right f g) z)
  · rw [Polynomial.le_rootMultiplicity_iff hgcd]
    apply EuclideanDomain.dvd_gcd
    · rw [← Polynomial.le_rootMultiplicity_iff hf]
      exact min_le_left _ _
    · rw [← Polynomial.le_rootMultiplicity_iff hg]
      exact min_le_right _ _

/-- Root multiplicity subtracts across an exact polynomial quotient. -/
theorem rootMultiplicity_of_mul_eq {K : Type*} [Field K]
    (quotient divisor dividend : Polynomial K) (hdividend : dividend ≠ 0)
    (hreconstruct : quotient * divisor = dividend) (z : K) :
    quotient.rootMultiplicity z =
      dividend.rootMultiplicity z - divisor.rootMultiplicity z := by
  have hproduct : quotient * divisor ≠ 0 := by simpa [hreconstruct]
  have hmultiplicity := Polynomial.rootMultiplicity_mul (x := z) hproduct
  rw [hreconstruct] at hmultiplicity
  omega

/-- A root's multiplicity is bounded by the degree of a nonzero polynomial. -/
theorem rootMultiplicity_le_natDegree {K : Type*} [Field K]
    (f : Polynomial K) (hf : f ≠ 0) (z : K) :
    f.rootMultiplicity z ≤ f.natDegree := by
  have hdegree := Polynomial.natDegree_le_of_dvd
    (Polynomial.pow_rootMultiplicity_dvd f z) hf
  simpa using hdegree

/-- Executable field division subtracts root multiplicities when the divisor
is known to divide the nonzero dividend. -/
theorem rootMultiplicity_div {K : Type*} [Field K] [DecidableEq K]
    (dividend divisor : DensePoly K) (hdivisor : divisor ∣ dividend)
    (hdividend : HexPolyMathlib.toPolynomial dividend ≠ 0) (z : K) :
    (HexPolyMathlib.toPolynomial (dividend / divisor)).rootMultiplicity z =
      (HexPolyMathlib.toPolynomial dividend).rootMultiplicity z -
        (HexPolyMathlib.toPolynomial divisor).rootMultiplicity z := by
  have hmod : dividend % divisor = 0 :=
    DensePoly.mod_eq_zero_of_dvd dividend divisor hdivisor
  have hreconstruct := DensePoly.div_mul_add_mod dividend divisor
  rw [hmod] at hreconstruct
  have hpolynomial := congrArg HexPolyMathlib.toPolynomial hreconstruct
  simp only [HexPolyMathlib.toPolynomial_add,
    HexPolyMathlib.toPolynomial_mul, HexPolyMathlib.toPolynomial_zero,
    add_zero] at hpolynomial
  exact rootMultiplicity_of_mul_eq _ _ _ hdividend hpolynomial z

/-- Monic normalization changes a nonzero polynomial only by a nonzero
constant factor, so it preserves every root multiplicity. -/
theorem rootMultiplicity_monic [ZPoly.CheckedIrreducible p]
    (f : DensePoly (PolyQuot p x))
    (hf : HexPolyMathlib.toPolynomial f ≠ 0) (z : PolyQuot p x) :
    (HexPolyMathlib.toPolynomial (monic f)).rootMultiplicity z =
      (HexPolyMathlib.toPolynomial f).rootMultiplicity z := by
  unfold monic
  split
  · rename_i hzero
    have hsize : f.size = 0 :=
      (DensePoly.isZero_eq_true_iff f).mp (by simpa using hzero)
    have hfzero : f = 0 := by
      apply DensePoly.ext_coeff
      intro n
      rw [DensePoly.coeff_zero]
      exact DensePoly.coeff_eq_zero_of_size_le f (by omega)
    exact (hf (by simp [hfzero])).elim
  · rw [HexPolyMathlib.toPolynomial_scale]
    have hleading : f.leadingCoeff ≠ 0 := by
      simpa only [← HexPolyMathlib.leadingCoeff_toPolynomial] using
        Polynomial.leadingCoeff_ne_zero.mpr hf
    have hconstant : Polynomial.C f.leadingCoeff⁻¹ ≠ 0 :=
      Polynomial.C_ne_zero.mpr (inv_ne_zero hleading)
    rw [Polynomial.rootMultiplicity_mul (mul_ne_zero hconstant hf),
      Polynomial.rootMultiplicity_C, zero_add]

/-- Monic normalization is associated to its nonzero input. -/
theorem toPolynomial_monic_associated [ZPoly.CheckedIrreducible p]
    (f : DensePoly (PolyQuot p x))
    (hf : HexPolyMathlib.toPolynomial f ≠ 0) :
    Associated (HexPolyMathlib.toPolynomial (monic f))
      (HexPolyMathlib.toPolynomial f) := by
  unfold monic
  split
  · rename_i hzero
    have hsize : f.size = 0 :=
      (DensePoly.isZero_eq_true_iff f).mp (by simpa using hzero)
    have hfzero : f = 0 := by
      apply DensePoly.ext_coeff
      intro n
      rw [DensePoly.coeff_zero]
      exact DensePoly.coeff_eq_zero_of_size_le f (by omega)
    exact (hf (by simp [hfzero])).elim
  · rw [HexPolyMathlib.toPolynomial_scale]
    have hleading : f.leadingCoeff ≠ 0 := by
      simpa only [← HexPolyMathlib.leadingCoeff_toPolynomial] using
        Polynomial.leadingCoeff_ne_zero.mpr hf
    exact associated_unit_mul_left _ _
      (Polynomial.isUnit_C.mpr (inv_ne_zero hleading).isUnit)

/-- Associated polynomials have the same root multiplicity. -/
theorem rootMultiplicity_associated {K : Type*} [Field K] [DecidableEq K]
    {f g : Polynomial K} (h : Associated f g) (z : K) :
    f.rootMultiplicity z = g.rootMultiplicity z := by
  rw [← Polynomial.count_roots, ← Polynomial.count_roots, h.roots_eq]

/-- The executable monic gcd realizes the pointwise minimum of root
multiplicities. -/
theorem rootMultiplicity_monicGcd [ZPoly.CheckedIrreducible p]
    (f g : DensePoly (PolyQuot p x))
    (hf : HexPolyMathlib.toPolynomial f ≠ 0)
    (hg : HexPolyMathlib.toPolynomial g ≠ 0) (z : PolyQuot p x) :
    (HexPolyMathlib.toPolynomial (monic (DensePoly.gcd f g))).rootMultiplicity z =
      min ((HexPolyMathlib.toPolynomial f).rootMultiplicity z)
        ((HexPolyMathlib.toPolynomial g).rootMultiplicity z) := by
  let raw := HexPolyMathlib.toPolynomial (DensePoly.gcd f g)
  let normalized := EuclideanDomain.gcd
    (HexPolyMathlib.toPolynomial f) (HexPolyMathlib.toPolynomial g)
  have hassociated : Associated raw normalized := by
    exact HexPolyMathlib.toPolynomial_gcd_associated f g
  have hnormalized : normalized ≠ 0 := by
    intro hzero
    exact hf (EuclideanDomain.gcd_eq_zero_iff.mp hzero).1
  have hraw : raw ≠ 0 := fun hzero =>
    hnormalized (hassociated.eq_zero_iff.mp hzero)
  calc
    (HexPolyMathlib.toPolynomial
        (monic (DensePoly.gcd f g))).rootMultiplicity z =
        raw.rootMultiplicity z :=
      rootMultiplicity_monic (DensePoly.gcd f g) hraw z
    _ = normalized.rootMultiplicity z :=
      rootMultiplicity_associated hassociated z
    _ = min ((HexPolyMathlib.toPolynomial f).rootMultiplicity z)
        ((HexPolyMathlib.toPolynomial g).rootMultiplicity z) :=
      rootMultiplicity_gcd _ _ hf hg z

/-- The executable monic gcd divides each nonzero input. -/
theorem monicGcd_dvd [ZPoly.CheckedIrreducible p]
    (f g : DensePoly (PolyQuot p x))
    (hf : HexPolyMathlib.toPolynomial f ≠ 0) :
    monic (DensePoly.gcd f g) ∣ f ∧ monic (DensePoly.gcd f g) ∣ g := by
  let raw := HexPolyMathlib.toPolynomial (DensePoly.gcd f g)
  let normalized := EuclideanDomain.gcd
    (HexPolyMathlib.toPolynomial f) (HexPolyMathlib.toPolynomial g)
  have hrawNormalized : Associated raw normalized :=
    HexPolyMathlib.toPolynomial_gcd_associated f g
  have hnormalized : normalized ≠ 0 := by
    intro hzero
    exact hf (EuclideanDomain.gcd_eq_zero_iff.mp hzero).1
  have hraw : raw ≠ 0 := fun hzero =>
    hnormalized (hrawNormalized.eq_zero_iff.mp hzero)
  have hmonicRaw : Associated
      (HexPolyMathlib.toPolynomial (monic (DensePoly.gcd f g))) raw :=
    toPolynomial_monic_associated (DensePoly.gcd f g) hraw
  have hmonicNormalized := hmonicRaw.trans hrawNormalized
  constructor <;> rw [← HexPolyMathlib.toPolynomial_dvd_iff]
  · exact hmonicNormalized.dvd.trans
      (EuclideanDomain.gcd_dvd_left
        (HexPolyMathlib.toPolynomial f) (HexPolyMathlib.toPolynomial g))
  · exact hmonicNormalized.dvd.trans
      (EuclideanDomain.gcd_dvd_right
        (HexPolyMathlib.toPolynomial f) (HexPolyMathlib.toPolynomial g))

/-- An exact quotient of a nonzero executable polynomial is nonzero. -/
theorem toPolynomial_div_ne_zero {K : Type*} [Field K] [DecidableEq K]
    (dividend divisor : DensePoly K) (hdivisor : divisor ∣ dividend)
    (hdividend : HexPolyMathlib.toPolynomial dividend ≠ 0) :
    HexPolyMathlib.toPolynomial (dividend / divisor) ≠ 0 := by
  have hmod : dividend % divisor = 0 :=
    DensePoly.mod_eq_zero_of_dvd dividend divisor hdivisor
  have hreconstruct := DensePoly.div_mul_add_mod dividend divisor
  rw [hmod] at hreconstruct
  have hpolynomial := congrArg HexPolyMathlib.toPolynomial hreconstruct
  simp only [HexPolyMathlib.toPolynomial_add,
    HexPolyMathlib.toPolynomial_mul, HexPolyMathlib.toPolynomial_zero,
    add_zero] at hpolynomial
  intro hquotient
  rw [hquotient, zero_mul] at hpolynomial
  exact hdividend hpolynomial.symm

/-- Monic normalization of a nonzero executable polynomial remains nonzero. -/
theorem toPolynomial_monic_ne_zero [ZPoly.CheckedIrreducible p]
    (f : DensePoly (PolyQuot p x))
    (hf : HexPolyMathlib.toPolynomial f ≠ 0) :
    HexPolyMathlib.toPolynomial (monic f) ≠ 0 := by
  intro hzero
  exact hf ((toPolynomial_monic_associated f hf).eq_zero_iff.mp hzero)

/-- A monic exact quotient subtracts the divisor's root multiplicity. -/
theorem rootMultiplicity_monicDiv [ZPoly.CheckedIrreducible p]
    (dividend divisor : DensePoly (PolyQuot p x))
    (hdivisor : divisor ∣ dividend)
    (hdividend : HexPolyMathlib.toPolynomial dividend ≠ 0)
    (z : PolyQuot p x) :
    (HexPolyMathlib.toPolynomial (monic (dividend / divisor))).rootMultiplicity z =
      (HexPolyMathlib.toPolynomial dividend).rootMultiplicity z -
        (HexPolyMathlib.toPolynomial divisor).rootMultiplicity z := by
  have hquotient := toPolynomial_div_ne_zero dividend divisor hdivisor hdividend
  rw [rootMultiplicity_monic (dividend / divisor) hquotient z]
  exact rootMultiplicity_div dividend divisor hdivisor hdividend z

/-- Monic normalization remains associated after any field embedding. -/
theorem map_monic_associated [ZPoly.CheckedIrreducible p]
    {K : Type*} [Field K] (embedding : PolyQuot p x →+* K)
    (f : DensePoly (PolyQuot p x)) (hf : toPolynomialMap embedding f ≠ 0) :
    Associated (toPolynomialMap embedding (monic f))
      (toPolynomialMap embedding f) := by
  have hfSource : HexPolyMathlib.toPolynomial f ≠ 0 := by
    intro hzero
    exact hf (by simp [toPolynomialMap, hzero])
  exact Polynomial.associated_map_map embedding
    (toPolynomial_monic_associated f hfSource)

/-- Monic normalization preserves root multiplicity after any field
embedding. -/
theorem rootMultiplicity_map_monic [ZPoly.CheckedIrreducible p]
    {K : Type*} [Field K] [DecidableEq K]
    (embedding : PolyQuot p x →+* K) (f : DensePoly (PolyQuot p x))
    (hf : toPolynomialMap embedding f ≠ 0) (z : K) :
    (toPolynomialMap embedding (monic f)).rootMultiplicity z =
      (toPolynomialMap embedding f).rootMultiplicity z :=
  rootMultiplicity_associated (map_monic_associated embedding f hf) z

/-- The executable monic gcd realizes the pointwise minimum of root
multiplicities after any field embedding. -/
theorem rootMultiplicity_map_monicGcd [ZPoly.CheckedIrreducible p]
    {K : Type*} [Field K] [DecidableEq K]
    (embedding : PolyQuot p x →+* K) (f g : DensePoly (PolyQuot p x))
    (hf : toPolynomialMap embedding f ≠ 0)
    (hg : toPolynomialMap embedding g ≠ 0) (z : K) :
    (toPolynomialMap embedding (monic (DensePoly.gcd f g))).rootMultiplicity z =
      min ((toPolynomialMap embedding f).rootMultiplicity z)
        ((toPolynomialMap embedding g).rootMultiplicity z) := by
  let sourceGcd := EuclideanDomain.gcd
    (HexPolyMathlib.toPolynomial f) (HexPolyMathlib.toPolynomial g)
  let targetGcd := EuclideanDomain.gcd
    (toPolynomialMap embedding f) (toPolynomialMap embedding g)
  have hfSource : HexPolyMathlib.toPolynomial f ≠ 0 := by
    intro hzero
    exact hf (by simp [toPolynomialMap, hzero])
  have hsourceGcd : sourceGcd ≠ 0 := by
    intro hzero
    exact hfSource (EuclideanDomain.gcd_eq_zero_iff.mp hzero).1
  have hrawSource : Associated
      (HexPolyMathlib.toPolynomial (DensePoly.gcd f g)) sourceGcd :=
    HexPolyMathlib.toPolynomial_gcd_associated f g
  have hraw : HexPolyMathlib.toPolynomial (DensePoly.gcd f g) ≠ 0 :=
    fun hzero => hsourceGcd (hrawSource.eq_zero_iff.mp hzero)
  have hmonicSource : Associated
      (HexPolyMathlib.toPolynomial (monic (DensePoly.gcd f g))) sourceGcd :=
    (toPolynomial_monic_associated (DensePoly.gcd f g) hraw).trans hrawSource
  have hmapped : Associated
      (toPolynomialMap embedding (monic (DensePoly.gcd f g)))
      (sourceGcd.map embedding) := by
    exact Polynomial.associated_map_map embedding hmonicSource
  have hmapGcd : sourceGcd.map embedding = targetGcd := by
    exact (Polynomial.gcd_map (p := HexPolyMathlib.toPolynomial f)
      (q := HexPolyMathlib.toPolynomial g) embedding).symm
  calc
    (toPolynomialMap embedding
        (monic (DensePoly.gcd f g))).rootMultiplicity z =
        (sourceGcd.map embedding).rootMultiplicity z :=
      rootMultiplicity_associated hmapped z
    _ = targetGcd.rootMultiplicity z := by rw [hmapGcd]
    _ = min ((toPolynomialMap embedding f).rootMultiplicity z)
        ((toPolynomialMap embedding g).rootMultiplicity z) :=
      rootMultiplicity_gcd _ _ hf hg z

/-- The monic gcd of two polynomials that remain nonzero after a field
embedding also remains nonzero. -/
theorem map_monicGcd_ne_zero [ZPoly.CheckedIrreducible p]
    {K : Type*} [Field K] (embedding : PolyQuot p x →+* K)
    (f g : DensePoly (PolyQuot p x))
    (hf : toPolynomialMap embedding f ≠ 0) :
    toPolynomialMap embedding (monic (DensePoly.gcd f g)) ≠ 0 := by
  have hfSource : HexPolyMathlib.toPolynomial f ≠ 0 := by
    intro hzero
    exact hf (by simp [toPolynomialMap, hzero])
  let sourceGcd := EuclideanDomain.gcd
    (HexPolyMathlib.toPolynomial f) (HexPolyMathlib.toPolynomial g)
  have hsourceGcd : sourceGcd ≠ 0 := by
    intro hzero
    exact hfSource (EuclideanDomain.gcd_eq_zero_iff.mp hzero).1
  have hrawSource : Associated
      (HexPolyMathlib.toPolynomial (DensePoly.gcd f g)) sourceGcd :=
    HexPolyMathlib.toPolynomial_gcd_associated f g
  have hraw : HexPolyMathlib.toPolynomial (DensePoly.gcd f g) ≠ 0 :=
    fun hzero => hsourceGcd (hrawSource.eq_zero_iff.mp hzero)
  have hmonic := toPolynomial_monic_ne_zero (DensePoly.gcd f g) hraw
  simpa only [toPolynomialMap] using
    (Polynomial.map_ne_zero_iff embedding.injective).mpr hmonic

/-- The executable derivative commutes with every field embedding. -/
theorem map_derivative [ZPoly.CheckedIrreducible p]
    {K : Type*} [Field K] (embedding : PolyQuot p x →+* K)
    (f : DensePoly (PolyQuot p x)) :
    toPolynomialMap embedding (derivative f) =
      Polynomial.derivative (toPolynomialMap embedding f) := by
  simp only [toPolynomialMap, toPolynomial_derivative,
    Polynomial.derivative_map]

/-- Exact executable division remains an exact factorization after a field
embedding. -/
theorem map_div_mul [ZPoly.CheckedIrreducible p]
    {K : Type*} [Field K] (embedding : PolyQuot p x →+* K)
    (dividend divisor : DensePoly (PolyQuot p x))
    (hdivisor : divisor ∣ dividend) :
    toPolynomialMap embedding (dividend / divisor) *
        toPolynomialMap embedding divisor =
      toPolynomialMap embedding dividend := by
  have hmod : dividend % divisor = 0 :=
    DensePoly.mod_eq_zero_of_dvd dividend divisor hdivisor
  have hreconstruct := DensePoly.div_mul_add_mod dividend divisor
  rw [hmod] at hreconstruct
  have hsource := congrArg HexPolyMathlib.toPolynomial hreconstruct
  simp only [HexPolyMathlib.toPolynomial_add,
    HexPolyMathlib.toPolynomial_mul, HexPolyMathlib.toPolynomial_zero,
    add_zero] at hsource
  have hmapped := congrArg (Polynomial.map embedding) hsource
  simpa only [toPolynomialMap, Polynomial.map_mul] using hmapped

/-- An exact quotient of a polynomial that stays nonzero after embedding also
stays nonzero. -/
theorem map_div_ne_zero [ZPoly.CheckedIrreducible p]
    {K : Type*} [Field K] (embedding : PolyQuot p x →+* K)
    (dividend divisor : DensePoly (PolyQuot p x))
    (hdivisor : divisor ∣ dividend)
    (hdividend : toPolynomialMap embedding dividend ≠ 0) :
    toPolynomialMap embedding (dividend / divisor) ≠ 0 := by
  intro hquotient
  have hreconstruct := map_div_mul embedding dividend divisor hdivisor
  rw [hquotient, zero_mul] at hreconstruct
  exact hdividend hreconstruct.symm

/-- Exact executable division subtracts root multiplicities after a field
embedding. -/
theorem rootMultiplicity_map_div [ZPoly.CheckedIrreducible p]
    {K : Type*} [Field K] (embedding : PolyQuot p x →+* K)
    (dividend divisor : DensePoly (PolyQuot p x))
    (hdivisor : divisor ∣ dividend)
    (hdividend : toPolynomialMap embedding dividend ≠ 0) (z : K) :
    (toPolynomialMap embedding (dividend / divisor)).rootMultiplicity z =
      (toPolynomialMap embedding dividend).rootMultiplicity z -
        (toPolynomialMap embedding divisor).rootMultiplicity z :=
  rootMultiplicity_of_mul_eq _ _ _ hdividend
    (map_div_mul embedding dividend divisor hdivisor) z

/-- A monic exact quotient subtracts root multiplicities after a field
embedding. -/
theorem rootMultiplicity_map_monicDiv [ZPoly.CheckedIrreducible p]
    {K : Type*} [Field K] [DecidableEq K]
    (embedding : PolyQuot p x →+* K)
    (dividend divisor : DensePoly (PolyQuot p x))
    (hdivisor : divisor ∣ dividend)
    (hdividend : toPolynomialMap embedding dividend ≠ 0) (z : K) :
    (toPolynomialMap embedding (monic (dividend / divisor))).rootMultiplicity z =
      (toPolynomialMap embedding dividend).rootMultiplicity z -
        (toPolynomialMap embedding divisor).rootMultiplicity z := by
  have hquotient := map_div_ne_zero embedding dividend divisor hdivisor hdividend
  rw [rootMultiplicity_map_monic embedding (dividend / divisor) hquotient z]
  exact rootMultiplicity_map_div embedding dividend divisor hdivisor hdividend z

/-- A monic exact quotient remains nonzero after a field embedding. -/
theorem map_monicDiv_ne_zero [ZPoly.CheckedIrreducible p]
    {K : Type*} [Field K] (embedding : PolyQuot p x →+* K)
    (dividend divisor : DensePoly (PolyQuot p x))
    (hdivisor : divisor ∣ dividend)
    (hdividend : toPolynomialMap embedding dividend ≠ 0) :
    toPolynomialMap embedding (monic (dividend / divisor)) ≠ 0 := by
  have hquotient := map_div_ne_zero embedding dividend divisor hdivisor hdividend
  intro hzero
  exact hquotient ((map_monic_associated embedding
    (dividend / divisor) hquotient).eq_zero_iff.mp hzero)

/-- Pointwise semantic invariant of the Yun loop at multiplicity index `k`.
The first polynomial contains the root once exactly while `k ≤ r`; the
repeated part contains the remaining `r - k` copies. -/
structure YunInvariant [ZPoly.CheckedIrreducible p]
    {K : Type*} [Field K] (embedding : PolyQuot p x →+* K) (z : K)
    (r k : Nat) (w repeated : DensePoly (PolyQuot p x)) : Prop where
  /-- The current squarefree-product accumulator is nonzero. -/
  w_ne : toPolynomialMap embedding w ≠ 0
  /-- The current repeated part is nonzero. -/
  repeated_ne : toPolynomialMap embedding repeated ≠ 0
  /-- The accumulator contains `z` exactly once while copies remain. -/
  w_multiplicity : (toPolynomialMap embedding w).rootMultiplicity z =
    if k ≤ r then 1 else 0
  /-- The repeated part contains the remaining `r - k` copies of `z`. -/
  repeated_multiplicity :
    (toPolynomialMap embedding repeated).rootMultiplicity z = r - k

/-- One executable Yun step advances the pointwise loop invariant. -/
theorem YunInvariant.step [ZPoly.CheckedIrreducible p]
    {K : Type*} [Field K] [DecidableEq K]
    (embedding : PolyQuot p x →+* K) (z : K) (r k : Nat)
    (w repeated : DensePoly (PolyQuot p x))
    (invariant : YunInvariant embedding z r k w repeated) :
    let shared := monic (DensePoly.gcd w repeated)
    let nextRepeated := monic (repeated / shared)
    YunInvariant embedding z r (k + 1) shared nextRepeated := by
  let shared := monic (DensePoly.gcd w repeated)
  let nextRepeated := monic (repeated / shared)
  have hwSource : HexPolyMathlib.toPolynomial w ≠ 0 := by
    intro hzero
    exact invariant.w_ne (by simp [toPolynomialMap, hzero])
  have hdivisors := monicGcd_dvd w repeated hwSource
  have hsharedNe : toPolynomialMap embedding shared ≠ 0 :=
    map_monicGcd_ne_zero embedding w repeated invariant.w_ne
  have hnextNe : toPolynomialMap embedding nextRepeated ≠ 0 :=
    map_monicDiv_ne_zero embedding repeated shared hdivisors.2 invariant.repeated_ne
  have hsharedMultiplicity :
      (toPolynomialMap embedding shared).rootMultiplicity z =
        min ((toPolynomialMap embedding w).rootMultiplicity z)
          ((toPolynomialMap embedding repeated).rootMultiplicity z) :=
    rootMultiplicity_map_monicGcd embedding w repeated
      invariant.w_ne invariant.repeated_ne z
  have hnextMultiplicity :
      (toPolynomialMap embedding nextRepeated).rootMultiplicity z =
        (toPolynomialMap embedding repeated).rootMultiplicity z -
          (toPolynomialMap embedding shared).rootMultiplicity z :=
    rootMultiplicity_map_monicDiv embedding repeated shared
      hdivisors.2 invariant.repeated_ne z
  refine ⟨hsharedNe, hnextNe, ?_, ?_⟩
  · rw [hsharedMultiplicity, invariant.w_multiplicity,
      invariant.repeated_multiplicity]
    by_cases hk : k ≤ r <;> by_cases hnext : k + 1 ≤ r <;>
      simp [hk, hnext] <;> omega
  · rw [hnextMultiplicity, invariant.repeated_multiplicity,
      hsharedMultiplicity, invariant.w_multiplicity,
      invariant.repeated_multiplicity]
    by_cases hk : k ≤ r <;> simp [hk] <;> omega

/-- The component produced at a Yun step contains the root exactly when the
current index is its original multiplicity. -/
theorem YunInvariant.component [ZPoly.CheckedIrreducible p]
    {K : Type*} [Field K] [DecidableEq K]
    (embedding : PolyQuot p x →+* K) (z : K) (r k : Nat)
    (w repeated : DensePoly (PolyQuot p x))
    (invariant : YunInvariant embedding z r k w repeated) :
    let shared := monic (DensePoly.gcd w repeated)
    let component := monic (w / shared)
    (toPolynomialMap embedding component).rootMultiplicity z =
      if k = r then 1 else 0 := by
  let shared := monic (DensePoly.gcd w repeated)
  let component := monic (w / shared)
  change (toPolynomialMap embedding component).rootMultiplicity z =
    if k = r then 1 else 0
  have hwSource : HexPolyMathlib.toPolynomial w ≠ 0 := by
    intro hzero
    exact invariant.w_ne (by simp [toPolynomialMap, hzero])
  have hdivisors := monicGcd_dvd w repeated hwSource
  rw [rootMultiplicity_map_monicDiv embedding w shared
      hdivisors.1 invariant.w_ne z,
    rootMultiplicity_map_monicGcd embedding w repeated
      invariant.w_ne invariant.repeated_ne z,
    invariant.w_multiplicity, invariant.repeated_multiplicity]
  by_cases hk : k ≤ r
  · by_cases heq : k = r
    · simp [heq]
    · simp [hk, heq]
      omega
  · have heq : k ≠ r := by omega
    simp [hk, heq]

/-- The normalized derivative/gcd prelude establishes the Yun invariant at
multiplicity index one. -/
theorem YunInvariant.init [ZPoly.CheckedIrreducible p]
    {K : Type*} [Field K] [CharZero K] [DecidableEq K]
    (embedding : PolyQuot p x →+* K) (f : DensePoly (PolyQuot p x))
    (hf : toPolynomialMap embedding f ≠ 0)
    (hdegree : (toPolynomialMap embedding f).natDegree ≠ 0) (z : K) :
    let normalized := monic f
    let repeated := monic (DensePoly.gcd normalized (derivative normalized))
    let distinct := monic (normalized / repeated)
    YunInvariant embedding z
      ((toPolynomialMap embedding f).rootMultiplicity z) 1
      distinct repeated := by
  let normalized := monic f
  let repeated := monic (DensePoly.gcd normalized (derivative normalized))
  let distinct := monic (normalized / repeated)
  change YunInvariant embedding z
    ((toPolynomialMap embedding f).rootMultiplicity z) 1 distinct repeated
  have hnormalizedNe : toPolynomialMap embedding normalized ≠ 0 := by
    intro hzero
    exact hf ((map_monic_associated embedding f hf).eq_zero_iff.mp hzero)
  have hnormalizedMultiplicity :
      (toPolynomialMap embedding normalized).rootMultiplicity z =
        (toPolynomialMap embedding f).rootMultiplicity z :=
    rootMultiplicity_map_monic embedding f hf z
  have hnormalizedDegree :
      (toPolynomialMap embedding normalized).natDegree ≠ 0 := by
    have hdegreeEq := Polynomial.degree_eq_degree_of_associated
      (map_monic_associated embedding f hf)
    have hnatDegreeEq := Polynomial.natDegree_eq_of_degree_eq hdegreeEq
    intro hzero
    apply hdegree
    rw [← hnatDegreeEq, hzero]
  have hderivativeNe :
      toPolynomialMap embedding (derivative normalized) ≠ 0 := by
    rw [map_derivative]
    exact Polynomial.derivative_ne_zero.mpr hnormalizedDegree
  have hrepeatedNe : toPolynomialMap embedding repeated ≠ 0 :=
    map_monicGcd_ne_zero embedding normalized (derivative normalized)
      hnormalizedNe
  have hnormalizedSource : HexPolyMathlib.toPolynomial normalized ≠ 0 := by
    intro hzero
    exact hnormalizedNe (by simp [toPolynomialMap, hzero])
  have hdivisor : repeated ∣ normalized :=
    (monicGcd_dvd normalized (derivative normalized) hnormalizedSource).1
  have hdistinctNe : toPolynomialMap embedding distinct ≠ 0 :=
    map_monicDiv_ne_zero embedding normalized repeated hdivisor hnormalizedNe
  have hrepeatedMultiplicity :
      (toPolynomialMap embedding repeated).rootMultiplicity z =
        (toPolynomialMap embedding f).rootMultiplicity z - 1 := by
    rw [rootMultiplicity_map_monicGcd embedding normalized
        (derivative normalized) hnormalizedNe hderivativeNe z,
      map_derivative, hnormalizedMultiplicity]
    by_cases hroot :
        (toPolynomialMap embedding f).rootMultiplicity z = 0
    · simp [hroot]
    · have hpositive : 0 <
          (toPolynomialMap embedding normalized).rootMultiplicity z := by
        omega
      have hisRoot : (toPolynomialMap embedding normalized).IsRoot z :=
        (Polynomial.rootMultiplicity_pos hnormalizedNe).mp hpositive
      rw [Polynomial.derivative_rootMultiplicity_of_root hisRoot,
        hnormalizedMultiplicity]
      omega
  refine ⟨hdistinctNe, hrepeatedNe, ?_, hrepeatedMultiplicity⟩
  rw [rootMultiplicity_map_monicDiv embedding normalized repeated
      hdivisor hnormalizedNe z,
    hnormalizedMultiplicity, hrepeatedMultiplicity]
  by_cases hpositive : 1 ≤
      (toPolynomialMap embedding f).rootMultiplicity z <;>
    simp [hpositive] <;> omega

/-- A nonzero embedded polynomial with a root has positive executable degree. -/
theorem degree_pos_of_map_root [ZPoly.CheckedIrreducible p]
    {K : Type*} [Field K] (embedding : PolyQuot p x →+* K)
    (f : DensePoly (PolyQuot p x)) (hf : toPolynomialMap embedding f ≠ 0)
    {z : K} (hroot : (toPolynomialMap embedding f).IsRoot z) :
    0 < f.degree?.getD 0 := by
  have hdegree := Polynomial.degree_pos_of_root hf hroot
  have hnatDegree : 0 < (toPolynomialMap embedding f).natDegree :=
    Polynomial.natDegree_pos_iff_degree_pos.mpr hdegree
  rw [toPolynomialMap,
    Polynomial.natDegree_map_eq_of_injective embedding.injective,
    HexPolyMathlib.natDegree_toPolynomial] at hnatDegree
  exact hnatDegree

private theorem mem_yunAux_of_mem [ZPoly.CheckedIrreducible p]
    (w repeated : DensePoly (PolyQuot p x)) (k fuel : Nat)
    (out : Array (DensePoly (PolyQuot p x) × Nat)) {entry}
    (hentry : entry ∈ out.toList) :
    entry ∈ (yunAux w repeated k fuel out).toList := by
  induction fuel generalizing w repeated k out with
  | zero => simpa [yunAux] using hentry
  | succ fuel ih =>
      rw [yunAux]
      split
      · exact hentry
      · dsimp only
        split
        · apply ih
          rw [Array.toList_push, List.mem_append]
          exact Or.inl hentry
        · exact ih _ _ _ _ hentry

private theorem yunAux_sound [ZPoly.CheckedIrreducible p]
    {K : Type*} [Field K] [DecidableEq K]
    (embedding : PolyQuot p x →+* K) (z : K) (r : Nat)
    (w repeated : DensePoly (PolyQuot p x)) (k fuel : Nat)
    (out : Array (DensePoly (PolyQuot p x) × Nat))
    (invariant : YunInvariant embedding z r k w repeated)
    (hOut : ∀ entry ∈ out.toList,
      (toPolynomialMap embedding entry.1).IsRoot z → entry.2 = r) :
    ∀ entry ∈ (yunAux w repeated k fuel out).toList,
      (toPolynomialMap embedding entry.1).IsRoot z → entry.2 = r := by
  induction fuel generalizing w repeated k out with
  | zero => simpa [yunAux] using hOut
  | succ fuel ih =>
      rw [yunAux]
      split
      · exact hOut
      · dsimp only
        let shared := monic (DensePoly.gcd w repeated)
        let component := monic (w / shared)
        let nextRepeated := monic (repeated / shared)
        have hwSource : HexPolyMathlib.toPolynomial w ≠ 0 := by
          intro hzero
          exact invariant.w_ne (by simp [toPolynomialMap, hzero])
        have hdivisors := monicGcd_dvd w repeated hwSource
        have hcomponentNe : toPolynomialMap embedding component ≠ 0 :=
          map_monicDiv_ne_zero embedding w shared hdivisors.1 invariant.w_ne
        have hcomponentMultiplicity :
            (toPolynomialMap embedding component).rootMultiplicity z =
              if k = r then 1 else 0 :=
          invariant.component embedding z r k w repeated
        have hcomponentSound :
            (toPolynomialMap embedding component).IsRoot z → k = r := by
          intro hroot
          have hpositive :=
            (Polynomial.rootMultiplicity_pos hcomponentNe).mpr hroot
          rw [hcomponentMultiplicity] at hpositive
          by_cases heq : k = r
          · exact heq
          · simp [heq] at hpositive
        have hnextInvariant : YunInvariant embedding z r (k + 1)
            shared nextRepeated :=
          invariant.step embedding z r k w repeated
        split
        · apply ih shared nextRepeated (k + 1) _ hnextInvariant
          intro entry hentry
          rw [Array.toList_push, List.mem_append,
            List.mem_singleton] at hentry
          rcases hentry with hentry | rfl
          · exact hOut entry hentry
          · intro hroot
            exact hcomponentSound hroot
        · exact ih shared nextRepeated (k + 1) _ hnextInvariant hOut

private theorem yunAux_complete [ZPoly.CheckedIrreducible p]
    {K : Type*} [Field K] [DecidableEq K]
    (embedding : PolyQuot p x →+* K) (z : K) (r : Nat)
    (w repeated : DensePoly (PolyQuot p x)) (k fuel : Nat)
    (out : Array (DensePoly (PolyQuot p x) × Nat))
    (invariant : YunInvariant embedding z r k w repeated)
    (hindex : k ≤ r) (hfuel : r < k + fuel) :
    ∃ entry ∈ (yunAux w repeated k fuel out).toList,
      (toPolynomialMap embedding entry.1).IsRoot z ∧ entry.2 = r := by
  induction fuel generalizing w repeated k out with
  | zero => omega
  | succ fuel ih =>
      have hnotOne : w ≠ 1 := by
        intro hone
        have hmultiplicity := invariant.w_multiplicity
        rw [hone] at hmultiplicity
        have honeMultiplicity :
            Polynomial.rootMultiplicity z (1 : Polynomial K) = 0 := by
          simpa only [Polynomial.C_1] using
            Polynomial.rootMultiplicity_C (1 : K) z
        simp only [toPolynomialMap, HexPolyMathlib.toPolynomial_one,
          Polynomial.map_one, ite_eq_left hindex] at hmultiplicity
        omega
      rw [yunAux, ite_eq_right hnotOne]
      dsimp only
      let shared := monic (DensePoly.gcd w repeated)
      let component := monic (w / shared)
      let nextRepeated := monic (repeated / shared)
      have hwSource : HexPolyMathlib.toPolynomial w ≠ 0 := by
        intro hzero
        exact invariant.w_ne (by simp [toPolynomialMap, hzero])
      have hdivisors := monicGcd_dvd w repeated hwSource
      have hcomponentNe : toPolynomialMap embedding component ≠ 0 :=
        map_monicDiv_ne_zero embedding w shared hdivisors.1 invariant.w_ne
      have hcomponentMultiplicity :
          (toPolynomialMap embedding component).rootMultiplicity z =
            if k = r then 1 else 0 :=
        invariant.component embedding z r k w repeated
      by_cases heq : k = r
      · have hpositive : 0 <
            (toPolynomialMap embedding component).rootMultiplicity z := by
          rw [hcomponentMultiplicity]
          simp [heq]
        have hroot : (toPolynomialMap embedding component).IsRoot z :=
          (Polynomial.rootMultiplicity_pos hcomponentNe).mp hpositive
        have hdegree : 0 < component.degree?.getD 0 :=
          degree_pos_of_map_root embedding component hcomponentNe hroot
        rw [ite_eq_left hdegree]
        refine ⟨(component, k), ?_, hroot, heq⟩
        apply mem_yunAux_of_mem
        simp [component, shared]
      · have hnextInvariant : YunInvariant embedding z r (k + 1)
            shared nextRepeated :=
          invariant.step embedding z r k w repeated
        have hnextIndex : k + 1 ≤ r := by omega
        have hnextFuel : r < k + 1 + fuel := by omega
        split
        · exact ih shared nextRepeated (k + 1) _ hnextInvariant
            hnextIndex hnextFuel
        · exact ih shared nextRepeated (k + 1) _ hnextInvariant
            hnextIndex hnextFuel

/-- Every root of an emitted Yun component is a root of the input with the
component's stored multiplicity. -/
theorem yun_sound [ZPoly.CheckedIrreducible p]
    {K : Type*} [Field K] [CharZero K] [DecidableEq K]
    (embedding : PolyQuot p x →+* K) (f : DensePoly (PolyQuot p x))
    (hf : toPolynomialMap embedding f ≠ 0)
    (hdegree : 0 < f.degree?.getD 0) (z : K) (entry)
    (hentry : entry ∈ (yun f).toList)
    (hroot : (toPolynomialMap embedding entry.1).IsRoot z) :
    entry.2 = (toPolynomialMap embedding f).rootMultiplicity z := by
  have hnatDegree : (toPolynomialMap embedding f).natDegree ≠ 0 := by
    rw [toPolynomialMap,
      Polynomial.natDegree_map_eq_of_injective embedding.injective,
      HexPolyMathlib.natDegree_toPolynomial]
    omega
  let normalized := monic f
  let repeated := monic (DensePoly.gcd normalized (derivative normalized))
  let distinct := monic (normalized / repeated)
  have invariant : YunInvariant embedding z
      ((toPolynomialMap embedding f).rootMultiplicity z) 1
      distinct repeated :=
    YunInvariant.init embedding f hf hnatDegree z
  unfold yun at hentry
  rw [ite_eq_right (by omega)] at hentry
  exact yunAux_sound embedding z
    ((toPolynomialMap embedding f).rootMultiplicity z)
    distinct repeated 1 (f.size + 1) #[] invariant (by simp)
    entry hentry hroot

/-- Every root of a positive-degree input occurs in an emitted Yun component
at its exact multiplicity. -/
theorem yun_complete [ZPoly.CheckedIrreducible p]
    {K : Type*} [Field K] [CharZero K] [DecidableEq K]
    (embedding : PolyQuot p x →+* K) (f : DensePoly (PolyQuot p x))
    (hf : toPolynomialMap embedding f ≠ 0)
    (hdegree : 0 < f.degree?.getD 0) (z : K)
    (hroot : (toPolynomialMap embedding f).IsRoot z) :
    ∃ entry ∈ (yun f).toList,
      (toPolynomialMap embedding entry.1).IsRoot z ∧
        entry.2 = (toPolynomialMap embedding f).rootMultiplicity z := by
  have hnatDegree : (toPolynomialMap embedding f).natDegree ≠ 0 := by
    rw [toPolynomialMap,
      Polynomial.natDegree_map_eq_of_injective embedding.injective,
      HexPolyMathlib.natDegree_toPolynomial]
    omega
  let r := (toPolynomialMap embedding f).rootMultiplicity z
  have hindex : 1 ≤ r := by
    exact (Polynomial.rootMultiplicity_pos hf).mpr hroot
  have hmultiplicityDegree : r ≤ (toPolynomialMap embedding f).natDegree :=
    rootMultiplicity_le_natDegree _ hf z
  have hsize : 0 < f.size := by
    by_contra hzero
    have hsizeZero : f.size = 0 := by omega
    simp [DensePoly.degree?, hsizeZero] at hdegree
  have hdenseDegree : f.degree?.getD 0 = f.size - 1 := by
    rw [DensePoly.degree?_eq_some_of_pos_size f hsize]
    rfl
  have hdegreeEq : (toPolynomialMap embedding f).natDegree =
      f.degree?.getD 0 := by
    simp only [toPolynomialMap,
      Polynomial.natDegree_map_eq_of_injective embedding.injective,
      HexPolyMathlib.natDegree_toPolynomial]
  have hfuel : r < 1 + (f.size + 1) := by omega
  let normalized := monic f
  let repeated := monic (DensePoly.gcd normalized (derivative normalized))
  let distinct := monic (normalized / repeated)
  have invariant : YunInvariant embedding z r 1 distinct repeated :=
    YunInvariant.init embedding f hf hnatDegree z
  have hcomplete := yunAux_complete embedding z r distinct repeated 1
    (f.size + 1) #[] invariant hindex hfuel
  unfold yun
  rw [ite_eq_right (by omega)]
  exact hcomplete

end Hex.PolyQuot.Roots
