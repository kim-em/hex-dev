/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexRealClosureMathlib.Yun
public import Mathlib.Algebra.Polynomial.FieldDivision
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import HexNumberFieldMathlib.Yun

public section

/-!
# Correctness of Yun decomposition

The invariant relates the executable polynomials to original root
multiplicities. Exact quotient and derivative identities establish it at
counter one and preserve it through the actual recurrence. The emitted gcd
selects precisely the roots with the current multiplicity.

Root multiplicities determine the powered product over an algebraic closure.
Coefficient maps reflect reconstruction, degree accounting, squarefreeness and
coprimality back to every characteristic-zero field. The public ordered-field
producer therefore passes the full executable replay checker for every input.
-/

namespace Hex.RealClosure.Yun

attribute [local instance 2000] Field.toGrindField

private theorem polynomial_ne_zero {K : Type*} [Field K] [DecidableEq K]
    (f : DensePoly K) (hf : f ≠ 0) : HexPolyMathlib.toPolynomial f ≠ 0 := by
  intro h
  exact hf ((HexPolyMathlib.equiv (R := K)).injective
    (h.trans HexPolyMathlib.toPolynomial_zero.symm))

private theorem divide_mul {K : Type*} [Field K] [DecidableEq K]
    (p a : DensePoly K) (hp : a ∣ p) :
    HexPolyMathlib.toPolynomial (p / a) * HexPolyMathlib.toPolynomial a =
      HexPolyMathlib.toPolynomial p := by
  have h := DensePoly.div_mul_add_mod p a
  rw [DensePoly.mod_eq_zero_of_dvd p a hp] at h
  simpa only [HexPolyMathlib.toPolynomial_add, HexPolyMathlib.toPolynomial_mul,
    HexPolyMathlib.toPolynomial_zero, add_zero] using
    congrArg HexPolyMathlib.toPolynomial h

private theorem gcd_associated {K : Type*} [Field K] [DecidableEq K]
    (f g : DensePoly K) (hf : f ≠ 0) :
    Associated (HexPolyMathlib.toPolynomial (DensePoly.monicize (DensePoly.gcd f g)))
      (EuclideanDomain.gcd (HexPolyMathlib.toPolynomial f) (HexPolyMathlib.toPolynomial g)) := by
  have hg : DensePoly.gcd f g ≠ 0 := by
    intro h
    have hd := DensePoly.gcd_dvd_left f g
    rw [h] at hd
    obtain ⟨q, hq⟩ := hd
    exact hf (hq.trans (DensePoly.zero_mul q))
  apply Associated.trans _ (HexPolyMathlib.toPolynomial_gcd_associated f g)
  apply associated_of_dvd_dvd
  · exact HexPolyMathlib.toPolynomial_dvd_iff.mpr
      (DensePoly.monicize_dvd_of_dvd hg
        ⟨1, (DensePoly.mul_one_right_poly _).symm⟩)
  · exact HexPolyMathlib.toPolynomial_dvd_iff.mpr (DensePoly.dvd_monicize _)

private theorem gcd_divisors {K : Type*} [Field K] [DecidableEq K]
    (f g : DensePoly K) (hf : f ≠ 0) :
    DensePoly.monicize (DensePoly.gcd f g) ∣ f ∧
      DensePoly.monicize (DensePoly.gcd f g) ∣ g := by
  have h := gcd_associated f g hf
  exact ⟨HexPolyMathlib.toPolynomial_dvd_iff.mp
      (h.dvd.trans (EuclideanDomain.gcd_dvd_left _ _)),
    HexPolyMathlib.toPolynomial_dvd_iff.mp
      (h.dvd.trans (EuclideanDomain.gcd_dvd_right _ _))⟩

/-- Dividing a polynomial and its derivative by a common divisor which
removes all but one copy of a root retains the original multiplicity in the
derivative quotient's value at that root. -/
theorem eval_quotient {K : Type*} [Field K]
    (f a v w : Polynomial K) (x : K) (hf : f ≠ 0) (ha : a ≠ 0)
    (hroot : f.IsRoot x)
    (hm : a.rootMultiplicity x = f.rootMultiplicity x - 1)
    (hv : v * a = f) (hw : w * a = f.derivative) :
    w.eval x = (f.rootMultiplicity x : K) * v.derivative.eval x := by
  classical
  set r := f.rootMultiplicity x
  obtain ⟨q, hfq, _⟩ := f.exists_eq_pow_rootMultiplicity_mul_and_not_dvd hf x
  obtain ⟨b, hab, hbn⟩ := a.exists_eq_pow_rootMultiplicity_mul_and_not_dvd ha x
  rw [hm] at hab
  change f = (Polynomial.X - Polynomial.C x) ^ r * q at hfq
  change a = (Polynomial.X - Polynomial.C x) ^ (r - 1) * b at hab
  have hb : b.eval x ≠ 0 := by
    simpa only [Polynomial.dvd_iff_isRoot, Polynomial.IsRoot] using hbn
  have hr : 0 < r :=
    (Polynomial.rootMultiplicity_pos hf).mpr hroot
  have hrsub : r - 1 + 1 = r := by omega
  have hpowers : (Polynomial.X - Polynomial.C x) ^ r =
      (Polynomial.X - Polynomial.C x) ^ (r - 1) * (Polynomial.X - Polynomial.C x) := by
    simpa only [hrsub] using pow_succ (Polynomial.X - Polynomial.C x) (r - 1)
  have hpow : (Polynomial.X - Polynomial.C x) ^ (r - 1) ≠ 0 :=
    _root_.pow_ne_zero _ (Polynomial.X_sub_C_ne_zero x)
  have hvb : v * b = (Polynomial.X - Polynomial.C x) * q := by
    apply mul_left_cancel₀ hpow
    calc
      _ = v * a := by rw [hab]; ring
      _ = f := hv
      _ = (Polynomial.X - Polynomial.C x) ^ r * q := hfq
      _ = _ := by rw [hpowers]; ring
  have hwb : w * b = Polynomial.C (r : K) * q +
      (Polynomial.X - Polynomial.C x) * q.derivative := by
    apply mul_left_cancel₀ hpow
    calc
      _ = w * a := by rw [hab]; ring
      _ = f.derivative := hw
      _ = ((Polynomial.X - Polynomial.C x) ^ r * q).derivative :=
        congrArg Polynomial.derivative hfq
      _ = _ := by
        rw [Polynomial.derivative_mul, Polynomial.derivative_X_sub_C_pow, hpowers]
        ring
  have hvzero : v.eval x = 0 := by
    have h := congrArg (Polynomial.eval x) hvb
    simp only [Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_X,
      Polynomial.eval_C, sub_self, zero_mul] at h
    exact (mul_eq_zero.mp h).resolve_right hb
  have hvderiv : v.derivative.eval x * b.eval x = q.eval x := by
    have h := congrArg (fun p : Polynomial K => p.derivative.eval x) hvb
    simpa only [Polynomial.derivative_mul, Polynomial.eval_add,
      Polynomial.eval_mul, Polynomial.derivative_X_sub_C,
      Polynomial.eval_one, Polynomial.eval_sub, Polynomial.eval_X,
      Polynomial.eval_C, sub_self, hvzero, zero_mul, add_zero,
      zero_add, one_mul] using h
  apply mul_right_cancel₀ hb
  have h := congrArg (Polynomial.eval x) hwb
  simp only [Polynomial.eval_add, Polynomial.eval_mul,
    Polynomial.eval_C, Polynomial.eval_sub, Polynomial.eval_X,
    sub_self, zero_mul, add_zero] at h
  rw [h, mul_assoc, hvderiv]

/-- The initial executable derivative quotient carries each root's original
multiplicity. The gcd, normalization and exact divisions are the operations
used in `decomposeRaw`. -/
theorem eval_initial {K : Type*} [Field K] [CharZero K] [DecidableEq K]
    (f : DensePoly K) (x : K) (hf : f ≠ 0) (hdegree : 0 < f.natDegree)
    (hroot : (HexPolyMathlib.toPolynomial f).IsRoot x) :
    let a := DensePoly.monicize (DensePoly.gcd f (DensePoly.derivativeImpl f))
    (HexPolyMathlib.toPolynomial (DensePoly.derivativeImpl f / a)).eval x =
      ((HexPolyMathlib.toPolynomial f).rootMultiplicity x : K) *
        (HexPolyMathlib.toPolynomial (f / a)).derivative.eval x := by
  let a := DensePoly.monicize (DensePoly.gcd f (DensePoly.derivativeImpl f))
  have hfPoly : HexPolyMathlib.toPolynomial f ≠ 0 := by
    intro h
    exact hf ((HexPolyMathlib.equiv (R := K)).injective
      (h.trans HexPolyMathlib.toPolynomial_zero.symm))
  have hderiv : HexPolyMathlib.toPolynomial (DensePoly.derivativeImpl f) =
      (HexPolyMathlib.toPolynomial f).derivative := by
    rw [← DensePoly.derivative_eq_derivativeImpl,
      HexPolyMathlib.toPolynomial_derivative]
  have hdPoly : (HexPolyMathlib.toPolynomial f).derivative ≠ 0 := by
    apply Polynomial.derivative_ne_zero.mpr
    rw [HexPolyMathlib.natDegree_toPolynomial]
    omega
  have hassociated := gcd_associated f (DensePoly.derivativeImpl f) hf
  rw [hderiv] at hassociated
  have haPoly : HexPolyMathlib.toPolynomial a ≠ 0 := by
    intro h
    have hz := hassociated.eq_zero_iff.mp h
    exact hfPoly (EuclideanDomain.gcd_eq_zero_iff.mp hz).1
  have hm : (HexPolyMathlib.toPolynomial a).rootMultiplicity x =
      (HexPolyMathlib.toPolynomial f).rootMultiplicity x - 1 := by
    rw [Hex.PolyQuot.Roots.rootMultiplicity_associated hassociated x,
      Hex.PolyQuot.Roots.rootMultiplicity_gcd _ _ hfPoly hdPoly x,
      Polynomial.derivative_rootMultiplicity_of_root hroot]
    omega
  have ⟨haF, haD⟩ := gcd_divisors f (DensePoly.derivativeImpl f) hf
  exact eval_quotient _ _ _ _ x hfPoly haPoly hroot hm
    (divide_mul f a haF) ((divide_mul (DensePoly.derivativeImpl f) a haD).trans hderiv)

private theorem initial_multiplicity {K : Type*} [Field K] [CharZero K] [DecidableEq K]
    (f : DensePoly K) (x : K) (hf : f ≠ 0) (hdegree : 0 < f.natDegree) :
    let a := DensePoly.monicize (DensePoly.gcd f (DensePoly.derivativeImpl f))
    (HexPolyMathlib.toPolynomial (f / a)).rootMultiplicity x =
      if (HexPolyMathlib.toPolynomial f).IsRoot x then 1 else 0 := by
  let a := DensePoly.monicize (DensePoly.gcd f (DensePoly.derivativeImpl f))
  have hfPoly := polynomial_ne_zero f hf
  have hderiv : HexPolyMathlib.toPolynomial (DensePoly.derivativeImpl f) =
      (HexPolyMathlib.toPolynomial f).derivative := by
    rw [← DensePoly.derivative_eq_derivativeImpl,
      HexPolyMathlib.toPolynomial_derivative]
  have hdPoly : (HexPolyMathlib.toPolynomial f).derivative ≠ 0 := by
    apply Polynomial.derivative_ne_zero.mpr
    rw [HexPolyMathlib.natDegree_toPolynomial]
    omega
  have hassociated := gcd_associated f (DensePoly.derivativeImpl f) hf
  rw [hderiv] at hassociated
  have hm := Hex.PolyQuot.Roots.rootMultiplicity_associated hassociated x
  rw [Hex.PolyQuot.Roots.rootMultiplicity_gcd _ _ hfPoly hdPoly x] at hm
  have haF := (gcd_divisors f (DensePoly.derivativeImpl f) hf).1
  have hquotient := Hex.PolyQuot.Roots.rootMultiplicity_div f a haF hfPoly x
  change (HexPolyMathlib.toPolynomial (f / a)).rootMultiplicity x = _
  rw [hquotient, hm]
  by_cases hx : (HexPolyMathlib.toPolynomial f).IsRoot x
  · have hr := (Polynomial.rootMultiplicity_pos hfPoly).mpr hx
    rw [Polynomial.derivative_rootMultiplicity_of_root hx, ite_eq_left hx]
    omega
  · rw [Polynomial.rootMultiplicity_eq_zero hx, ite_eq_right hx]
    simp

/-- At counter `i`, the current polynomial contains each remaining root once.
The derivative quotient records how many copies remain in the original input.
The fields refer to the polynomials carried by the executable recurrence. -/
structure Invariant {K : Type*} [Field K] [DecidableEq K]
    (f : DensePoly K) (i : Nat) (v w : DensePoly K) : Prop where
  positive : 0 < i
  nonzero : v ≠ 0
  simple : ∀ x, (HexPolyMathlib.toPolynomial v).rootMultiplicity x ≤ 1
  roots : ∀ x, (HexPolyMathlib.toPolynomial v).IsRoot x ↔
    i ≤ (HexPolyMathlib.toPolynomial f).rootMultiplicity x
  derivative : ∀ x, (HexPolyMathlib.toPolynomial v).IsRoot x →
    (HexPolyMathlib.toPolynomial w).eval x =
      (((HexPolyMathlib.toPolynomial f).rootMultiplicity x : K) - (i : K) + 1) *
        (HexPolyMathlib.toPolynomial v).derivative.eval x

/-- The executable gcd and derivative-quotient setup establishes the
invariant at counter one, including nonmonic inputs. -/
theorem Invariant.init {K : Type*} [Field K] [CharZero K] [DecidableEq K]
    (f : DensePoly K) (hf : f ≠ 0) (hdegree : 0 < f.natDegree) :
    let a := DensePoly.monicize (DensePoly.gcd f (DensePoly.derivativeImpl f))
    Invariant f 1 (f / a) (DensePoly.derivativeImpl f / a) := by
  let a := DensePoly.monicize (DensePoly.gcd f (DensePoly.derivativeImpl f))
  have haF := (gcd_divisors f (DensePoly.derivativeImpl f) hf).1
  have hv : f / a ≠ 0 := by
    intro h
    have he := divide_mul f a haF
    rw [h, HexPolyMathlib.toPolynomial_zero, zero_mul] at he
    exact polynomial_ne_zero f hf he.symm
  refine ⟨by omega, hv, ?_, ?_, ?_⟩
  · intro x
    rw [initial_multiplicity f x hf hdegree]
    split <;> omega
  · intro x
    rw [← Polynomial.rootMultiplicity_pos (polynomial_ne_zero (f / a) hv),
      initial_multiplicity f x hf hdegree]
    by_cases hx : (HexPolyMathlib.toPolynomial f).IsRoot x
    · have hr := (Polynomial.rootMultiplicity_pos (polynomial_ne_zero f hf)).mpr hx
      rw [ite_eq_left hx]
      omega
    · rw [ite_eq_right hx, Polynomial.rootMultiplicity_eq_zero hx]
      omega
  · intro x hx
    have hm : (HexPolyMathlib.toPolynomial (f / a)).rootMultiplicity x =
        if (HexPolyMathlib.toPolynomial f).IsRoot x then 1 else 0 :=
      initial_multiplicity f x hf hdegree
    have hr := (Polynomial.rootMultiplicity_pos (polynomial_ne_zero (f / a) hv)).mpr hx
    have hfroot : (HexPolyMathlib.toPolynomial f).IsRoot x := by
      by_contra hn
      rw [ite_eq_right hn] at hm
      omega
    simpa only [Nat.cast_one, sub_add_cancel] using eval_initial f x hf hdegree hfroot

private theorem derivative_ne_zero {K : Type*} [Field K] [DecidableEq K]
    {v : DensePoly K} (hv : v ≠ 0)
    (hs : ∀ x, (HexPolyMathlib.toPolynomial v).rootMultiplicity x ≤ 1)
    (x : K) (hx : (HexPolyMathlib.toPolynomial v).IsRoot x) :
    (HexPolyMathlib.toPolynomial v).derivative.eval x ≠ 0 := by
  intro h
  have hm := (Polynomial.one_lt_rootMultiplicity_iff_isRoot
    (polynomial_ne_zero v hv)).mpr ⟨hx, h⟩
  have hb := hs x
  omega

private theorem quotient_ne_zero {K : Type*} [Field K] [DecidableEq K]
    (v z : DensePoly K) (hv : v ≠ 0) (hz : z ∣ v) : v / z ≠ 0 := by
  intro h
  have he := divide_mul v z hz
  rw [h, HexPolyMathlib.toPolynomial_zero, zero_mul] at he
  exact polynomial_ne_zero v hv he.symm

private theorem quotient_roots {K : Type*} [Field K] [DecidableEq K]
    (v z : DensePoly K) (hv : v ≠ 0) (hz : z ∣ v)
    (hs : ∀ x, (HexPolyMathlib.toPolynomial v).rootMultiplicity x ≤ 1) (x : K) :
    (HexPolyMathlib.toPolynomial (v / z)).IsRoot x ↔
      (HexPolyMathlib.toPolynomial v).IsRoot x ∧
        ¬(HexPolyMathlib.toPolynomial z).IsRoot x := by
  have hvPoly := polynomial_ne_zero v hv
  have hqPoly := polynomial_ne_zero (v / z) (quotient_ne_zero v z hv hz)
  have hzPoly : HexPolyMathlib.toPolynomial z ≠ 0 := by
    intro h
    have he := divide_mul v z hz
    rw [h, mul_zero] at he
    exact hvPoly he.symm
  have hm := Hex.PolyQuot.Roots.rootMultiplicity_div v z hz hvPoly x
  have hzle := Polynomial.rootMultiplicity_le_rootMultiplicity_of_dvd hvPoly
    (HexPolyMathlib.toPolynomial_dvd_iff.mpr hz) x
  have hsx := hs x
  rw [← Polynomial.rootMultiplicity_pos hqPoly, hm,
    ← Polynomial.rootMultiplicity_pos hvPoly, ← Polynomial.rootMultiplicity_pos hzPoly]
  omega

/-- The gcd emitted in a Yun round has precisely the roots whose original
multiplicity equals the current counter. -/
theorem Invariant.component {K : Type*} [Field K] [CharZero K] [DecidableEq K]
    {f v w : DensePoly K} {i : Nat} (h : Invariant f i v w) (x : K) :
    let t := w - DensePoly.derivativeImpl v
    let z := DensePoly.monicize (DensePoly.gcd v t)
    (HexPolyMathlib.toPolynomial z).IsRoot x ↔
      (HexPolyMathlib.toPolynomial f).rootMultiplicity x = i := by
  let t := w - DensePoly.derivativeImpl v
  let z := DensePoly.monicize (DensePoly.gcd v t)
  change (HexPolyMathlib.toPolynomial z).IsRoot x ↔
    (HexPolyMathlib.toPolynomial f).rootMultiplicity x = i
  have hg := gcd_associated v t h.nonzero
  have hz : (HexPolyMathlib.toPolynomial z).IsRoot x ↔
      (HexPolyMathlib.toPolynomial v).IsRoot x ∧
        (HexPolyMathlib.toPolynomial t).IsRoot x := by
    rw [← Polynomial.dvd_iff_isRoot, hg.dvd_iff_dvd_right,
      Polynomial.dvd_iff_isRoot, Polynomial.isRoot_gcd_iff_isRoot_left_right]
  have ht (hx : (HexPolyMathlib.toPolynomial v).IsRoot x) :
      (HexPolyMathlib.toPolynomial t).IsRoot x ↔
        (HexPolyMathlib.toPolynomial f).rootMultiplicity x = i := by
    have hd := derivative_ne_zero h.nonzero h.simple x hx
    have he : (HexPolyMathlib.toPolynomial t).eval x =
        (((HexPolyMathlib.toPolynomial f).rootMultiplicity x : K) - (i : K)) *
          (HexPolyMathlib.toPolynomial v).derivative.eval x := by
      dsimp [t]
      rw [HexPolyMathlib.toPolynomial_sub, ← DensePoly.derivative_eq_derivativeImpl,
        HexPolyMathlib.toPolynomial_derivative, Polynomial.eval_sub, h.derivative x hx]
      ring
    rw [Polynomial.IsRoot, he, mul_eq_zero, or_iff_left hd,
      sub_eq_zero, Nat.cast_inj]
  rw [hz]
  constructor
  · rintro ⟨hx, htroot⟩
    exact (ht hx).mp htroot
  · intro hm
    have hx : (HexPolyMathlib.toPolynomial v).IsRoot x :=
      (h.roots x).mpr (by omega)
    exact ⟨hx, (ht hx).mpr hm⟩

/-- The exact divisions executed by a Yun round preserve the invariant at
the next multiplicity counter. No degree decrease of `v` is assumed. -/
theorem Invariant.step {K : Type*} [Field K] [CharZero K] [DecidableEq K]
    {f v w : DensePoly K} {i : Nat} (h : Invariant f i v w) :
    let t := w - DensePoly.derivativeImpl v
    let z := DensePoly.monicize (DensePoly.gcd v t)
    Invariant f (i + 1) (v / z) (t / z) := by
  let t := w - DensePoly.derivativeImpl v
  let z := DensePoly.monicize (DensePoly.gcd v t)
  have hd := gcd_divisors v t h.nonzero
  have hq := quotient_ne_zero v z h.nonzero hd.1
  refine ⟨by have := h.positive; omega, hq, ?_, ?_, ?_⟩
  · intro x
    rw [Hex.PolyQuot.Roots.rootMultiplicity_div v z hd.1
      (polynomial_ne_zero v h.nonzero) x]
    have hv := h.simple x
    omega
  · intro x
    have hc : (HexPolyMathlib.toPolynomial z).IsRoot x ↔
        (HexPolyMathlib.toPolynomial f).rootMultiplicity x = i := h.component x
    rw [quotient_roots v z h.nonzero hd.1 h.simple x, h.roots x, hc]
    omega
  · intro x hx
    have ⟨hv, hz⟩ := (quotient_roots v z h.nonzero hd.1 h.simple x).mp hx
    have hxzero : (HexPolyMathlib.toPolynomial (v / z)).eval x = 0 := hx
    have hzEval : (HexPolyMathlib.toPolynomial z).eval x ≠ 0 := hz
    have hvderiv : (HexPolyMathlib.toPolynomial v).derivative.eval x =
        (HexPolyMathlib.toPolynomial (v / z)).derivative.eval x *
          (HexPolyMathlib.toPolynomial z).eval x := by
      have he := congrArg (fun p : Polynomial K => p.derivative.eval x)
        (divide_mul v z hd.1)
      simpa only [Polynomial.derivative_mul, Polynomial.eval_add,
        Polynomial.eval_mul, hxzero, zero_mul, add_zero] using he.symm
    apply mul_right_cancel₀ hzEval
    calc
      _ = (HexPolyMathlib.toPolynomial t).eval x := by
        simpa only [Polynomial.eval_mul] using
          congrArg (Polynomial.eval x) (divide_mul t z hd.2)
      _ = (HexPolyMathlib.toPolynomial w).eval x -
          (HexPolyMathlib.toPolynomial v).derivative.eval x := by
        dsimp [t]
        rw [HexPolyMathlib.toPolynomial_sub, ← DensePoly.derivative_eq_derivativeImpl,
          HexPolyMathlib.toPolynomial_derivative, Polynomial.eval_sub]
      _ = (((HexPolyMathlib.toPolynomial f).rootMultiplicity x : K) - (i : K)) *
          (HexPolyMathlib.toPolynomial v).derivative.eval x := by
        rw [h.derivative x hv]
        ring
      _ = _ := by
        rw [hvderiv, Nat.cast_add, Nat.cast_one]
        ring

/-- The remaining multiplicity weight sums the copies still represented at
counter `i`. It decreases even when the emitted gcd is constant. -/
noncomputable def remaining {K : Type*} [Field K] [DecidableEq K]
    (f : DensePoly K) (i : Nat) : Nat :=
  (HexPolyMathlib.toPolynomial f).roots.toFinset.sum fun x =>
    (HexPolyMathlib.toPolynomial f).rootMultiplicity x + 1 - i

/-- Over an algebraically closed field, the initial remaining multiplicity
weight is the input's degree. -/
theorem remaining_one {K : Type*} [Field K] [DecidableEq K] [IsAlgClosed K]
    (f : DensePoly K) : remaining f 1 = f.natDegree := by
  unfold remaining
  simp only [Nat.add_sub_cancel, ← Polynomial.count_roots]
  rw [Multiset.toFinset_sum_count_eq, IsAlgClosed.card_roots_eq_natDegree,
    HexPolyMathlib.natDegree_toPolynomial]

/-- Advancing the multiplicity counter removes one copy of every remaining
root from the weight. -/
theorem remaining_succ {K : Type*} [Field K] [DecidableEq K]
    (f : DensePoly K) (i : Nat) :
    remaining f i = remaining f (i + 1) +
      (HexPolyMathlib.toPolynomial f).roots.toFinset.sum
        (fun x => if i ≤ (HexPolyMathlib.toPolynomial f).rootMultiplicity x then 1 else 0) := by
  unfold remaining
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro x hx
  split <;> omega

/-- On a nonconstant loop state the remaining multiplicity weight strictly
decreases. This supplies descent for rounds which emit no factor. -/
theorem Invariant.remaining_lt {K : Type*} [Field K] [CharZero K] [DecidableEq K]
    [IsAlgClosed K] {f v w : DensePoly K} {i : Nat}
    (h : Invariant f i v w) (hdegree : 0 < v.natDegree) :
    remaining f (i + 1) < remaining f i := by
  have hpos : 0 < (HexPolyMathlib.toPolynomial v).natDegree := by
    rw [HexPolyMathlib.natDegree_toPolynomial]
    exact hdegree
  obtain ⟨x, hx⟩ := IsAlgClosed.exists_root (HexPolyMathlib.toPolynomial v)
    (ne_of_gt (Polynomial.natDegree_pos_iff_degree_pos.mp hpos))
  have hr := (h.roots x).mp hx
  have hp := h.positive
  have hrpos : 0 < (HexPolyMathlib.toPolynomial f).rootMultiplicity x := by omega
  have hmem : x ∈ (HexPolyMathlib.toPolynomial f).roots.toFinset := by
    rw [Multiset.mem_toFinset, ← Multiset.count_pos, Polynomial.count_roots]
    exact hrpos
  have hsum : 0 < (HexPolyMathlib.toPolynomial f).roots.toFinset.sum
      (fun x => if i ≤ (HexPolyMathlib.toPolynomial f).rootMultiplicity x then 1 else 0) := by
    have hle := Finset.single_le_sum
      (fun y hy => Nat.zero_le
        (if i ≤ (HexPolyMathlib.toPolynomial f).rootMultiplicity y then 1 else 0)) hmem
    rw [ite_eq_left hr] at hle
    omega
  rw [remaining_succ f i]
  omega

/-- The decreasing remaining-multiplicity weight bounds the number of
actual recurrence rounds, including rounds with constant emitted gcd. -/
theorem Invariant.loop_weight {K : Type*} [Field K] [CharZero K] [DecidableEq K]
    [IsAlgClosed K] {f v w : DensePoly K} {i : Nat} (h : Invariant f i v w)
    (extra : Nat) (out : Array (DensePoly K × Nat)) :
    loop v w i (remaining f i + extra) out = loop v w i (remaining f i) out := by
  have bound : ∀ (r i : Nat) (v w : DensePoly K),
      Invariant f i v w → remaining f i ≤ r →
      ∀ (extra : Nat) (out : Array (DensePoly K × Nat)),
        loop v w i (r + extra) out = loop v w i r out := by
    intro r
    induction r with
    | zero =>
        intro i v w h hr extra out
        have hv : v.natDegree = 0 := by
          by_contra hn
          have ht := h.remaining_lt (Nat.pos_of_ne_zero hn)
          omega
        cases extra <;> simp only [loop, hv, ↓reduceIte]
    | succ r ih =>
        intro i v w h hr extra out
        by_cases hv : v.natDegree = 0
        · simp only [Nat.succ_add, loop, hv, ↓reduceIte]
        · have ht := h.remaining_lt (Nat.pos_of_ne_zero hv)
          have hn : remaining f (i + 1) ≤ r := by omega
          simp only [Nat.succ_add, loop, hv, ↓reduceIte]
          exact ih _ _ _ h.step hn extra _
  exact bound _ _ _ _ h (Nat.le_refl _) extra out

/-- The producer's original-degree fuel covers every multiplicity round,
including gaps where no factor is emitted. -/
theorem initial_loop_bound {K : Type*} [Field K] [CharZero K] [DecidableEq K]
    [IsAlgClosed K] (f : DensePoly K) (hf : f ≠ 0) (hdegree : 0 < f.natDegree) :
    let a := DensePoly.monicize (DensePoly.gcd f (DensePoly.derivativeImpl f))
    loop (f / a) (DensePoly.derivativeImpl f / a) 1 (f.natDegree + 1) #[] =
      loop (f / a) (DensePoly.derivativeImpl f / a) 1 f.natDegree #[] := by
  have h := (Invariant.init f hf hdegree).loop_weight 1 #[]
  simpa only [remaining_one] using h

private theorem hom_zero {K L : Type*} [Field K] [Field L]
    (φ : K →+* L) (x : K) : φ x = 0 ↔ x = 0 := map_eq_zero φ

private theorem interpret_injective {K L : Type*} [Field K] [Field L]
    [DecidableEq K] [DecidableEq L] (φ : K →+* L) :
    Function.Injective (DensePoly.Interpret.map φ (hom_zero φ)) := by
  intro p q hpq
  apply DensePoly.ext_coeff
  intro i
  apply φ.injective
  simpa only [DensePoly.Interpret.map_coeff] using
    congrArg (fun r : DensePoly L => r.coeff i) hpq

/-- The original-degree loop bound descends along a field embedding into
an algebraically closed extension. -/
theorem loop_bound_map {K L : Type*} [Field K] [Field L] [CharZero L]
    [DecidableEq K] [DecidableEq L] [IsAlgClosed L]
    (φ : K →+* L) (f : DensePoly K) (hf : f ≠ 0) (hd : 0 < f.natDegree) (extra : Nat) :
    let a := DensePoly.monicize (DensePoly.gcd f (DensePoly.derivativeImpl f))
    loop (f / a) (DensePoly.derivativeImpl f / a) 1 (f.natDegree + extra) #[] =
      loop (f / a) (DensePoly.derivativeImpl f / a) 1 f.natDegree #[] := by
  let ψ := DensePoly.Interpret.map φ (hom_zero φ)
  let a := DensePoly.monicize (DensePoly.gcd f (DensePoly.derivativeImpl f))
  have hderiv : ∀ p : DensePoly K, ψ (DensePoly.derivativeImpl p) =
      DensePoly.derivativeImpl (ψ p) := by
    intro p
    simpa only [← DensePoly.derivative_eq_derivativeImpl] using
      DensePoly.Interpret.map_derivative φ (hom_zero φ)
        (fun n => map_natCast φ n) (fun x y => map_mul φ x y) p
  have ha : ψ a = DensePoly.monicize
      (DensePoly.gcd (ψ f) (DensePoly.derivativeImpl (ψ f))) := by
    dsimp only [ψ, a]
    rw [DensePoly.Interpret.map_monicize φ (hom_zero φ)
      (fun x y => map_mul φ x y) (fun x => map_inv₀ φ x),
      DensePoly.Interpret.map_gcd φ (hom_zero φ)
        (fun x y => map_sub φ x y) (fun x y => map_mul φ x y)
        (fun x y => map_div₀ φ x y)]
    exact congrArg (fun q : DensePoly L => DensePoly.monicize (DensePoly.gcd (ψ f) q))
      (hderiv f)
  have hdiv : ∀ p q : DensePoly K, ψ (p / q) = ψ p / ψ q :=
    DensePoly.Interpret.map_div φ (hom_zero φ)
      (fun x y => map_sub φ x y) (fun x y => map_mul φ x y)
      (fun x y => map_div₀ φ x y)
  have hmap (fuel : Nat) := map_loop φ (hom_zero φ)
    (fun x y => map_sub φ x y) (fun x y => map_mul φ x y)
    (fun x y => map_div₀ φ x y) (fun x => map_inv₀ φ x)
    (fun n => map_natCast φ n) (f / a) (DensePoly.derivativeImpl f / a)
    1 fuel #[]
  change loop (f / a) (DensePoly.derivativeImpl f / a) 1 (f.natDegree + extra) #[] =
    loop (f / a) (DensePoly.derivativeImpl f / a) 1 f.natDegree #[]
  have hinj : ∀ x y : DensePoly K × Nat,
      (ψ x.1, x.2) = (ψ y.1, y.2) → x = y := by
    intro x y h
    exact Prod.ext (interpret_injective φ (congrArg Prod.fst h))
      (congrArg (fun e : DensePoly L × Nat => e.2) h)
  apply (Array.map_inj_right hinj).mp
  rw [hmap, hmap]
  simp only [Array.map_empty]
  change loop (ψ (f / a)) (ψ (DensePoly.derivativeImpl f / a)) 1
      (f.natDegree + extra) #[] =
    loop (ψ (f / a)) (ψ (DensePoly.derivativeImpl f / a)) 1 f.natDegree #[]
  simp only [hdiv, hderiv, ha]
  have hf' : ψ f ≠ 0 := by
    intro hz
    exact hf ((DensePoly.Interpret.map_eq_zero φ
      (hom_zero φ) f).mp hz)
  have hd' : 0 < (ψ f).natDegree := by
    simpa only [ψ, DensePoly.Interpret.map_degree] using hd
  simpa only [remaining_one, ψ, DensePoly.Interpret.map_degree] using
    (Invariant.init (ψ f) hf' hd').loop_weight extra #[]

/-- Yun's initial recurrence needs at most the original degree over every
characteristic-zero field, via its algebraic closure. -/
theorem decompose_bound {K : Type*} [Field K] [CharZero K] [DecidableEq K]
    (f : DensePoly K) (hf : f ≠ 0) (hd : 0 < f.natDegree) (extra : Nat) :
    let a := DensePoly.monicize (DensePoly.gcd f (DensePoly.derivativeImpl f))
    loop (f / a) (DensePoly.derivativeImpl f / a) 1 (f.natDegree + extra) #[] =
      loop (f / a) (DensePoly.derivativeImpl f / a) 1 f.natDegree #[] := by
  classical
  exact loop_bound_map (algebraMap K (AlgebraicClosure K)) f hf hd extra

section Ordered

attribute [local instance] Lean.Grind.Semiring.natCast

/-- The degree bound applies to the public executable field instances;
its Mathlib interpretation retains every arithmetic operation. -/
theorem ordered_bound {K : Type*} [s : Lean.Grind.Field K]
    [LE K] [LT K] [Std.IsPreorder K] [Std.LawfulOrderLT K]
    [Lean.Grind.OrderedRing K] [DecidableEq K]
    (f : DensePoly K) (hf : f ≠ 0) (hd : 0 < f.natDegree) (extra : Nat) :
    let a := DensePoly.monicize (DensePoly.gcd f (DensePoly.derivativeImpl f))
    loop (f / a) (DensePoly.derivativeImpl f / a) 1 (f.natDegree + extra) #[] =
      loop (f / a) (DensePoly.derivativeImpl f / a) 1 f.natDegree #[] := by
  let : Field K := HexPolyMathlib.fieldOfGrind
  let : CharZero K := ⟨fun m n h =>
    @natCast_injective K s inferInstance inferInstance inferInstance inferInstance
      inferInstance m n h⟩
  have h := decompose_bound f hf hd extra
  exact h

end Ordered

private theorem degree_pos_of_root {K : Type*} [Field K] [DecidableEq K]
    (p : DensePoly K) (hp : HexPolyMathlib.toPolynomial p ≠ 0)
    (x : K) (hx : (HexPolyMathlib.toPolynomial p).IsRoot x) : 0 < p.natDegree := by
  have h := Polynomial.natDegree_pos_iff_degree_pos.mpr
    (Polynomial.degree_pos_of_root hp hx)
  rwa [HexPolyMathlib.natDegree_toPolynomial] at h

/-- Every root still present in the invariant appears in an emitted factor
with its original multiplicity, once the supplied fuel reaches that round. -/
theorem Invariant.loop_complete {K : Type*} [Field K] [CharZero K] [DecidableEq K]
    {f v w : DensePoly K} {i : Nat} (h : Invariant f i v w)
    (fuel : Nat) (out : Array (DensePoly K × Nat)) (x : K)
    (hi : i ≤ (HexPolyMathlib.toPolynomial f).rootMultiplicity x)
    (hfuel : (HexPolyMathlib.toPolynomial f).rootMultiplicity x < i + fuel) :
    ∃ entry ∈ loop v w i fuel out,
      entry.2 = (HexPolyMathlib.toPolynomial f).rootMultiplicity x ∧
        (HexPolyMathlib.toPolynomial entry.1).IsRoot x := by
  induction fuel generalizing v w i out with
  | zero => omega
  | succ fuel ih =>
      let t := w - DensePoly.derivativeImpl v
      let z := DensePoly.monicize (DensePoly.gcd v t)
      have hvroot := (h.roots x).mpr hi
      have hvdegree := degree_pos_of_root v (polynomial_ne_zero v h.nonzero) x hvroot
      simp only [loop, Nat.ne_of_gt hvdegree, ↓reduceIte]
      change ∃ entry ∈ loop (v / z) (t / z) (i + 1) fuel
          (if 0 < z.natDegree then out.push (z, i) else out),
        entry.2 = (HexPolyMathlib.toPolynomial f).rootMultiplicity x ∧
          (HexPolyMathlib.toPolynomial entry.1).IsRoot x
      by_cases hm : (HexPolyMathlib.toPolynomial f).rootMultiplicity x = i
      · have hzroot : (HexPolyMathlib.toPolynomial z).IsRoot x :=
          (h.component x).mpr hm
        have hzPoly : HexPolyMathlib.toPolynomial z ≠ 0 := by
          intro hz
          have he := divide_mul v z (gcd_divisors v t h.nonzero).1
          rw [hz, mul_zero] at he
          exact polynomial_ne_zero v h.nonzero he.symm
        have hzdegree := degree_pos_of_root z hzPoly x hzroot
        simp only [hzdegree, ↓reduceIte]
        refine ⟨(z, i), ?_, hm.symm, hzroot⟩
        exact mem_loop (v / z) (t / z) (i + 1) fuel
          (out.push (z, i)) (z, i) Array.mem_push_self
      · exact ih h.step _ (by omega) (by omega)

/-- Every root of a nonzero input occurs in the produced array with its
original multiplicity. This is a producer theorem, requiring no replay
acceptance premise and no algebraic-closedness hypothesis. -/
theorem decompose_root {K : Type*} [Field K] [CharZero K] [DecidableEq K]
    (f : DensePoly K) (x : K) (hf : f ≠ 0)
    (hx : (HexPolyMathlib.toPolynomial f).IsRoot x) :
    ∃ unit entries, decomposeRaw f = .factors unit entries ∧
      ∃ entry ∈ entries,
        entry.2 = (HexPolyMathlib.toPolynomial f).rootMultiplicity x ∧
          (HexPolyMathlib.toPolynomial entry.1).IsRoot x := by
  let a := DensePoly.monicize (DensePoly.gcd f (DensePoly.derivativeImpl f))
  have hfPoly := polynomial_ne_zero f hf
  have hdegree := degree_pos_of_root f hfPoly x hx
  have hr := (Polynomial.rootMultiplicity_pos hfPoly).mpr hx
  have hb := Hex.PolyQuot.Roots.rootMultiplicity_le_natDegree
    (HexPolyMathlib.toPolynomial f) hfPoly x
  rw [HexPolyMathlib.natDegree_toPolynomial] at hb
  have hcomplete := (Invariant.init f hf hdegree).loop_complete
    (f.natDegree + 1) #[] x (by omega) (by omega)
  refine ⟨f.leadingCoeff,
    loop (f / a) (DensePoly.derivativeImpl f / a) 1 (f.natDegree + 1) #[],
    ?_, hcomplete⟩
  have hsize : 0 < f.size := by
    rw [DensePoly.natDegree_eq_size_sub_one] at hdegree
    omega
  have hzero : f.isZero = false := (DensePoly.isZero_eq_false_iff f).mpr hsize
  simp only [decomposeRaw, a, hzero, Bool.false_eq_true,
    Nat.ne_of_gt hdegree, ↓reduceIte]

/-- The properties of one produced multiplicity component. -/
structure Component {K : Type*} [Field K] [DecidableEq K]
    (f : DensePoly K) (entry : DensePoly K × Nat) : Prop where
  positive : 0 < entry.2
  nonconstant : 0 < entry.1.natDegree
  monic : entry.1.Monic
  simple : ∀ x, (HexPolyMathlib.toPolynomial entry.1).rootMultiplicity x ≤ 1
  roots : ∀ x, (HexPolyMathlib.toPolynomial entry.1).IsRoot x ↔
    (HexPolyMathlib.toPolynomial f).rootMultiplicity x = entry.2

/-- A nonconstant gcd emitted by the current round is a valid component. -/
theorem Invariant.factor {K : Type*} [Field K] [CharZero K] [DecidableEq K]
    {f v w : DensePoly K} {i : Nat} (h : Invariant f i v w)
    (hdegree : 0 < (DensePoly.monicize
      (DensePoly.gcd v (w - DensePoly.derivativeImpl v))).natDegree) :
    Component f (DensePoly.monicize
      (DensePoly.gcd v (w - DensePoly.derivativeImpl v)), i) := by
  let t := w - DensePoly.derivativeImpl v
  let z := DensePoly.monicize (DensePoly.gcd v t)
  have hraw : DensePoly.gcd v t ≠ 0 := by
    intro hz
    have hd := DensePoly.gcd_dvd_left v t
    rw [hz] at hd
    obtain ⟨q, hq⟩ := hd
    exact h.nonzero (hq.trans (DensePoly.zero_mul q))
  refine ⟨h.positive, hdegree, DensePoly.monicize_monic hraw, ?_, ?_⟩
  · intro x
    have hd := (gcd_divisors v t h.nonzero).1
    have hm := Polynomial.rootMultiplicity_le_rootMultiplicity_of_dvd
      (polynomial_ne_zero v h.nonzero) (HexPolyMathlib.toPolynomial_dvd_iff.mpr hd) x
    exact hm.trans (h.simple x)
  · intro x
    exact h.component x

/-- Every emitted factor retains the original root multiplicity labels and
is monic, nonconstant, and simple at every coefficient-field root. -/
theorem Invariant.loop_factor {K : Type*} [Field K] [CharZero K] [DecidableEq K]
    {f v w : DensePoly K} {i : Nat} (h : Invariant f i v w)
    (fuel : Nat) (out : Array (DensePoly K × Nat))
    (hout : ∀ entry ∈ out, Component f entry) :
    ∀ entry ∈ loop v w i fuel out, Component f entry := by
  induction fuel generalizing v w i out with
  | zero => exact hout
  | succ fuel ih =>
      by_cases hv : v.natDegree = 0
      · simpa only [loop, hv, ↓reduceIte] using hout
      · let t := w - DensePoly.derivativeImpl v
        let z := DensePoly.monicize (DensePoly.gcd v t)
        simp only [loop, hv, ↓reduceIte]
        apply ih h.step
        intro entry he
        split at he
        · rename_i hzdegree
          rw [Array.mem_push] at he
          rcases he with he | he
          · exact hout entry he
          · subst entry
            exact h.factor hzdegree
        · exact hout entry he

/-- Every factor returned on a positive-degree input has the component
properties, independently of optional replay acceptance. -/
theorem decompose_factor {K : Type*} [Field K] [CharZero K] [DecidableEq K]
    (f : DensePoly K) (hdegree : 0 < f.natDegree)
    (unit : K) (entries : Array (DensePoly K × Nat))
    (hresult : decomposeRaw f = .factors unit entries) :
    ∀ entry ∈ entries, Component f entry := by
  have hf : f ≠ 0 := by
    intro h
    rw [h] at hdegree
    simp at hdegree
  have hsize : 0 < f.size := by
    rw [DensePoly.natDegree_eq_size_sub_one] at hdegree
    omega
  have hzero : f.isZero = false := (DensePoly.isZero_eq_false_iff f).mpr hsize
  have hfactor := (Invariant.init f hf hdegree).loop_factor
    (f.natDegree + 1) #[] (by intro entry he; simp at he)
  simp only [decomposeRaw, hzero, Bool.false_eq_true,
    Nat.ne_of_gt hdegree, ↓reduceIte, Decomposition.factors.injEq] at hresult
  rw [← hresult.2]
  exact hfactor

/-- Over an algebraically closed coefficient field every produced component
is separable, since each of its roots has multiplicity at most one. -/
theorem Component.separable {K : Type*} [Field K] [DecidableEq K] [IsAlgClosed K]
    {f : DensePoly K} {entry : DensePoly K × Nat} (h : Component f entry) :
    (HexPolyMathlib.toPolynomial entry.1).Separable := by
  have hn : (HexPolyMathlib.toPolynomial entry.1).roots.Nodup := by
    rw [Multiset.nodup_iff_count_le_one]
    intro x
    rw [Polynomial.count_roots]
    exact h.simple x
  exact (Polynomial.nodup_roots_iff_of_splits
    (polynomial_ne_zero entry.1 (DensePoly.monic_ne_zero h.monic))
    (IsAlgClosed.splits _)).mp hn

private theorem gcd_degree_zero {K : Type*} [Field K] [DecidableEq K]
    (p q : DensePoly K)
    (h : IsCoprime (HexPolyMathlib.toPolynomial p) (HexPolyMathlib.toPolynomial q)) :
    (DensePoly.gcd p q).natDegree = 0 := by
  have ha := HexPolyMathlib.toPolynomial_gcd_associated p q
  have hu := ha.isUnit_iff.mpr (EuclideanDomain.gcd_isUnit_iff.mpr h)
  have hd := Polynomial.isUnit_iff_degree_eq_zero.mp hu
  have hn := Polynomial.natDegree_eq_zero_iff_degree_le_zero.mpr hd.le
  simpa only [HexPolyMathlib.natDegree_toPolynomial] using hn

/-- The executable squarefreeness gcd check accepts every component. -/
theorem Component.squarefree {K : Type*} [Field K] [DecidableEq K] [IsAlgClosed K]
    {f : DensePoly K} {entry : DensePoly K × Nat} (h : Component f entry) :
    (DensePoly.gcd entry.1 (DensePoly.derivativeImpl entry.1)).natDegree = 0 := by
  apply gcd_degree_zero
  simpa only [← DensePoly.derivative_eq_derivativeImpl,
    HexPolyMathlib.toPolynomial_derivative] using
    (Polynomial.separable_def _).mp h.separable

/-- Components with different multiplicity labels have constant executable
gcd, since a common root would have both original multiplicities. -/
theorem Component.coprime {K : Type*} [Field K] [DecidableEq K] [IsAlgClosed K]
    {f : DensePoly K} {a b : DensePoly K × Nat}
    (ha : Component f a) (hb : Component f b) (hne : a.2 ≠ b.2) :
    (DensePoly.gcd a.1 b.1).natDegree = 0 := by
  by_contra hn
  have hp : 0 < (HexPolyMathlib.toPolynomial (DensePoly.gcd a.1 b.1)).natDegree := by
    rw [HexPolyMathlib.natDegree_toPolynomial]
    omega
  obtain ⟨x, hx⟩ := IsAlgClosed.exists_root
    (HexPolyMathlib.toPolynomial (DensePoly.gcd a.1 b.1))
    (ne_of_gt (Polynomial.natDegree_pos_iff_degree_pos.mp hp))
  have hg := HexPolyMathlib.toPolynomial_gcd_associated a.1 b.1
  have hroot : (EuclideanDomain.gcd (HexPolyMathlib.toPolynomial a.1)
      (HexPolyMathlib.toPolynomial b.1)).IsRoot x :=
    Polynomial.dvd_iff_isRoot.mp ((Polynomial.dvd_iff_isRoot.mpr hx).trans hg.dvd)
  obtain ⟨hax, hbx⟩ := Polynomial.isRoot_gcd_iff_isRoot_left_right.mp hroot
  exact hne (((ha.roots x).mp hax).symm.trans ((hb.roots x).mp hbx))

private theorem component_monic {K : Type*} [Field K] [DecidableEq K]
    {f : DensePoly K} {entry : DensePoly K × Nat} (h : Component f entry) :
    (HexPolyMathlib.toPolynomial entry.1).Monic := by
  rw [Polynomial.Monic.def, HexPolyMathlib.leadingCoeff_toPolynomial]
  exact h.monic

private theorem multiplicity_pow {K : Type*} [Field K]
    (p : Polynomial K) (hp : p ≠ 0) (n : Nat) (x : K) :
    (p ^ n).rootMultiplicity x = n * p.rootMultiplicity x := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [pow_succ, Polynomial.rootMultiplicity_mul
        (mul_ne_zero (_root_.pow_ne_zero n hp) hp), ih]
      simp [Nat.succ_mul]

private theorem multiplicity_prod {K : Type*} [Field K]
    (ps : List (Polynomial K)) (hp : ∀ p ∈ ps, p ≠ 0) (x : K) :
    ps.prod.rootMultiplicity x = (ps.map fun p => p.rootMultiplicity x).sum := by
  induction ps with
  | nil => simp
  | cons p ps ih =>
      have hhead : p ≠ 0 := hp p (by simp)
      have htail : ∀ q ∈ ps, q ≠ 0 := fun q hq => hp q (by simp [hq])
      have hprod : ps.prod ≠ 0 := List.prod_ne_zero (by
        intro hz
        exact htail 0 hz rfl)
      rw [List.prod_cons, Polynomial.rootMultiplicity_mul (mul_ne_zero hhead hprod),
        ih htail]
      simp

private theorem multiplicity_sum {K : Type*} [Field K] [DecidableEq K]
    (f : DensePoly K) (hf : HexPolyMathlib.toPolynomial f ≠ 0) (x : K)
    (entries : List (DensePoly K × Nat))
    (hcomp : ∀ entry ∈ entries, Component f entry)
    (hlabels : entries.Pairwise fun a b => a.2 < b.2)
    (hcomplete : (HexPolyMathlib.toPolynomial f).IsRoot x →
      ∃ entry ∈ entries, (HexPolyMathlib.toPolynomial entry.1).IsRoot x) :
    (entries.map fun entry => entry.2 *
      (HexPolyMathlib.toPolynomial entry.1).rootMultiplicity x).sum =
        (HexPolyMathlib.toPolynomial f).rootMultiplicity x := by
  revert hcomp hlabels hcomplete
  induction entries with
  | nil =>
      intro hcomp hlabels hcomplete
      have hr : (HexPolyMathlib.toPolynomial f).rootMultiplicity x = 0 := by
        by_contra hn
        obtain ⟨entry, he, _⟩ := hcomplete
          ((Polynomial.rootMultiplicity_pos hf).mp (Nat.pos_of_ne_zero hn))
        simp at he
      simp [hr]
  | cons entry entries ih =>
      intro hcomp hlabels hcomplete
      rw [List.pairwise_cons] at hlabels
      have hc : Component f entry := hcomp entry (by simp)
      have ht : ∀ e ∈ entries, Component f e := fun e he => hcomp e (by simp [he])
      have hne := (component_monic hc).ne_zero
      by_cases hz : (HexPolyMathlib.toPolynomial entry.1).rootMultiplicity x = 0
      · simp only [List.map_cons, List.sum_cons, hz, mul_zero, zero_add]
        apply ih ht hlabels.2
        intro hx
        obtain ⟨e, he, hx⟩ := hcomplete hx
        rw [List.mem_cons] at he
        rcases he with he | he
        · subst e
          have hpos := (Polynomial.rootMultiplicity_pos hne).mpr hx
          omega
        · exact ⟨e, he, hx⟩
      · have hroot := (Polynomial.rootMultiplicity_pos hne).mp (Nat.pos_of_ne_zero hz)
        have hlabel := (hc.roots x).mp hroot
        have hone : (HexPolyMathlib.toPolynomial entry.1).rootMultiplicity x = 1 := by
          have := hc.simple x
          omega
        have htail : (entries.map fun e => e.2 *
            (HexPolyMathlib.toPolynomial e.1).rootMultiplicity x).sum = 0 := by
          rw [List.sum_eq_zero_iff_forall_eq_nat]
          intro value hvalue
          obtain ⟨e, he, rfl⟩ := List.mem_map.mp hvalue
          by_cases hezero : (HexPolyMathlib.toPolynomial e.1).rootMultiplicity x = 0
          · simp [hezero]
          · have hecomp := ht e he
            have heroot := (Polynomial.rootMultiplicity_pos
              (component_monic hecomp).ne_zero).mp (Nat.pos_of_ne_zero hezero)
            have helabel := (hecomp.roots x).mp heroot
            have hlt := hlabels.1 e he
            omega
        simp only [List.map_cons, List.sum_cons, hone, mul_one, htail, add_zero, hlabel]

/-- The powered product of the actual producer components reconstructs the
input over an algebraically closed characteristic-zero coefficient field. -/
theorem decompose_product {K : Type*} [Field K] [CharZero K] [DecidableEq K]
    [IsAlgClosed K] (f : DensePoly K) (hd : 0 < f.natDegree)
    (unit : K) (entries : Array (DensePoly K × Nat))
    (hresult : decomposeRaw f = .factors unit entries) :
    reconstruct unit entries = f := by
  have hf : f ≠ 0 := by
    intro hz
    rw [hz] at hd
    simp at hd
  have hfPoly := polynomial_ne_zero f hf
  have hcomp := decompose_factor f hd unit entries hresult
  let ps := entries.toList.map fun entry =>
    (HexPolyMathlib.toPolynomial entry.1) ^ entry.2
  let product := ps.prod
  let normalized := HexPolyMathlib.toPolynomial f * Polynomial.C f.leadingCoeff⁻¹
  have hmonic : ∀ entry ∈ entries, (HexPolyMathlib.toPolynomial entry.1).Monic := by
    intro entry he
    exact component_monic (hcomp entry he)
  have hpmonic : ∀ p ∈ ps, p.Monic := by
    intro p hp
    obtain ⟨entry, he, rfl⟩ := List.mem_map.mp hp
    exact (hmonic entry (Array.mem_toList_iff.mp he)).pow entry.2
  have hproduct : product.Monic := by
    have aux : ∀ (qs : List (Polynomial K)),
        (∀ q ∈ qs, q.Monic) → qs.prod.Monic := by
      intro qs hqs
      induction qs with
      | nil => simp
      | cons q qs ih =>
          rw [List.prod_cons]
          exact (hqs q (by simp)).mul (ih (fun p hp => hqs p (by simp [hp])))
    exact aux ps hpmonic
  have hnormalized : normalized.Monic := by
    simpa only [HexPolyMathlib.leadingCoeff_toPolynomial] using
      Polynomial.monic_mul_leadingCoeff_inv hfPoly
  have hnonzero : ∀ p ∈ ps, p ≠ 0 := fun p hp => (hpmonic p hp).ne_zero
  have hlabels := decompose_labels f unit entries hresult
  have hmult (x : K) : product.rootMultiplicity x =
      (HexPolyMathlib.toPolynomial f).rootMultiplicity x := by
    have hcomplete : (HexPolyMathlib.toPolynomial f).IsRoot x →
        ∃ entry ∈ entries.toList, (HexPolyMathlib.toPolynomial entry.1).IsRoot x := by
      intro hx
      obtain ⟨u, es, hr, entry, he, _, hroot⟩ := decompose_root f x hf hx
      have heq : es = entries := by
        have hs := hr.symm.trans hresult
        simp only [Decomposition.factors.injEq] at hs
        exact hs.2
      subst es
      exact ⟨entry, Array.mem_toList_iff.mpr he, hroot⟩
    calc
      product.rootMultiplicity x = (ps.map fun p => p.rootMultiplicity x).sum :=
        multiplicity_prod ps hnonzero x
      _ = (entries.toList.map fun entry => entry.2 *
          (HexPolyMathlib.toPolynomial entry.1).rootMultiplicity x).sum := by
        congr 1
        simp only [ps, List.map_map]
        apply List.map_congr_left
        intro entry he
        exact multiplicity_pow _
          (hmonic entry (Array.mem_toList_iff.mp he)).ne_zero entry.2 x
      _ = (HexPolyMathlib.toPolynomial f).rootMultiplicity x :=
        multiplicity_sum f hfPoly x entries.toList
          (fun entry he => hcomp entry (Array.mem_toList_iff.mp he)) hlabels hcomplete
  have hlc : f.leadingCoeff ≠ 0 := by
    simpa only [← HexPolyMathlib.leadingCoeff_toPolynomial] using
      Polynomial.leadingCoeff_ne_zero.mpr hfPoly
  have hc : Polynomial.C f.leadingCoeff⁻¹ ≠ 0 :=
    Polynomial.C_ne_zero.mpr (inv_ne_zero hlc)
  have hnormalized_mult (x : K) : normalized.rootMultiplicity x =
      (HexPolyMathlib.toPolynomial f).rootMultiplicity x := by
    rw [Polynomial.rootMultiplicity_mul (mul_ne_zero hfPoly hc),
      Polynomial.rootMultiplicity_C, add_zero]
  have hroots : product.roots = normalized.roots := by
    apply Multiset.ext.mpr
    intro x
    rw [Polynomial.count_roots, Polynomial.count_roots, hmult, hnormalized_mult]
  have hsame : product = normalized := by
    rw [(IsAlgClosed.splits product).eq_prod_roots_of_monic hproduct,
      (IsAlgClosed.splits normalized).eq_prod_roots_of_monic hnormalized, hroots]
  have hu := (decompose_unit f unit entries hresult).1
  apply (HexPolyMathlib.equiv (R := K)).injective
  change HexPolyMathlib.toPolynomial (reconstruct unit entries) =
    HexPolyMathlib.toPolynomial f
  rw [toPolynomial_reconstruct_prod]
  change Polynomial.C unit * product = HexPolyMathlib.toPolynomial f
  rw [hsame, hu]
  calc
    Polynomial.C f.leadingCoeff * normalized =
        HexPolyMathlib.toPolynomial f *
          (Polynomial.C f.leadingCoeff * Polynomial.C f.leadingCoeff⁻¹) := by
      dsimp only [normalized]
      ring
    _ = HexPolyMathlib.toPolynomial f := by
      rw [← Polynomial.C_mul, mul_inv_cancel₀ hlc, Polynomial.C_1, mul_one]

private theorem map_reconstruct {K L : Type*} [Field K] [Field L]
    [DecidableEq K] [DecidableEq L] (φ : K →+* L)
    (unit : K) (entries : Array (DensePoly K × Nat)) :
    DensePoly.Interpret.map φ (hom_zero φ) (reconstruct unit entries) =
      reconstruct (φ unit) (entries.map fun entry =>
        (DensePoly.Interpret.map φ (hom_zero φ) entry.1, entry.2)) := by
  let ψ := DensePoly.Interpret.map φ (hom_zero φ)
  have hmul : ∀ p q : DensePoly K, ψ (p * q) = ψ p * ψ q :=
    DensePoly.Interpret.map_mul φ (hom_zero φ)
      (fun a b => map_add φ a b) (fun a b => map_mul φ a b)
  have hpow (p : DensePoly K) (n : Nat) : ψ (p ^ n) = (ψ p) ^ n :=
    DensePoly.Interpret.map_natPow φ (hom_zero φ)
      (fun a b => map_mul φ a b) (fun a b => map_add φ a b) (map_one φ) p n
  have hc (a : K) : ψ (DensePoly.C a) = DensePoly.C (φ a) := by
    apply DensePoly.ext_coeff
    intro i
    simp only [ψ, DensePoly.Interpret.map_coeff, DensePoly.coeff_C]
    split
    · rfl
    · exact map_zero φ
  have hfold (es : List (DensePoly K × Nat)) (acc : DensePoly K) :
      ψ (es.foldl (fun product entry => product * entry.1 ^ entry.2) acc) =
      (es.map fun entry => (ψ entry.1, entry.2)).foldl
        (fun product entry => product * entry.1 ^ entry.2) (ψ acc) := by
    induction es generalizing acc with
    | nil => rfl
    | cons entry es ih =>
        simpa only [List.foldl_cons, List.map_cons, hmul, hpow] using
          ih (acc * entry.1 ^ entry.2)
  simpa only [reconstruct, ← Array.foldl_toList, Array.toList_map, hc] using
    hfold entries.toList (DensePoly.C unit)

private theorem map_result {K L : Type*} [Field K] [Field L]
    [DecidableEq K] [DecidableEq L] (φ : K →+* L)
    (f : DensePoly K) (unit : K) (entries : Array (DensePoly K × Nat))
    (hresult : decomposeRaw f = .factors unit entries) :
    decomposeRaw (DensePoly.Interpret.map φ (hom_zero φ) f) =
      .factors (φ unit) (entries.map fun entry =>
        (DensePoly.Interpret.map φ (hom_zero φ) entry.1, entry.2)) := by
  have hmap := map_decomposeRaw φ (hom_zero φ)
    (fun a b => map_sub φ a b) (fun a b => map_mul φ a b)
    (fun a b => map_div₀ φ a b) (fun a => map_inv₀ φ a)
    (fun n => map_natCast φ n) f
  rw [hresult] at hmap
  exact hmap.symm

/-- Reconstruction descends along a field embedding into an algebraically
closed characteristic-zero extension. -/
theorem reconstruct_map {K L : Type*} [Field K] [Field L] [CharZero L]
    [DecidableEq K] [DecidableEq L] [IsAlgClosed L]
    (φ : K →+* L) (f : DensePoly K) (hd : 0 < f.natDegree)
    (unit : K) (entries : Array (DensePoly K × Nat))
    (hresult : decomposeRaw f = .factors unit entries) :
    reconstruct unit entries = f := by
  let ψ := DensePoly.Interpret.map φ (hom_zero φ)
  have htarget := map_result φ f unit entries hresult
  have hd' : 0 < (ψ f).natDegree := by
    simpa only [ψ, DensePoly.Interpret.map_degree] using hd
  have hprod := decompose_product (ψ f) hd' (φ unit)
    (entries.map fun entry => (ψ entry.1, entry.2)) htarget
  apply interpret_injective φ
  rw [map_reconstruct, hprod]

/-- Every positive-degree characteristic-zero producer result reconstructs
the input, independently of replay acceptance. -/
theorem decompose_reconstruct {K : Type*} [Field K] [CharZero K] [DecidableEq K]
    (f : DensePoly K) (hd : 0 < f.natDegree)
    (unit : K) (entries : Array (DensePoly K × Nat))
    (hresult : decomposeRaw f = .factors unit entries) :
    reconstruct unit entries = f := by
  classical
  exact reconstruct_map (algebraMap K (AlgebraicClosure K)) f hd unit entries hresult

private theorem degree_sum {K : Type*} [Zero K] [DecidableEq K]
    (entries : Array (DensePoly K × Nat)) : degreeSum entries =
    (entries.toList.map fun entry => entry.2 * entry.1.natDegree).sum := by
  simp only [degreeSum, ← Array.foldl_toList, List.sum_eq_foldl_nat, List.foldl_map]

private theorem monic_degree_prod {K : Type*} [Field K]
    (ps : List (Polynomial K)) (hp : ∀ p ∈ ps, p.Monic) :
    ps.prod.Monic ∧ ps.prod.natDegree = (ps.map Polynomial.natDegree).sum := by
  induction ps with
  | nil => simp
  | cons p ps ih =>
      have hh := hp p (by simp)
      have ht := ih (fun q hq => hp q (by simp [hq]))
      constructor
      · simpa only [List.prod_cons] using hh.mul ht.1
      · rw [List.prod_cons, hh.natDegree_mul ht.1, ht.2]
        simp

/-- The producer's powered factors account for exactly the original degree
over every characteristic-zero coefficient field. -/
theorem decompose_degree {K : Type*} [Field K] [CharZero K] [DecidableEq K]
    (f : DensePoly K) (hd : 0 < f.natDegree)
    (unit : K) (entries : Array (DensePoly K × Nat))
    (hresult : decomposeRaw f = .factors unit entries) :
    degreeSum entries = f.natDegree := by
  have hf : f ≠ 0 := by
    intro hz
    rw [hz] at hd
    simp at hd
  have hu := (decompose_unit f unit entries hresult).1
  have hunit : unit ≠ 0 := by
    rw [hu]
    simpa only [← HexPolyMathlib.leadingCoeff_toPolynomial] using
      Polynomial.leadingCoeff_ne_zero.mpr (polynomial_ne_zero f hf)
  have hcomp := decompose_factor f hd unit entries hresult
  let ps := entries.toList.map fun entry =>
    (HexPolyMathlib.toPolynomial entry.1) ^ entry.2
  have hmonic : ∀ p ∈ ps, p.Monic := by
    intro p hp
    obtain ⟨entry, he, rfl⟩ := List.mem_map.mp hp
    exact (component_monic (hcomp entry (Array.mem_toList_iff.mp he))).pow entry.2
  have hprod := monic_degree_prod ps hmonic
  have hlc : (Polynomial.C unit).leadingCoeff * ps.prod.leadingCoeff ≠ 0 := by
    rw [Polynomial.leadingCoeff_C, hprod.1.leadingCoeff, mul_one]
    exact hunit
  have hdegree : f.natDegree = (ps.map Polynomial.natDegree).sum := by
    rw [← HexPolyMathlib.natDegree_toPolynomial,
      ← decompose_reconstruct f hd unit entries hresult,
      toPolynomial_reconstruct_prod, Polynomial.natDegree_mul' hlc,
      Polynomial.natDegree_C, zero_add, hprod.2]
  rw [degree_sum]
  rw [hdegree]
  congr 1
  simp only [ps, List.map_map]
  apply List.map_congr_left
  intro entry he
  simp only [Function.comp_apply]
  rw [(component_monic (hcomp entry (Array.mem_toList_iff.mp he))).natDegree_pow,
    HexPolyMathlib.natDegree_toPolynomial]

/-- Each emitted factor passes the executable squarefree gcd check over
every characteristic-zero coefficient field. -/
theorem decompose_factor_gcd {K : Type*} [Field K] [CharZero K] [DecidableEq K]
    (f : DensePoly K) (hd : 0 < f.natDegree)
    (unit : K) (entries : Array (DensePoly K × Nat))
    (hresult : decomposeRaw f = .factors unit entries)
    (entry : DensePoly K × Nat) (he : entry ∈ entries) :
    (DensePoly.gcd entry.1 (DensePoly.derivativeImpl entry.1)).natDegree = 0 := by
  classical
  let φ := algebraMap K (AlgebraicClosure K)
  let ψ := DensePoly.Interpret.map φ (hom_zero φ)
  have ht := map_result φ f unit entries hresult
  have hd' : 0 < (ψ f).natDegree := by
    simpa only [ψ, DensePoly.Interpret.map_degree] using hd
  have hm : (ψ entry.1, entry.2) ∈
      entries.map (fun e => (ψ e.1, e.2)) := Array.mem_map.mpr ⟨entry, he, rfl⟩
  have hc := decompose_factor (ψ f) hd' (φ unit)
    (entries.map fun e => (ψ e.1, e.2)) ht (ψ entry.1, entry.2) hm
  have hg := DensePoly.Interpret.map_gcd φ (hom_zero φ)
    (fun a b => map_sub φ a b) (fun a b => map_mul φ a b)
    (fun a b => map_div₀ φ a b) entry.1 (DensePoly.derivativeImpl entry.1)
  have hder : ψ (DensePoly.derivativeImpl entry.1) =
      DensePoly.derivativeImpl (ψ entry.1) := by
    simpa only [← DensePoly.derivative_eq_derivativeImpl] using
      DensePoly.Interpret.map_derivative φ (hom_zero φ)
        (fun n => map_natCast φ n) (fun a b => map_mul φ a b) entry.1
  have hs := hc.squarefree
  change (DensePoly.gcd (ψ entry.1) (DensePoly.derivativeImpl (ψ entry.1))).natDegree = 0 at hs
  rw [← hder] at hs
  change (DensePoly.gcd (DensePoly.Interpret.map φ (hom_zero φ) entry.1)
    (DensePoly.Interpret.map φ (hom_zero φ) (DensePoly.derivativeImpl entry.1))).natDegree = 0 at hs
  rw [← hg, DensePoly.Interpret.map_degree] at hs
  exact hs

/-- Distinct producer multiplicity labels have constant executable gcd over
every characteristic-zero coefficient field. -/
theorem decompose_coprime {K : Type*} [Field K] [CharZero K] [DecidableEq K]
    (f : DensePoly K) (hd : 0 < f.natDegree)
    (unit : K) (entries : Array (DensePoly K × Nat))
    (hresult : decomposeRaw f = .factors unit entries)
    (a b : DensePoly K × Nat) (ha : a ∈ entries) (hb : b ∈ entries)
    (hne : a.2 ≠ b.2) : (DensePoly.gcd a.1 b.1).natDegree = 0 := by
  classical
  let φ := algebraMap K (AlgebraicClosure K)
  let ψ := DensePoly.Interpret.map φ (hom_zero φ)
  have ht := map_result φ f unit entries hresult
  have hd' : 0 < (ψ f).natDegree := by
    simpa only [ψ, DensePoly.Interpret.map_degree] using hd
  have hcomp := decompose_factor (ψ f) hd' (φ unit)
    (entries.map fun e => (ψ e.1, e.2)) ht
  have ha' := hcomp (ψ a.1, a.2) (Array.mem_map.mpr ⟨a, ha, rfl⟩)
  have hb' := hcomp (ψ b.1, b.2) (Array.mem_map.mpr ⟨b, hb, rfl⟩)
  have hg := DensePoly.Interpret.map_gcd φ (hom_zero φ)
    (fun a b => map_sub φ a b) (fun a b => map_mul φ a b)
    (fun a b => map_div₀ φ a b) a.1 b.1
  have hs := ha'.coprime hb' hne
  change (DensePoly.gcd (DensePoly.Interpret.map φ (hom_zero φ) a.1)
    (DensePoly.Interpret.map φ (hom_zero φ) b.1)).natDegree = 0 at hs
  rw [← hg, DensePoly.Interpret.map_degree] at hs
  exact hs

section Producer

attribute [local instance] Lean.Grind.Semiring.natCast

/-- Every public Yun result passes full exact replay, including repeated
factors, nonmonic inputs and gaps in multiplicity labels. -/
theorem decompose_sound {K : Type*} [s : Lean.Grind.Field K]
    [LE K] [LT K] [Std.IsPreorder K] [Std.LawfulOrderLT K]
    [Lean.Grind.OrderedRing K] [DecidableEq K] (f : DensePoly K) :
    check f (decompose f) = true := by
  by_cases hf : f = 0
  · subst f
    exact check_decompose_zero
  · by_cases hd : f.natDegree = 0
    · exact check_decompose_constant f hf hd
    · have hdegree : 0 < f.natDegree := Nat.pos_of_ne_zero hd
      change check f (decomposeRaw f) = true
      have hzero : f.isZero = false := by
        apply (DensePoly.isZero_eq_false_iff f).mpr
        have hs : f.size ≠ 0 := fun hs => hf ((DensePoly.size_eq_zero_iff f).mp hs)
        omega
      generalize hr : decomposeRaw f = result
      cases result with
      | zero =>
          simp only [decomposeRaw, hzero, Bool.false_eq_true, hd, ↓reduceIte] at hr
          cases hr
      | factors unit entries =>
          simp only [check, hzero, Bool.not_false, Bool.true_and,
            Bool.and_eq_true, decide_eq_true_eq]
          let : Field K := HexPolyMathlib.fieldOfGrind
          let : CharZero K := ⟨fun m n h =>
            @natCast_injective K s inferInstance inferInstance inferInstance inferInstance
              inferInstance m n h⟩
          have hu := (decompose_unit f unit entries hr).1
          have hunit : unit ≠ 0 := by
            rw [hu]
            simpa only [← HexPolyMathlib.leadingCoeff_toPolynomial] using
              Polynomial.leadingCoeff_ne_zero.mpr (polynomial_ne_zero f hf)
          have hcomp := decompose_factor f hdegree unit entries hr
          have hlabels := decompose_labels f unit entries hr
          have hproduct := decompose_reconstruct f hdegree unit entries hr
          have haccount := decompose_degree f hdegree unit entries hr
          have hall : entries.all (fun entry =>
              0 < entry.2 && 0 < entry.1.natDegree && decide (entry.1.leadingCoeff = 1) &&
                (DensePoly.gcd entry.1 (DensePoly.derivativeImpl entry.1)).natDegree == 0) = true := by
            rw [Array.all_eq_true_iff_forall_mem]
            intro entry he
            simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq]
            have hc := hcomp entry he
            exact ⟨⟨⟨hc.positive, hc.nonconstant⟩, hc.monic⟩,
              decompose_factor_gcd f hdegree unit entries hr entry he⟩
          have hcoprime : entries.toList.Pairwise fun a b =>
              (DensePoly.gcd a.1 b.1).natDegree = 0 := by
            apply hlabels.imp_of_mem
            intro a b ha hb hab
            exact decompose_coprime f hdegree unit entries hr a b
              (Array.mem_toList_iff.mp ha) (Array.mem_toList_iff.mp hb) (Nat.ne_of_lt hab)
          exact ⟨⟨⟨⟨⟨hunit, hall⟩, hlabels⟩, hcoprime⟩, hproduct⟩, haccount⟩

end Producer

section Integration

attribute [-instance] Field.toGrindField
attribute [local instance] Lean.Grind.Semiring.natCast

example (f : DensePoly Rat) (hf : f ≠ 0) (hd : 0 < f.natDegree) (extra : Nat) :
    let a := DensePoly.monicize (DensePoly.gcd f (DensePoly.derivativeImpl f))
    loop (f / a) (DensePoly.derivativeImpl f / a) 1 (f.natDegree + extra) #[] =
      loop (f / a) (DensePoly.derivativeImpl f / a) 1 f.natDegree #[] :=
  ordered_bound f hf hd extra

example (f : DensePoly Rat) : check f (decompose f) = true := decompose_sound f

-- The rational replay consumers use the executable field instance.
example (f : DensePoly Rat) (unit : Rat)
    (entries : Array (DensePoly Rat × Nat))
    (hdecomp : decompose f = .factors unit entries) :
    HexPolyMathlib.toPolynomial f =
      entries.toList.foldl (fun product entry =>
        product * (HexPolyMathlib.toPolynomial entry.1) ^ entry.2)
        (Polynomial.C unit) := by
  have hcheck := decompose_sound f
  rw [hdecomp] at hcheck
  exact check_product_polynomial f unit entries hcheck

example (f : DensePoly Rat) (unit : Rat)
    (entries : Array (DensePoly Rat × Nat))
    (hdecomp : decompose f = .factors unit entries)
    (entry : DensePoly Rat × Nat) (hmem : entry ∈ entries)
    (x : ℝ)
    (hroot : Polynomial.IsRoot
      ((HexPolyMathlib.toPolynomial entry.1).map (Rat.castHom ℝ)) x) :
    Polynomial.rootMultiplicity x
      ((HexPolyMathlib.toPolynomial f).map (Rat.castHom ℝ)) =
      entry.2 := by
  have hcheck := decompose_sound f
  rw [hdecomp] at hcheck
  exact check_real_rootMultiplicity f unit entries entry hmem hcheck x hroot

end Integration

-- This semantic selected-root field inherits inverse soundness from
-- the proved `Tarski.check_rootSum`; the generic producer theorem does not.
example {context : Nat} (d : Root context) (f : DensePoly (Value d)) :
    check f (decompose f) = true := decompose_sound f

/-- The actual cached packed recurrence passes full replay after interpreting
its coefficients as canonical real algebraic numbers. This instantiation
inherits the selected-root inverse dependency on the proved root-sum theorem. -/
theorem decompose_packed {context : Nat} {d : Root context}
    (h : Root.Handle d) (f : DensePoly (Root.Handle.Value h)) :
    check
      (DensePoly.Interpret.map
        (fun a : Root.Handle.Value h => a.value)
        (fun a => (Root.Handle.Value.eq_zero_iff a).symm) f)
      (Decomposition.map (fun a : Root.Handle.Value h => a.value)
        (fun a => (Root.Handle.Value.eq_zero_iff a).symm)
        (decomposeRaw f)) = true := by
  rw [map_packed]
  exact decompose_sound _

/-- info: 'Hex.RealClosure.Yun.decompose_packed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hex.RealClosure.Yun.decompose_packed

/-- info: 'Hex.RealClosure.Yun.decompose_product' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hex.RealClosure.Yun.decompose_product

/-- info: 'Hex.RealClosure.Yun.reconstruct_map' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hex.RealClosure.Yun.reconstruct_map

/-- info: 'Hex.RealClosure.Yun.decompose_reconstruct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hex.RealClosure.Yun.decompose_reconstruct

/-- info: 'Hex.RealClosure.Yun.decompose_degree' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hex.RealClosure.Yun.decompose_degree

/-- info: 'Hex.RealClosure.Yun.decompose_factor_gcd' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hex.RealClosure.Yun.decompose_factor_gcd

/-- info: 'Hex.RealClosure.Yun.decompose_coprime' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hex.RealClosure.Yun.decompose_coprime

/-- info: 'Hex.RealClosure.Yun.decompose_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hex.RealClosure.Yun.decompose_sound

/-- info: 'Hex.RealClosure.Yun.Invariant.loop_weight' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hex.RealClosure.Yun.Invariant.loop_weight

/-- info: 'Hex.RealClosure.Yun.loop_bound_map' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hex.RealClosure.Yun.loop_bound_map

/-- info: 'Hex.RealClosure.Yun.decompose_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hex.RealClosure.Yun.decompose_bound

/-- info: 'Hex.RealClosure.Yun.ordered_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hex.RealClosure.Yun.ordered_bound

/-- info: 'Hex.RealClosure.Yun.eval_initial' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hex.RealClosure.Yun.eval_initial

/-- info: 'Hex.RealClosure.Yun.Invariant.init' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hex.RealClosure.Yun.Invariant.init

/-- info: 'Hex.RealClosure.Yun.Invariant.component' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hex.RealClosure.Yun.Invariant.component

/-- info: 'Hex.RealClosure.Yun.Invariant.step' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hex.RealClosure.Yun.Invariant.step

/-- info: 'Hex.RealClosure.Yun.Invariant.remaining_lt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hex.RealClosure.Yun.Invariant.remaining_lt

/-- info: 'Hex.RealClosure.Yun.initial_loop_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hex.RealClosure.Yun.initial_loop_bound

/-- info: 'Hex.RealClosure.Yun.Invariant.loop_complete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hex.RealClosure.Yun.Invariant.loop_complete

/-- info: 'Hex.RealClosure.Yun.decompose_root' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hex.RealClosure.Yun.decompose_root

/-- info: 'Hex.RealClosure.Yun.Invariant.loop_factor' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hex.RealClosure.Yun.Invariant.loop_factor

/-- info: 'Hex.RealClosure.Yun.decompose_factor' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hex.RealClosure.Yun.decompose_factor

/-- info: 'Hex.RealClosure.Yun.Component.squarefree' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hex.RealClosure.Yun.Component.squarefree

/-- info: 'Hex.RealClosure.Yun.Component.coprime' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hex.RealClosure.Yun.Component.coprime

end Hex.RealClosure.Yun
