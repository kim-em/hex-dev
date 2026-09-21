/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexPoly.PseudoInterpret
public import HexPolyMathlib.Interpret
public import Mathlib.Algebra.Polynomial.RingDivision
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Algebra.Order.Ring.Basic

public section

/-! Interpretation of fraction-free division and gcd in a semantic field.
The coefficient representation requires no field structure. In particular,
integer coefficients embed in the field without a `Field Int` instance. -/
namespace HexPolyMathlib.Interpret

open Hex DensePoly

universe u v
variable {E : Type u} {K : Type v} [Zero E] [DecidableEq E]
variable [One E] [Add E] [Sub E] [Mul E]
variable [Field K] [DecidableEq K]
variable (f : E → K) (hz : ∀ a, f a = 0 ↔ a = 0)
variable (h1 : f (1 : E) = 1)
variable (ha : ∀ a b, f (a + b) = f a + f b)
variable (hs : ∀ a b, f (a - b) = f a - f b)
variable (hm : ∀ a b, f (a * b) = f a * f b)
include hz h1 ha hs hm

/-- The multiplier agrees with the fixed leading-coefficient power after interpretation. -/
theorem pseudo_multiplier (p q : DensePoly E) :
    f (pseudoDiv p q).multiplier = (f q.leadingCoeff) ^ pseudoExponent p q := by
  have h := congrArg PseudoResult.multiplier
    (DensePoly.Interpret.map_pseudoDiv f hz h1 ha hs hm p q)
  dsimp only at h
  rw [h, pseudoDiv_multiplier, DensePoly.Interpret.map_leading,
    DensePoly.Interpret.map_pseudoExponent]

/-- Every nonzero divisor has a nonzero recorded multiplier. -/
theorem pseudo_multiplier_ne_zero (p q : DensePoly E) (hq : q ≠ 0) :
    f (pseudoDiv p q).multiplier ≠ 0 := by
  rw [pseudo_multiplier f hz h1 ha hs hm]
  apply pow_ne_zero
  intro h
  have hc : q.leadingCoeff ≠ 0 := leadingCoeff_ne_zero_of_pos_size q
    (Nat.pos_of_ne_zero (fun h => hq ((size_eq_zero_iff q).mp h)))
  exact hc ((hz _).mp h)

/-- Reconstruction is an identity of interpreted polynomials, not stored representatives. -/
theorem pseudo_reconstruct (p q : DensePoly E) :
    Polynomial.C (f (pseudoDiv p q).multiplier) * interpret f hz p =
      interpret f hz (pseudoDiv p q).quotient * interpret f hz q +
        interpret f hz (pseudoDiv p q).remainder := by
  by_cases hq : q = 0
  · subst q
    simp [pseudoDiv_zero_right, h1, interpret_zero]
  · have h := pseudoDiv_reconstruct (DensePoly.Interpret.map f hz p)
      (DensePoly.Interpret.map f hz q) (fun h => hq ((DensePoly.Interpret.map_eq_zero f hz q).mp h))
    rw [← DensePoly.Interpret.map_pseudoDiv f hz h1 ha hs hm p q] at h
    have hh := congrArg toPolynomial h
    have ht (r : DensePoly E) : toPolynomial (DensePoly.Interpret.map f hz r) = interpret f hz r := by
      ext i
      simp only [coeff_toPolynomial, DensePoly.Interpret.map_coeff, coeff_interpret]
    simpa only [toPolynomial_scale, toPolynomial_mul, toPolynomial_add, ht] using hh

omit h1 ha hs hm in
/-- Interpreted remainders have strictly smaller degree, with zero recorded separately. -/
theorem pseudo_remainder_degree (p q : DensePoly E) (hq : q ≠ 0) :
    interpret f hz (pseudoDiv p q).remainder = 0 ∨
      (interpret f hz (pseudoDiv p q).remainder).natDegree < (interpret f hz q).natDegree := by
  have h := pseudoDiv_remainder_lt p q hq
  by_cases hr : (pseudoDiv p q).remainder = 0
  · simp only [hr, interpret_zero, true_or]
  · right
    simp only [natDegree_interpret, natDegree_eq_size_sub_one]
    have hp : 0 < (pseudoDiv p q).remainder.size :=
      Nat.pos_of_ne_zero (fun h => hr ((size_eq_zero_iff _).mp h))
    omega

/-- The pseudo-remainder is the field remainder times its recorded nonzero scalar. -/
theorem pseudo_rem (p q : DensePoly E) :
    interpret f hz (pseudoDiv p q).remainder =
      Polynomial.C (f (pseudoDiv p q).multiplier) * (interpret f hz p % interpret f hz q) := by
  by_cases hq : q = 0
  · subst q
    simp [pseudoDiv_zero_right, h1, interpret_zero]
  · have hq' : interpret f hz q ≠ 0 := fun h => hq ((interpret_eq_zero f hz q).mp h)
    have hr : interpret f hz (pseudoDiv p q).remainder % interpret f hz q =
        interpret f hz (pseudoDiv p q).remainder := by
      rcases pseudo_remainder_degree f hz p q hq with hr | hr
      · simp only [hr, EuclideanDomain.zero_mod]
      · exact (Polynomial.mod_eq_self_iff hq').mpr (Polynomial.degree_lt_degree hr)
    have h := congrArg (fun r => r % interpret f hz q) (pseudo_reconstruct f hz h1 ha hs hm p q)
    have hmod : (interpret f hz (pseudoDiv p q).quotient * interpret f hz q) % interpret f hz q = 0 :=
      EuclideanDomain.mod_eq_zero.mpr (dvd_mul_left _ _)
    rw [Polynomial.add_mod, hmod, _root_.zero_add, hr] at h
    rw [← h]
    simp only [Polynomial.mod_def, ← Polynomial.smul_eq_C_mul, Polynomial.smul_modByMonic]

/-- Both pseudo-division outputs agree with field division after scaling by the
recorded multiplier; no inverse operation is required on the source carrier. -/
theorem pseudo_divMod (p q : DensePoly E) :
    (interpret f hz (pseudoDiv p q).quotient, interpret f hz (pseudoDiv p q).remainder) =
      (Polynomial.C (f (pseudoDiv p q).multiplier) * (interpret f hz p / interpret f hz q),
       Polynomial.C (f (pseudoDiv p q).multiplier) * (interpret f hz p % interpret f hz q)) := by
  by_cases hq : q = 0
  · subst q
    simp [pseudoDiv_zero_right, h1, interpret_zero]
  · apply Prod.ext
    · have hq' : interpret f hz q ≠ 0 := fun h => hq ((interpret_eq_zero f hz q).mp h)
      apply mul_right_cancel₀ hq'
      have hrec := pseudo_reconstruct f hz h1 ha hs hm p q
      have hrem := pseudo_rem f hz h1 ha hs hm p q
      have hdiv := EuclideanDomain.div_add_mod (interpret f hz p) (interpret f hz q)
      rw [hrem] at hrec
      have hc : (Polynomial.C (f (pseudoDiv p q).multiplier) *
          (interpret f hz p / interpret f hz q)) * interpret f hz q +
          Polynomial.C (f (pseudoDiv p q).multiplier) * (interpret f hz p % interpret f hz q) =
          Polynomial.C (f (pseudoDiv p q).multiplier) * interpret f hz p := by
        rw [mul_assoc, ← mul_add, mul_comm (interpret f hz p / interpret f hz q) (interpret f hz q), hdiv]
      exact add_right_cancel (hrec.symm.trans hc.symm)
    · exact pseudo_rem f hz h1 ha hs hm p q

private theorem pseudo_dvd_step (p q : DensePoly E) (hq : q ≠ 0) (d : Polynomial K)
    (hdq : d ∣ interpret f hz q) :
    d ∣ interpret f hz (pseudoDiv p q).remainder ↔ d ∣ interpret f hz p := by
  have hmul : d ∣ interpret f hz (pseudoDiv p q).quotient * interpret f hz q :=
    dvd_mul_of_dvd_right hdq _
  have h := (dvd_add_right (c := interpret f hz (pseudoDiv p q).remainder) hmul).symm
  rw [← pseudo_reconstruct f hz h1 ha hs hm p q] at h
  exact h.trans (Polynomial.dvd_C_mul (pseudo_multiplier_ne_zero f hz h1 ha hs hm p q hq))

/-- The actual fraction-free gcd has precisely the common divisors of the inputs
in the semantic field. It need not be a polynomial gcd over the stored domain. -/
theorem dvd_pseudoGcd (p q : DensePoly E) (d : Polynomial K) :
    d ∣ interpret f hz (pseudoGcd p q) ↔ d ∣ interpret f hz p ∧ d ∣ interpret f hz q := by
  induction n : q.size using Nat.strongRecOn generalizing p q with
  | ind n ih =>
    by_cases hq : q = 0
    · subst q
      simp only [pseudoGcd_zero_right, interpret_zero, dvd_zero, and_true]
    · rw [pseudoGcd_step p q hq]
      rw [ih (pseudoDivMod p q).2.size
        (by simpa only [← n] using pseudoDivMod_remainder_lt p q hq) q _ rfl]
      change (d ∣ interpret f hz q ∧ d ∣ interpret f hz (pseudoDiv p q).remainder) ↔ _
      constructor
      · rintro ⟨hdq, hdr⟩
        exact ⟨(pseudo_dvd_step f hz h1 ha hs hm p q hq d hdq).mp hdr, hdq⟩
      · rintro ⟨hdp, hdq⟩
        exact ⟨hdq, (pseudo_dvd_step f hz h1 ha hs hm p q hq d hdq).mpr hdp⟩

/-- Plain pseudo-gcd agrees with field gcd up to a nonzero scalar, including zero inputs. -/
theorem interpret_pseudoGcd (p q : DensePoly E) :
    Associated (interpret f hz (pseudoGcd p q))
      (EuclideanDomain.gcd (interpret f hz p) (interpret f hz q)) := by
  apply associated_of_dvd_dvd
  · have h := (dvd_pseudoGcd f hz h1 ha hs hm p q _).mp (dvd_refl _)
    exact EuclideanDomain.dvd_gcd h.1 h.2
  · exact (dvd_pseudoGcd f hz h1 ha hs hm p q _).mpr
      ⟨EuclideanDomain.gcd_dvd_left _ _, EuclideanDomain.gcd_dvd_right _ _⟩

/-- Correcting a negative multiplier negates the quotient and remainder too. -/
theorem positive_reconstruct [Neg E] (hn : ∀ a, f (-a) = -f a)
    (sign : E → Int) (p q : DensePoly E) :
    Polynomial.C (f (positivePseudoDiv sign p q).multiplier) * interpret f hz p =
      interpret f hz (positivePseudoDiv sign p q).quotient * interpret f hz q +
        interpret f hz (positivePseudoDiv sign p q).remainder := by
  simp only [positivePseudoDiv]
  split
  · simp only [hn, Polynomial.C_neg, neg_mul, interpret_neg f hz hs, ← neg_add]
    exact congrArg Neg.neg (pseudo_reconstruct f hz h1 ha hs hm p q)
  · exact pseudo_reconstruct f hz h1 ha hs hm p q

omit h1 ha hm in
/-- Sign correction preserves the strict interpreted remainder-degree bound. -/
theorem positive_remainder_degree [Neg E] (sign : E → Int)
    (p q : DensePoly E) (hq : q ≠ 0) :
    interpret f hz (positivePseudoDiv sign p q).remainder = 0 ∨
      (interpret f hz (positivePseudoDiv sign p q).remainder).natDegree <
        (interpret f hz q).natDegree := by
  simp only [positivePseudoDiv]
  split
  · simpa only [interpret_neg f hz hs, neg_eq_zero, Polynomial.natDegree_neg] using
      pseudo_remainder_degree f hz p q hq
  · exact pseudo_remainder_degree f hz p q hq

/-- The signed variant returns a strictly positive interpreted multiplier. -/
theorem positive_multiplier [Neg E] [LinearOrder K] [IsStrictOrderedRing K]
    (hn : ∀ a, f (-a) = -f a) (sign : E → Int)
    (hsign : ∀ a, sign a < 0 ↔ f a < 0) (p q : DensePoly E) (hq : q ≠ 0) :
    0 < f (positivePseudoDiv sign p q).multiplier := by
  have htest : (pseudoExponent p q % 2 = 1 ∧ sign q.leadingCoeff < 0) ↔
      f (pseudoDiv p q).multiplier < 0 := by
    rw [pseudo_multiplier f hz h1 ha hs hm]
    constructor
    · rintro ⟨hodd, hneg⟩
      exact (Nat.odd_iff.mpr hodd).pow_neg ((hsign _).mp hneg)
    · intro hu
      have hodd : Odd (pseudoExponent p q) := by
        rcases Nat.even_or_odd (pseudoExponent p q) with heven | hodd
        · exact False.elim ((not_lt_of_ge (heven.pow_nonneg _)) hu)
        · exact hodd
      exact ⟨Nat.odd_iff.mp hodd, (hsign _).mpr (hodd.pow_neg_iff.mp hu)⟩
  simp only [positivePseudoDiv]
  split
  · rename_i h
    simpa only [hn] using neg_pos.mpr (htest.mp h)
  · rename_i h
    have hle : 0 ≤ f (pseudoDiv p q).multiplier := not_lt.mp (fun hneg => h (htest.mpr hneg))
    exact lt_of_le_of_ne hle (Ne.symm (pseudo_multiplier_ne_zero f hz h1 ha hs hm p q hq))

end HexPolyMathlib.Interpret
