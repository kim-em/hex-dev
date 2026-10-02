/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module
public import HexNumberField.Radical
public import HexNumberFieldMathlib.Conjugate
public import HexNumberFieldMathlib.Branch
public import HexNumberFieldMathlib.Unity
public import HexNumberFieldMathlib.Order
public import HexNumberFieldMathlib.Polynomial
public import HexNumberFieldMathlib.AlgebraicRoots
public import HexNumberFieldMathlib.PrincipalRoot
public import Mathlib.Analysis.RCLike.Sqrt
public section

/-! The executable radicals select Mathlib's principal complex branches. -/
namespace Hex.AlgebraicNumber.Radical

/-- The root solver receives exactly `X^n - a`. -/
theorem polynomial_value (a : AlgebraicNumber) {n : Nat} (hn : n ≠ 0) :
    (polynomial a n).toPolynomial = Polynomial.X ^ n - Polynomial.C a.toComplex := by
  apply Polynomial.ext
  intro k
  rw [polynomial, AlgebraicPoly.coeff_ofArray, Array.getD_eq_getD_getElem?,
    Array.getElem?_ofFn]
  split
  · rename_i hk
    by_cases hk0 : k = 0
    · subst k
      simp [hn, Ne.symm hn, neg_toComplex, Polynomial.coeff_C]
    · by_cases hkn : k = n
      · subst k
        simp [hn, Ne.symm hn, neg_toComplex, Polynomial.coeff_C]
      · simp [hk0, hkn, Polynomial.coeff_X_pow, Polynomial.coeff_C]
  · rename_i hk
    have hk0 : k ≠ 0 := by omega
    have hkn : k ≠ n := by omega
    simp [hk0, hkn, Polynomial.coeff_X_pow, Polynomial.coeff_C]

/-- Selection succeeds and returns the principal complex root. -/
theorem select_value (a : AlgebraicNumber) {n : Nat} (hn : n ≠ 0) :
    ∃ c, select (polynomial a n).roots.toArray = some c ∧
      c.value.toComplex = a.toComplex ^ ((n : ℂ)⁻¹) := by
  let f := polynomial a n
  have hf : f.toPolynomial = Polynomial.X ^ n - Polynomial.C a.toComplex :=
    polynomial_value a hn
  have hcontains (z : ℂ) : RootSet.Contains f.roots z ↔ z ^ n = a.toComplex := by
    rw [AlgebraicPoly.contains_roots_iff, hf]
    simp only [Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X,
      Polynomial.eval_C, sub_eq_zero]
  cases hr : f.roots with
  | all =>
    have hz := (AlgebraicPoly.roots_all_iff f).mp hr
    exact (Polynomial.X_pow_sub_C_ne_zero (Nat.pos_of_ne_zero hn) a.toComplex
      (hf.symm.trans hz)).elim
  | finite roots =>
    have hm := (hcontains (a.toComplex ^ ((n : ℂ)⁻¹))).mpr
      (Complex.cpow_nat_inv_pow a.toComplex hn)
    rw [hr] at hm
    obtain ⟨r, hrmem, _⟩ := hm
    have hne : roots.toList ≠ [] := fun h => by simpa [h] using hrmem
    obtain ⟨c, hc, ⟨s, hs, hcs⟩, hdom⟩ := select_spec roots hne
    refine ⟨c, ?_, ?_⟩
    · simpa only [RootSet.toArray, RootSet.finite?, Option.getD_some] using hc
    · have hvalue (r : RootCount) : (candidate r).value.toComplex = r.root.toComplex :=
        AlgebraicRoot.exact_toComplex r.root
      have hw : c.value.toComplex ^ n = a.toComplex := by
        apply (hcontains _).mp
        rw [hr, hcs, hvalue]
        exact ⟨s, hs, rfl⟩
      apply HexNumberFieldMathlib.PrincipalRoot.eq_of_max hn hw
      · intro v hv
        have hm := (hcontains v).mpr hv
        rw [hr] at hm
        obtain ⟨r, hrmem, hrv⟩ := hm
        have hd := (hdom r hrmem).1
        rwa [hvalue, hrv] at hd
      · intro v hv hre him
        have hm := (hcontains v).mpr hv
        rw [hr] at hm
        obtain ⟨r, hrmem, hrv⟩ := hm
        have hd := (hdom r hrmem).2 (by rwa [hvalue, hrv])
        apply (rank_nonneg _).mp
        apply le_trans _ hd
        apply (rank_nonneg _).mpr
        rwa [hvalue, hrv]

/-- The lazy branch selector returns the same principal value as the exact reference. -/
theorem fast?_value (a : AlgebraicNumber) {n : Nat} (hn : 1 < n) (ha : a.toComplex ≠ 0)
    {out : AlgebraicRoot} (h : fast? a (polynomial a n).roots.toArray = some out) :
    out.toComplex = a.toComplex ^ ((n : ℂ)⁻¹) := by
  have hn0 : n ≠ 0 := by omega
  let f := polynomial a n
  have hf : f.toPolynomial = Polynomial.X ^ n - Polynomial.C a.toComplex :=
    polynomial_value a hn0
  have hcontains (z : ℂ) : RootSet.Contains f.roots z ↔ z ^ n = a.toComplex := by
    rw [AlgebraicPoly.contains_roots_iff, hf]
    simp only [Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X,
      Polynomial.eval_C, sub_eq_zero]
  cases hr : f.roots with
  | all =>
    have hz := (AlgebraicPoly.roots_all_iff f).mp hr
    exact (Polynomial.X_pow_sub_C_ne_zero (Nat.pos_of_ne_zero hn0) a.toComplex
      (hf.symm.trans hz)).elim
  | finite roots =>
    have hp := (hcontains (a.toComplex ^ ((n : ℂ)⁻¹))).mpr
      (Complex.cpow_nat_inv_pow a.toComplex hn0)
    rw [hr] at hp
    have hall (r : RootCount) (hm : r ∈ roots.toList) : r.root.toComplex ^ n = a.toComplex := by
      apply (hcontains _).mp
      rw [hr]
      exact ⟨r, hm, rfl⟩
    have hh : fast? a roots = some out := by
      change fast? a f.roots.toArray = some out at h
      simpa only [hr, RootSet.toArray, RootSet.finite?, Option.getD_some] using h
    exact fast?_sound a hn ha roots hall hp hh

end Hex.AlgebraicNumber.Radical


namespace Hex.AlgebraicNumber

/-- The executable nth root agrees with Mathlib's principal complex power. -/
@[simp] theorem nthRoot_toComplex (a : AlgebraicNumber) (n : Nat) :
    (a.nthRoot n).toComplex = a.toComplex ^ ((n : ℂ)⁻¹) := by
  by_cases hn : n = 0
  · subst n
    simp
  by_cases hn1 : n = 1
  · subst n
    simp
  by_cases ha : a.isZero = true
  · have hz := (isZero_iff a).mp ha
    simp [nthRoot, hn, hn1, ha, hz]
  by_cases ha1 : a == 1
  · have he := (beq_iff a 1).mp ha1
    simp [nthRoot, hn, hn1, ha, ha1, he]
  by_cases hm : a == -1
  · have he := (beq_iff a (-1)).mp hm
    simp only [nthRoot, ite_eq_right hn, ite_eq_right hn1, ite_eq_right ha, ite_eq_right ha1, ite_eq_left hm]
    rw [rootOfUnity_toComplex, he, neg_toComplex, one_toComplex,
      Complex.cpow_def_of_ne_zero (by norm_num), Complex.log_neg_one]
    congr 1
    push_cast
    ring
  by_cases hi : a == I
  · have he := (beq_iff a I).mp hi
    simp only [nthRoot, ite_eq_right hn, ite_eq_right hn1, ite_eq_right ha, ite_eq_right ha1, ite_eq_right hm, ite_eq_left hi]
    rw [rootOfUnity_toComplex, he, I_toComplex,
      Complex.cpow_def_of_ne_zero Complex.I_ne_zero, Complex.log_I]
    congr 1
    push_cast
    ring
  by_cases hni : a == -I
  · have he := (beq_iff a (-I)).mp hni
    simp only [nthRoot, ite_eq_right hn, ite_eq_right hn1, ite_eq_right ha, ite_eq_right ha1, ite_eq_right hm,
      ite_eq_right hi, ite_eq_left hni]
    rw [rootOfUnity_toComplex, he, neg_toComplex, I_toComplex,
      Complex.cpow_def_of_ne_zero (neg_ne_zero.mpr Complex.I_ne_zero), Complex.log_neg_I]
    congr 1
    push_cast
    ring
  simp only [nthRoot, ite_eq_right hn, ite_eq_right hn1, ite_eq_right ha, ite_eq_right ha1, ite_eq_right hm,
    ite_eq_right hi, ite_eq_right hni]
  split
  · rename_i r hr
    rw [AlgebraicRoot.exact_toComplex]
    exact Radical.fast?_value a (by omega) (fun hz => ha ((isZero_iff a).mpr hz)) hr
  · obtain ⟨c, hc, hv⟩ := Radical.select_value a hn
    rw [hc]
    exact hv

/-- Every positive-index radical is a root of the expected equation. -/
@[simp] theorem nthRoot_pow (a : AlgebraicNumber) {n : Nat} (hn : n ≠ 0) :
    a.nthRoot n ^ n = a := by
  apply toComplex_injective
  change toComplexHom (a.nthRoot n ^ n) = a.toComplex
  rw [map_pow]
  exact (congrArg (· ^ n) (nthRoot_toComplex a n)).trans (Complex.cpow_nat_inv_pow _ hn)

/-- The executable square root uses Mathlib's principal branch. -/
@[simp] theorem sqrt_toComplex (a : AlgebraicNumber) :
    a.sqrt.toComplex = a.toComplex.sqrt := by
  simp [sqrt, Complex.sqrt]

@[simp] theorem sqrt_sq (a : AlgebraicNumber) : a.sqrt ^ 2 = a := nthRoot_pow a (by decide)

/-- Conjugation commutes with the principal radical away from the negative-real branch cut. -/
theorem nthRoot_conj (a : AlgebraicNumber) (n : Nat) (ha : a.toComplex.arg ≠ Real.pi) :
    a.conj.nthRoot n = (a.nthRoot n).conj := by
  apply toComplex_injective
  simp only [nthRoot_toComplex, conj_toComplex]
  simpa using Complex.conj_cpow a.toComplex ((n : ℂ)⁻¹) ha

/-- A decidable branch-cut condition for conjugating principal radicals. -/
theorem nthRoot_conj_of_not_lt (a : AlgebraicNumber) (n : Nat) (ha : ¬ a < 0) :
    a.conj.nthRoot n = (a.nthRoot n).conj := by
  apply nthRoot_conj a n
  intro harg
  apply ha
  rw [lt_iff, zero_toComplex]
  simpa only [Complex.zero_re, Complex.zero_im] using Complex.arg_eq_pi_iff.mp harg

/-- info: 'Hex.AlgebraicNumber.nthRoot_toComplex' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms nthRoot_toComplex

end Hex.AlgebraicNumber
