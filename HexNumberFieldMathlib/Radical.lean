/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module
public import HexNumberField.Radical
public import HexNumberFieldMathlib.Conjugate
public import HexNumberFieldMathlib.Polynomial
public import HexNumberFieldMathlib.AlgebraicRoots
public import HexNumberFieldMathlib.PrincipalRoot
public import Mathlib.Analysis.RCLike.Sqrt
public section

/-! The executable radicals select Mathlib's principal complex branches. -/
namespace Hex.AlgebraicNumber.Radical

private theorem rank_nonneg (a : AlgebraicNumber) :
    0 ≤ rank a ↔ 0 ≤ a.toComplex.im := by
  have h := a.isolation.sign
  change match a.side with
    | .real => a.toComplex.im = 0
    | .upper => 0 < a.toComplex.im
    | .lower => a.toComplex.im < 0 at h
  unfold rank
  cases hs : a.side <;> simp_all <;> linarith

private theorem twiceRe_value (a : Candidate) :
    a.twiceRe.toComplex = ((2 * a.value.toComplex.re : ℝ) : ℂ) := by
  rw [a.correct, add_toComplex, conj_toComplex, Complex.add_conj]

private theorem compare_value (a b : Candidate) :
    realCompare a.twiceRe b.twiceRe =
      compare (2 * a.value.toComplex.re) (2 * b.value.toComplex.re) := by
  rw [realCompare_eq _ _ ((isReal_iff _).mpr (by rw [twiceRe_value]; rfl))
    ((isReal_iff _).mpr (by rw [twiceRe_value]; rfl)), twiceRe_value, twiceRe_value]
  rfl

private def Dominates (a b : Candidate) : Prop :=
  b.value.toComplex.re ≤ a.value.toComplex.re ∧
    (b.value.toComplex.re = a.value.toComplex.re → rank b.value ≤ rank a.value)

private theorem dominates_refl (a : Candidate) : Dominates a a := ⟨le_rfl, fun _ => le_rfl⟩

private theorem dominates_trans {a b c : Candidate}
    (hab : Dominates a b) (hbc : Dominates b c) : Dominates a c := by
  refine ⟨hbc.1.trans hab.1, fun h => ?_⟩
  have hb : b.value.toComplex.re = a.value.toComplex.re := by linarith [hab.1, hbc.1]
  exact (hbc.2 (h.trans hb.symm)).trans (hab.2 hb)

private theorem choose_spec (a b : Candidate) :
    (choose a b = a ∨ choose a b = b) ∧
      Dominates (choose a b) a ∧ Dominates (choose a b) b := by
  have hc := compare_value a b
  unfold choose
  cases h : realCompare a.twiceRe b.twiceRe with
  | lt =>
    have hr := compare_lt_iff_lt.mp (h.symm.trans hc).symm
    exact ⟨Or.inr rfl, ⟨by linarith, fun he => by linarith⟩, dominates_refl b⟩
  | gt =>
    have hr := compare_gt_iff_gt.mp (h.symm.trans hc).symm
    exact ⟨Or.inl rfl, dominates_refl a, ⟨by linarith, fun he => by linarith⟩⟩
  | eq =>
    have hr := compare_eq_iff_eq.mp (h.symm.trans hc).symm
    simp only
    split
    · rename_i hk
      exact ⟨Or.inr rfl, ⟨by linarith, fun _ => hk.le⟩, dominates_refl b⟩
    · rename_i hk
      exact ⟨Or.inl rfl, dominates_refl a, ⟨by linarith, fun _ => le_of_not_gt hk⟩⟩

private theorem fold_spec (rs : List RootCount) (a : Candidate) :
    let b := rs.foldl (fun best root => choose best (candidate root)) a
    (b = a ∨ ∃ r ∈ rs, b = candidate r) ∧
      Dominates b a ∧ ∀ r ∈ rs, Dominates b (candidate r) := by
  induction rs generalizing a with
  | nil => exact ⟨Or.inl rfl, dominates_refl a, by simp⟩
  | cons r rs ih =>
    obtain ⟨hm, ha, hall⟩ := ih (choose a (candidate r))
    obtain ⟨hc, hca, hcr⟩ := choose_spec a (candidate r)
    refine ⟨?_, dominates_trans ha hca, ?_⟩
    · rcases hm with hm | ⟨s, hs, hm⟩
      · rcases hc with hc | hc
        · exact Or.inl (hm.trans hc)
        · exact Or.inr ⟨r, by simp, hm.trans hc⟩
      · exact Or.inr ⟨s, List.mem_cons_of_mem _ hs, hm⟩
    · intro s hs
      rcases List.mem_cons.mp hs with rfl | hs
      · exact dominates_trans ha hcr
      · exact hall s hs

private theorem select_spec (roots : Array RootCount) (hne : roots.toList ≠ []) :
    ∃ c, select roots = some c ∧ (∃ r ∈ roots.toList, c = candidate r) ∧
      ∀ r ∈ roots.toList, Dominates c (candidate r) := by
  unfold select
  cases h : roots.toList with
  | nil => exact (hne h).elim
  | cons r rs =>
    obtain ⟨hm, ha, hall⟩ := fold_spec rs (candidate r)
    refine ⟨_, rfl, ?_, ?_⟩
    · rcases hm with hm | ⟨s, hs, hm⟩
      · exact ⟨r, by simp, hm⟩
      · exact ⟨s, List.mem_cons_of_mem _ hs, hm⟩
    · intro s hs
      rcases List.mem_cons.mp hs with rfl | hs
      · exact ha
      · exact hall s hs

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
  obtain ⟨c, hc, hv⟩ := Radical.select_value a hn
  simpa only [nthRoot, ite_eq_right hn, ite_eq_right hn1, ite_eq_right ha,
    ite_eq_right ha1, hc, Option.map_some, Option.getD_some] using hv

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

/-- info: 'Hex.AlgebraicNumber.nthRoot_toComplex' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms nthRoot_toComplex

end Hex.AlgebraicNumber
