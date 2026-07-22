/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import Mathlib

public section

/-!
# Parity of Descartes sign variations

Mathlib's `Polynomial.roots_countP_pos_le_signVariations` is the inequality half of
Descartes' rule of signs: a real polynomial has at most as many positive roots (with
multiplicity) as it has sign variations. This file proves the companion **parity**
statement

`Polynomial.signVariations_parity`:
  `P.roots.countP (0 < ·) ≡ P.signVariations [MOD 2]`

for a nonzero real polynomial. Both quantities are congruent modulo two to the same
"end-sign indicator" `if sign P.leadingCoeff = sign P.trailingCoeff then 0 else 1`:

* `signVariations_modTwo` handles the sign-variation side by induction over `eraseLead`,
  using `signVariations_eq_eraseLead_add_ite` and the fact that `eraseLead` leaves the
  trailing coefficient unchanged (`trailingCoeff_eraseLead`).
* `countP_pos_modTwo` handles the root side by reducing to a monic polynomial and peeling
  monic real factors of degree one or two
  (`IsMonicOfDegree.eq_isMonicOfDegree_one_or_two_mul`); a degree-two factor with no real
  root is positive at `0` by a discriminant argument.

The two exported consequences `countP_pos_eq_zero_of_signVariations_eq_zero` and
`countP_pos_eq_one_of_signVariations_eq_one` combine the parity with the Mathlib
inequality to pin the number of positive roots exactly when there are zero or one sign
variations.

Everything here is `Hex`-free and stated over `ℝ`; it is intended to be upstreamable to
Mathlib alongside `Polynomial.roots_countP_pos_le_signVariations`.
-/

namespace Polynomial

open scoped Classical in
private lemma sign_ne_zero' {x : ℝ} (hx : x ≠ 0) : SignType.sign x ≠ 0 := by
  rw [Ne, sign_eq_zero_iff]; exact hx

/-- Modulo two, a sign change count telescopes: if `a`, `b`, `c` are nonzero signs then
`[b ≠ c] + [a = -b] ≡ [a ≠ c]`. -/
private lemma sign_modTwo_add {a b c : SignType} (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) :
    ((if b = c then 0 else 1) + if a = -b then 1 else 0) ≡ (if a = c then 0 else 1) [MOD 2] := by
  fin_cases a <;> fin_cases b <;> fin_cases c <;> simp_all [Nat.ModEq]

/-- Modulo two, the indicator of a product of nonzero signs is the sum of the indicators. -/
private lemma sign_modTwo_mul {a b : SignType} (ha : a ≠ 0) (hb : b ≠ 0) :
    ((if a = 1 then 0 else 1) + if b = 1 then 0 else 1) ≡ (if a * b = 1 then 0 else 1) [MOD 2] := by
  fin_cases a <;> fin_cases b <;> simp_all [Nat.ModEq]

private lemma sign_ite_mul {a b : SignType} (ha : a ≠ 0) (hb : b ≠ 0) :
    (if a * b = 1 then (0 : ℕ) else 1) = if a = b then 0 else 1 := by
  fin_cases a <;> fin_cases b <;> simp_all

/-- `eraseLead` only removes the top coefficient, so it leaves the trailing coefficient
unchanged (as long as it does not empty the polynomial). -/
theorem trailingCoeff_eraseLead {P : ℝ[X]} (h : P.eraseLead ≠ 0) :
    P.eraseLead.trailingCoeff = P.trailingCoeff := by
  have hP : P ≠ 0 := fun h0 => h (by rw [h0, eraseLead_zero])
  have hlt : P.natTrailingDegree < P.natDegree := by
    rcases (natTrailingDegree_le_natDegree P).lt_or_eq with h' | h'
    · exact h'
    · refine absurd ?_ h
      ext k
      rw [eraseLead_coeff, coeff_zero]
      split
      · rfl
      · rename_i hk
        rcases lt_or_gt_of_ne hk with hk1 | hk1
        · exact coeff_eq_zero_of_lt_natTrailingDegree (by rw [h']; exact hk1)
        · exact coeff_eq_zero_of_natDegree_lt hk1
  have key : P.eraseLead.natTrailingDegree = P.natTrailingDegree := by
    refine le_antisymm ?_ ?_
    · refine natTrailingDegree_le_of_ne_zero ?_
      rw [eraseLead_coeff_of_ne _ hlt.ne]
      exact coeff_natTrailingDegree_ne_zero.mpr hP
    · refine le_natTrailingDegree h (fun m hm => ?_)
      rw [eraseLead_coeff_of_ne _ (by omega)]
      exact coeff_eq_zero_of_lt_natTrailingDegree hm
  rw [trailingCoeff, trailingCoeff, key, eraseLead_coeff_of_ne _ hlt.ne]

/-- The root-count parity indicator is multiplicative: knowing it for two nonzero factors
gives it for the product. -/
private lemma combine_mul {f₁ f₂ : ℝ[X]} (h1 : f₁ ≠ 0) (h2 : f₂ ≠ 0)
    (e1 : f₁.roots.countP (0 < ·) ≡ (if SignType.sign f₁.trailingCoeff = 1 then 0 else 1) [MOD 2])
    (e2 : f₂.roots.countP (0 < ·) ≡ (if SignType.sign f₂.trailingCoeff = 1 then 0 else 1) [MOD 2]) :
    (f₁ * f₂).roots.countP (0 < ·) ≡
      (if SignType.sign (f₁ * f₂).trailingCoeff = 1 then 0 else 1) [MOD 2] := by
  rw [roots_mul (mul_ne_zero h1 h2), Multiset.countP_add, trailingCoeff_mul, sign_mul]
  refine (Nat.ModEq.add e1 e2).trans (sign_modTwo_mul ?_ ?_)
  · exact sign_ne_zero' (trailingCoeff_nonzero_iff_nonzero.mpr h1)
  · exact sign_ne_zero' (trailingCoeff_nonzero_iff_nonzero.mpr h2)

/-- Base leaf: a monic degree-one real polynomial. -/
private lemma countP_deg_one {f : ℝ[X]} (hf : IsMonicOfDegree f 1) :
    f.roots.countP (0 < ·) ≡ (if SignType.sign f.trailingCoeff = 1 then 0 else 1) [MOD 2] := by
  have hfeq : f = X + C (f.coeff 0) := hf.monic.eq_X_add_C hf.natDegree_eq
  set b := f.coeff 0 with hb
  rw [hfeq, roots_X_add_C]
  by_cases hbz : b = 0
  · rw [hbz, map_zero, add_zero, neg_zero,
      show (X : ℝ[X]).trailingCoeff = 1 from by rw [trailingCoeff, natTrailingDegree_X,
      coeff_X_one]]
    rw [← Multiset.cons_zero, Multiset.countP_cons, Multiset.countP_zero, zero_add]
    simp [Nat.ModEq]
  · have htc : (X + C b).trailingCoeff = b := by
      have hcoeff : (X + C b).coeff 0 = b := by
        rw [coeff_add, coeff_X_zero, coeff_C_zero, zero_add]
      have hne : (X + C b).coeff 0 ≠ 0 := by rw [hcoeff]; exact hbz
      rw [trailingCoeff_eq_coeff_zero hne, hcoeff]
    rw [htc, ← Multiset.cons_zero, Multiset.countP_cons, Multiset.countP_zero, zero_add]
    rcases lt_or_gt_of_ne hbz with h | h
    · rw [if_pos (show (0 : ℝ) < -b by linarith), sign_neg h, if_neg (by decide)]
    · rw [if_neg (show ¬ (0 : ℝ) < -b by linarith), sign_pos h, if_pos rfl]

/-- A monic degree-two real polynomial with no real root has a positive trailing (constant)
coefficient. -/
private lemma trailingCoeff_pos_of_no_root {f : ℝ[X]} (hf : IsMonicOfDegree f 2)
    (hroot : ∀ x, ¬ f.IsRoot x) : 0 < f.trailingCoeff := by
  have hdeg : f.degree ≤ 2 := natDegree_le_iff_degree_le.mp hf.natDegree_eq.le
  have hc2 : f.coeff 2 = 1 := by
    have h := hf.monic.coeff_natDegree; rwa [hf.natDegree_eq] at h
  have hfq : f = C (f.coeff 2) * X ^ 2 + C (f.coeff 1) * X + C (f.coeff 0) :=
    eq_quadratic_of_degree_le_two hdeg
  set b := f.coeff 1 with hb
  set c := f.coeff 0 with hcc
  have heval : ∀ x, f.eval x = x * x + b * x + c := by
    intro x
    rw [hfq, hc2]
    simp only [eval_add, eval_mul, eval_pow, eval_X, eval_C, one_mul]
    ring
  have hdisc : discrim 1 b c < 0 := by
    by_contra hcon
    rw [not_lt] at hcon
    obtain ⟨x, hx⟩ := exists_quadratic_eq_zero one_ne_zero
      ⟨Real.sqrt (discrim 1 b c), (Real.mul_self_sqrt hcon).symm⟩
    exact hroot x (by rw [IsRoot, heval]; linarith)
  have hcpos : 0 < c := by
    rw [discrim] at hdisc
    nlinarith [sq_nonneg b]
  rw [trailingCoeff_eq_coeff_zero (by rw [← hcc]; exact hcpos.ne'), ← hcc]
  exact hcpos

/-- Leaf: a monic degree-two real polynomial. -/
private lemma countP_deg_two {f : ℝ[X]} (hf : IsMonicOfDegree f 2) :
    f.roots.countP (0 < ·) ≡ (if SignType.sign f.trailingCoeff = 1 then 0 else 1) [MOD 2] := by
  by_cases hroot : ∃ x, f.IsRoot x
  · obtain ⟨x, hx⟩ := hroot
    obtain ⟨g, hg⟩ := dvd_iff_isRoot.mpr hx
    have hXm : IsMonicOfDegree (X - C x) 1 := ⟨natDegree_X_sub_C x, monic_X_sub_C x⟩
    have hgm : IsMonicOfDegree g 1 := hXm.of_mul_left (hg ▸ hf)
    rw [hg]
    exact combine_mul (X_sub_C_ne_zero x) hgm.monic.ne_zero
      (countP_deg_one hXm) (countP_deg_one hgm)
  · rw [not_exists] at hroot
    have hroots : f.roots = 0 := by
      rw [Multiset.eq_zero_iff_forall_notMem]
      exact fun x hx => hroot x (isRoot_of_mem_roots hx)
    rw [hroots, Multiset.countP_zero,
      if_pos (sign_pos (trailingCoeff_pos_of_no_root hf hroot))]

/-- Core (monic case): the number of positive roots of a monic real polynomial is congruent
modulo two to the indicator of its trailing coefficient's sign. -/
theorem countP_pos_modTwo_monic {n : ℕ} {Q : ℝ[X]} (hQ : IsMonicOfDegree Q n) :
    Q.roots.countP (0 < ·) ≡ (if SignType.sign Q.trailingCoeff = 1 then 0 else 1) [MOD 2] := by
  induction n using Nat.strong_induction_on generalizing Q with
  | _ n ih =>
    rcases n with _ | m
    · rw [isMonicOfDegree_zero_iff] at hQ
      subst hQ
      have htc1 : (1 : ℝ[X]).trailingCoeff = 1 := by
        rw [trailingCoeff_eq_coeff_zero (by rw [coeff_one_zero]; exact one_ne_zero), coeff_one_zero]
      rw [roots_one, htc1, sign_one]
      simp [Nat.ModEq]
    · obtain ⟨f₁, f₂, h12, hmul⟩ := hQ.eq_isMonicOfDegree_one_or_two_mul
      rcases h12 with h1 | h2
      · have hf2 : IsMonicOfDegree f₂ m := by
          have hQ' : IsMonicOfDegree (f₁ * f₂) (1 + m) := by
            rw [← hmul, Nat.add_comm 1 m]; exact hQ
          exact h1.of_mul_left hQ'
        have e2 := ih m (Nat.lt_succ_self m) hf2
        subst hmul
        exact combine_mul h1.monic.ne_zero hf2.monic.ne_zero (countP_deg_one h1) e2
      · have hm1 : 1 ≤ m := by
          have hdvd : f₁ ∣ Q := ⟨f₂, hmul⟩
          have hle := natDegree_le_of_dvd hdvd hQ.monic.ne_zero
          rw [h2.natDegree_eq, hQ.natDegree_eq] at hle
          omega
        have hf2 : IsMonicOfDegree f₂ (m - 1) := by
          have hQ' : IsMonicOfDegree (f₁ * f₂) (2 + (m - 1)) := by
            rw [← hmul, show 2 + (m - 1) = m + 1 from by omega]; exact hQ
          exact h2.of_mul_left hQ'
        have e2 := ih (m - 1) (by omega) hf2
        subst hmul
        exact combine_mul h2.monic.ne_zero hf2.monic.ne_zero (countP_deg_two h2) e2

/-- The number of positive roots of a nonzero real polynomial is congruent modulo two to the
end-sign indicator `[sign leadingCoeff ≠ sign trailingCoeff]`. -/
theorem countP_pos_modTwo {P : ℝ[X]} (hP : P ≠ 0) :
    P.roots.countP (0 < ·) ≡
      (if SignType.sign P.leadingCoeff = SignType.sign P.trailingCoeff then 0 else 1) [MOD 2] := by
  have hlc : P.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hP
  set u := (P.leadingCoeff)⁻¹ with hu
  have hune : u ≠ 0 := inv_ne_zero hlc
  have hmonic : (C u * P).Monic :=
    monic_C_mul_of_mul_leadingCoeff_eq_one (by rw [hu, inv_mul_cancel₀ hlc])
  have core := countP_pos_modTwo_monic (n := (C u * P).natDegree) ⟨rfl, hmonic⟩
  rw [roots_C_mul _ hune] at core
  have htcC : (C u).trailingCoeff = u := by
    rw [trailingCoeff_eq_coeff_zero (by rw [coeff_C_zero]; exact hune), coeff_C_zero]
  have hsu : SignType.sign u = SignType.sign P.leadingCoeff := by
    rcases lt_or_gt_of_ne hlc with h | h
    · rw [hu, sign_neg (inv_lt_zero.mpr h), sign_neg h]
    · rw [hu, sign_pos (inv_pos.mpr h), sign_pos h]
  have hsign : SignType.sign (C u * P).trailingCoeff
      = SignType.sign P.leadingCoeff * SignType.sign P.trailingCoeff := by
    rw [trailingCoeff_mul, sign_mul, htcC, hsu]
  rw [hsign, sign_ite_mul (sign_ne_zero' hlc)
    (sign_ne_zero' (trailingCoeff_nonzero_iff_nonzero.mpr hP))] at core
  exact core

/-- The number of sign variations of a nonzero real polynomial is congruent modulo two to the
end-sign indicator `[sign leadingCoeff ≠ sign trailingCoeff]`. -/
theorem signVariations_modTwo {P : ℝ[X]} (hP : P ≠ 0) :
    P.signVariations ≡
      (if SignType.sign P.leadingCoeff = SignType.sign P.trailingCoeff then 0 else 1) [MOD 2] := by
  generalize hd : P.natDegree = d
  induction d using Nat.strong_induction_on generalizing P with
  | _ d ih =>
    have hslc : SignType.sign P.leadingCoeff ≠ 0 := sign_ne_zero' (leadingCoeff_ne_zero.mpr hP)
    have hstc : SignType.sign P.trailingCoeff ≠ 0 :=
      sign_ne_zero' (trailingCoeff_nonzero_iff_nonzero.mpr hP)
    rw [signVariations_eq_eraseLead_add_ite hP]
    by_cases he : P.eraseLead = 0
    · have hnt : P.natTrailingDegree = P.natDegree := by
        refine le_antisymm (natTrailingDegree_le_natDegree P) (le_natTrailingDegree hP ?_)
        intro m hm
        have hmc : P.eraseLead.coeff m = P.coeff m := eraseLead_coeff_of_ne m (by omega)
        rw [← hmc, he, coeff_zero]
      have hlctc : P.trailingCoeff = P.leadingCoeff := by
        simp only [trailingCoeff, leadingCoeff, hnt]
      rw [he, signVariations_zero, leadingCoeff_zero, sign_zero, neg_zero, if_neg hslc, hlctc,
        if_pos rfl]
    · have hltd : P.eraseLead.natDegree < d := by
        rw [← hd]
        rcases eraseLead_natDegree_lt_or_eraseLead_eq_zero P with h' | h'
        · exact h'
        · exact absurd h' he
      have hb : SignType.sign P.eraseLead.leadingCoeff ≠ 0 :=
        sign_ne_zero' (leadingCoeff_ne_zero.mpr he)
      have IHe := ih P.eraseLead.natDegree hltd he rfl
      rw [trailingCoeff_eraseLead he] at IHe
      exact (Nat.ModEq.add_right _ IHe).trans (sign_modTwo_add hslc hb hstc)

/-- **Descartes parity.** For a nonzero real polynomial the number of positive roots (with
multiplicity) and the number of sign variations of the coefficients have the same parity. -/
theorem signVariations_parity (P : ℝ[X]) (hP : P ≠ 0) :
    P.roots.countP (0 < ·) ≡ P.signVariations [MOD 2] :=
  (countP_pos_modTwo hP).trans (signVariations_modTwo hP).symm

set_option linter.unusedVariables false in
/-- No sign variations forces no positive roots. -/
theorem countP_pos_eq_zero_of_signVariations_eq_zero {P : ℝ[X]} (hP : P ≠ 0)
    (h : P.signVariations = 0) : P.roots.countP (0 < ·) = 0 :=
  Nat.le_zero.mp (h ▸ roots_countP_pos_le_signVariations P)

/-- Exactly one sign variation forces exactly one positive root. -/
theorem countP_pos_eq_one_of_signVariations_eq_one {P : ℝ[X]} (hP : P ≠ 0)
    (h : P.signVariations = 1) : P.roots.countP (0 < ·) = 1 := by
  have hle : P.roots.countP (0 < ·) ≤ 1 := h ▸ roots_countP_pos_le_signVariations P
  have hpar := signVariations_parity P hP
  rw [h] at hpar
  rcases Nat.eq_zero_or_pos (P.roots.countP (0 < ·)) with h0 | hpos
  · rw [h0] at hpar; exact absurd hpar (by decide)
  · omega

/-- Sanity check: the parity theorem applies to `X² - 1` (whose positive-root count `1` and
sign-variation count `1` are indeed congruent mod two). -/
example : (X ^ 2 - C 1 : ℝ[X]).roots.countP (0 < ·) ≡ (X ^ 2 - C 1 : ℝ[X]).signVariations [MOD 2] :=
  signVariations_parity _ (by
    intro h
    have := congrArg (fun p => Polynomial.coeff p 2) h
    simp [coeff_sub, coeff_X_pow, coeff_one] at this)

end Polynomial
