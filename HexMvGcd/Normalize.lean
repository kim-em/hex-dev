/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexMvGcd.View

@[expose] public section
set_option backward.proofsInPublic true

/-!
Producer-free unit, normalization, and scalar-content operations.

None of these definitions calls the multivariate gcd producer. This is
important because certificate replay needs them before the public
`GcdOps (MvPoly ...)` instance can be assembled.
-/

namespace Hex.MvPoly

universe u

variable {n : Nat} {R : Type u} {cmp : Mono n → Mono n → Ordering}
  [Std.TransCmp cmp] [Std.LawfulEqCmp cmp]
  [Lean.Grind.CommRing R] [DecidableEq R] [BEq R] [LawfulBEq R]
  [Dvd R] [GcdOps R]

/-- The constant unit selected from the leading coefficient, with `1` at
zero. -/
@[reducible] def polyNormUnit [IsMonomialOrder cmp]
    (p : MvPoly n R cmp) : MvPoly n R cmp :=
  match p.termsList.getLast? with
  | none => 1
  | some (_, c) => C (GcdOps.normUnit c)

/-- Canonical associate selected by the unit attached to the leading
coefficient. -/
@[reducible] def polyNormalize [IsMonomialOrder cmp]
    (p : MvPoly n R cmp) : MvPoly n R cmp :=
  p * polyNormUnit p

/-- Recognize exactly a one-term constant polynomial whose coefficient is a
unit in the base ring. -/
@[reducible] def polyIsUnit (p : MvPoly n R cmp) : Bool :=
  match p.termsList with
  | [(m, c)] => decide (m = Mono.zero) && GcdOps.isUnit c
  | _ => false

/-- Normalized gcd fold of the distributed scalar coefficients. The empty
fold is the specified zero content; a nonempty fold starts at the first
coefficient rather than relying on an unstated `gcd 0 a` law. -/
@[reducible] def scalarContent (p : MvPoly n R cmp) : R :=
  match p.termsList with
  | [] => 0
  | (_, c) :: terms =>
      normalize (terms.foldl (fun g term => GcdOps.gcd g term.2) c)

omit [Dvd R] in
/-- The normalization unit at zero is the constant one polynomial. -/
@[simp] theorem polyNormUnit_zero [IsMonomialOrder cmp] :
    polyNormUnit (0 : MvPoly n R cmp) = 1 := by
  rfl

omit [Dvd R] in
/-- Polynomial normalization preserves zero. -/
@[simp] theorem polyNormalize_zero [IsMonomialOrder cmp] :
    polyNormalize (0 : MvPoly n R cmp) = 0 := by
  rw [polyNormalize, polyNormUnit_zero, Lean.Grind.Semiring.zero_mul]

omit [Dvd R] in
/-- Scalar content uses the explicit zero convention. -/
@[simp] theorem scalarContent_zero :
    scalarContent (0 : MvPoly n R cmp) = 0 := by
  rfl

private theorem dvdRefl [LawfulGcdOps R] (a : R) : a ∣ a := by
  apply (LawfulGcdOps.dvd_iff a a).mpr
  exact ⟨1, (Lean.Grind.Semiring.mul_one a).symm⟩

private theorem dvdTrans [LawfulGcdOps R] {a b c : R}
    (hab : a ∣ b) (hbc : b ∣ c) : a ∣ c := by
  rcases (LawfulGcdOps.dvd_iff a b).mp hab with ⟨x, rfl⟩
  rcases (LawfulGcdOps.dvd_iff (a * x) c).mp hbc with ⟨y, rfl⟩
  apply (LawfulGcdOps.dvd_iff a ((a * x) * y)).mpr
  exact ⟨x * y, Lean.Grind.Semiring.mul_assoc a x y⟩

private theorem normalize_dvd [LawfulGcdOps R] (a : R) : normalize a ∣ a := by
  rcases LawfulGcdOps.normUnit_unit a with ⟨u, hu⟩
  apply (LawfulGcdOps.dvd_iff (normalize a) a).mpr
  refine ⟨u, ?_⟩
  calc
    a = a * 1 := (Lean.Grind.Semiring.mul_one a).symm
    _ = a * (GcdOps.normUnit a * u) := by rw [hu]
    _ = normalize a * u := (Lean.Grind.Semiring.mul_assoc ..).symm

private theorem dvd_normalize [LawfulGcdOps R] (a : R) : a ∣ normalize a := by
  apply (LawfulGcdOps.dvd_iff a (normalize a)).mpr
  exact ⟨GcdOps.normUnit a, rfl⟩

private theorem foldGcd_dvd_acc [LawfulGcdOps R]
    (terms : List (Mono n × R)) (acc : R) :
    terms.foldl (fun g term => GcdOps.gcd g term.2) acc ∣ acc := by
  induction terms generalizing acc with
  | nil => exact dvdRefl acc
  | cons term terms ih =>
      exact dvdTrans (ih (GcdOps.gcd acc term.2))
        (LawfulGcdOps.gcd_dvd_left acc term.2)

private theorem foldGcd_dvd_term [LawfulGcdOps R]
    (terms : List (Mono n × R)) (acc : R) {term : Mono n × R}
    (hterm : term ∈ terms) :
    terms.foldl (fun g term => GcdOps.gcd g term.2) acc ∣ term.2 := by
  induction terms generalizing acc with
  | nil => simp at hterm
  | cons head terms ih =>
      rcases List.mem_cons.mp hterm with rfl | hterm
      · exact dvdTrans (foldGcd_dvd_acc terms (GcdOps.gcd acc term.2))
          (LawfulGcdOps.gcd_dvd_right acc term.2)
      · exact ih (GcdOps.gcd acc head.2) hterm

private theorem dvd_foldGcd [LawfulGcdOps R]
    (terms : List (Mono n × R)) (acc d : R)
    (hacc : d ∣ acc) (hterms : ∀ term ∈ terms, d ∣ term.2) :
    d ∣ terms.foldl (fun g term => GcdOps.gcd g term.2) acc := by
  induction terms generalizing acc with
  | nil => exact hacc
  | cons term terms ih =>
      apply ih (GcdOps.gcd acc term.2)
      · exact LawfulGcdOps.dvd_gcd acc term.2 d hacc
          (hterms term (List.mem_cons_self ..))
      · intro tail htail
        exact hterms tail (List.mem_cons_of_mem term htail)

/-- Scalar content divides every coefficient, including the implicit zeros
outside the support. -/
theorem scalarContent_dvd_coeff [LawfulGcdOps R]
    (p : MvPoly n R cmp) (m : Mono n) :
    scalarContent p ∣ coeff m p := by
  cases hterms : p.termsList with
  | nil =>
      have hm : m ∉ p.monomials := by simp [monomials, hterms]
      rw [coeff_eq_zero_of_not_mem m p hm]
      apply (LawfulGcdOps.dvd_iff (scalarContent p) 0).mpr
      exact ⟨0, (Lean.Grind.Semiring.mul_zero _).symm⟩
  | cons head terms =>
      rcases head with ⟨headMono, headCoeff⟩
      by_cases hm : m ∈ p.monomials
      · rcases List.mem_map.mp hm with ⟨term, hterm, hmono⟩
        rcases term with ⟨termMono, termCoeff⟩
        simp only at hmono
        subst termMono
        rw [coeff_eq_of_mem_terms p hterm]
        unfold scalarContent
        rw [hterms]
        simp only
        apply dvdTrans (normalize_dvd _)
        rw [hterms] at hterm
        rcases List.mem_cons.mp hterm with hhead | htail
        · cases hhead
          exact foldGcd_dvd_acc terms headCoeff
        · exact foldGcd_dvd_term terms headCoeff htail
      · rw [coeff_eq_zero_of_not_mem m p hm]
        apply (LawfulGcdOps.dvd_iff (scalarContent p) 0).mpr
        exact ⟨0, (Lean.Grind.Semiring.mul_zero _).symm⟩

/-- Scalar content is divisible by every common scalar divisor of the
coefficients. -/
theorem dvd_scalarContent [LawfulGcdOps R]
    (p : MvPoly n R cmp) (d : R)
    (hd : ∀ m, d ∣ coeff m p) : d ∣ scalarContent p := by
  cases hterms : p.termsList with
  | nil =>
      unfold scalarContent
      rw [hterms]
      apply (LawfulGcdOps.dvd_iff d 0).mpr
      exact ⟨0, (Lean.Grind.Semiring.mul_zero _).symm⟩
  | cons head terms =>
      rcases head with ⟨headMono, headCoeff⟩
      unfold scalarContent
      rw [hterms]
      simp only
      apply dvdTrans _ (dvd_normalize _)
      apply dvd_foldGcd terms headCoeff d
      · have hcoeff : coeff headMono p = headCoeff :=
          coeff_eq_of_mem_terms p (hterms ▸ List.mem_cons_self)
        rw [← hcoeff]
        exact hd headMono
      · intro term hterm
        rcases term with ⟨termMono, termCoeff⟩
        have hcoeff : coeff termMono p = termCoeff :=
          coeff_eq_of_mem_terms p
            (hterms ▸ List.mem_cons_of_mem _ hterm)
        rw [← hcoeff]
        exact hd termMono

/-- Unit recognition is sound and complete under the coefficient gcd laws. -/
theorem polyIsUnit_iff [LawfulGcdOps R] (p : MvPoly n R cmp) :
    polyIsUnit p = true ↔ ∃ q, p * q = 1 := by
  sorry

/-- The chosen normalization multiplier is a polynomial unit. -/
theorem polyNormUnit_isUnit [IsMonomialOrder cmp] [LawfulGcdOps R]
    (p : MvPoly n R cmp) :
    polyIsUnit (polyNormUnit p) = true := by
  sorry

/-- Polynomial normalization is idempotent. -/
theorem polyNormalize_idem [IsMonomialOrder cmp] [LawfulGcdOps R]
    (p : MvPoly n R cmp) :
    polyNormalize (polyNormalize p) = polyNormalize p := by
  sorry

end Hex.MvPoly
