/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

import HexBasic.Fold
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
  match p.leadingTerm with
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
  rw [polyNormUnit, leadingTerm_zero]

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

/-- Scalar content is already in the coefficient ring's canonical
normalization. -/
theorem normalize_scalarContent [LawfulGcdOps R] (p : MvPoly n R cmp) :
    normalize (scalarContent p) = scalarContent p := by
  cases hterms : p.termsList with
  | nil =>
      unfold scalarContent
      rw [hterms]
      exact Lean.Grind.Semiring.zero_mul _
  | cons head terms =>
      unfold scalarContent
      rw [hterms]
      simp only
      exact LawfulGcdOps.normalize_idem _

private theorem eq_zero_of_mul_eq_zero {a b : Mono n}
    (h : Mono.mul a b = Mono.zero) : a = Mono.zero := by
  apply Vector.ext
  intro i hi
  let j : Fin n := ⟨i, hi⟩
  have hj := congrArg (fun m : Mono n => m[j]) h
  have hj' : a[j] + b[j] = 0 := by
    calc
      a[j] + b[j] = (Mono.mul a b)[j] := (Mono.getElem_mul a b j).symm
      _ = Mono.zero[j] := hj
      _ = 0 := Mono.getElem_zero j
  change a[j] = Mono.zero[j]
  rw [Mono.getElem_zero]
  exact (Nat.eq_zero_of_add_eq_zero hj').1

private theorem eq_zero_of_isLE [IsMonomialOrder cmp] {m : Mono n}
    (h : (cmp m Mono.zero).isLE) : m = Mono.zero := by
  cases hcmp : cmp m Mono.zero with
  | lt =>
      have hgt : cmp Mono.zero m = .gt :=
        (Std.OrientedCmp.gt_iff_lt (cmp := cmp)).mpr hcmp
      exact False.elim (IsMonomialOrder.zero_le m hgt)
  | eq => exact Std.LawfulEqCmp.eq_of_compare hcmp
  | gt => simp [hcmp] at h

/-- Unit recognition is sound and complete under the coefficient gcd laws. -/
theorem polyIsUnit_iff [IsMonomialOrder cmp] [LawfulGcdOps R]
    (p : MvPoly n R cmp) :
    polyIsUnit p = true ↔ ∃ q, p * q = 1 := by
  constructor
  · intro hunit
    cases hterms : p.termsList with
    | nil => simp [polyIsUnit, hterms] at hunit
    | cons term terms =>
        cases terms with
        | nil =>
            rcases term with ⟨m, c⟩
            rw [polyIsUnit, hterms] at hunit
            simp only at hunit
            change (decide (m = Mono.zero) && GcdOps.isUnit c) = true at hunit
            rcases Bool.and_eq_true_iff.mp hunit with ⟨hm, hc⟩
            have hmzero : m = Mono.zero := by
              simpa only [decide_eq_true_eq] using hm
            subst m
            rcases (LawfulGcdOps.isUnit_iff c).mp hc with ⟨d, hd⟩
            have hcne : c ≠ 0 := by
              intro hzero
              rw [hzero, Lean.Grind.Semiring.zero_mul] at hd
              exact LawfulGcdOps.one_ne_zero hd.symm
            have hpC : p = C c := by
              apply termsList_inj
              rw [hterms, termsList_C, ite_eq_right hcne]
            refine ⟨C d, ?_⟩
            rw [hpC]
            change monomial Mono.zero c * monomial Mono.zero d = 1
            rw [monomial_mul_monomial, Mono.zero_mul, hd]
            rfl
        | cons next rest => simp [polyIsUnit, hterms] at hunit
  · rintro ⟨q, hpq⟩
    have hpzero : p ≠ 0 := by
      intro hp
      subst p
      rw [zero_mul] at hpq
      have hcoeff := congrArg (coeff (Mono.zero : Mono n)) hpq
      rw [coeff_zero, coeff_one, ite_eq_left rfl] at hcoeff
      exact LawfulGcdOps.one_ne_zero hcoeff.symm
    have hqzero : q ≠ 0 := by
      intro hq
      subst q
      rw [mul_zero] at hpq
      have hcoeff := congrArg (coeff (Mono.zero : Mono n)) hpq
      rw [coeff_zero, coeff_one, ite_eq_left rfl] at hcoeff
      exact LawfulGcdOps.one_ne_zero hcoeff.symm
    cases hpLead : p.leadingTerm with
    | none => exact False.elim (hpzero ((leadingTerm_eq_none_iff p).mp hpLead))
    | some pterm =>
        rcases pterm with ⟨mp, cp⟩
        cases hqLead : q.leadingTerm with
        | none => exact False.elim (hqzero ((leadingTerm_eq_none_iff q).mp hqLead))
        | some qterm =>
            rcases qterm with ⟨mq, cq⟩
            have hlead := leadingTerm_mul hpLead hqLead
            have hcoeff := coeff_eq_of_leadingTerm hlead
            rw [hpq, coeff_one] at hcoeff
            have hcp : cp ≠ 0 := by
              intro hzero
              have hopt := (leadingTerm_eq_some_iff p mp cp).mp hpLead |>.1
              exact p.coeff?_ne_zero mp
                (hopt.trans (congrArg some hzero))
            have hcq : cq ≠ 0 := by
              intro hzero
              have hopt := (leadingTerm_eq_some_iff q mq cq).mp hqLead |>.1
              exact q.coeff?_ne_zero mq
                (hopt.trans (congrArg some hzero))
            have hcprod : cp * cq ≠ 0 := by
              intro hzero
              rcases LawfulGcdOps.no_zero_div cp cq hzero with hzero | hzero
              · exact hcp hzero
              · exact hcq hzero
            have hmono : Mono.mul mp mq = Mono.zero := by
              by_cases hmono : Mono.mul mp mq = Mono.zero
              · exact hmono
              · rw [ite_eq_right hmono] at hcoeff
                exact False.elim (hcprod hcoeff.symm)
            have hcoeffUnit : cp * cq = 1 := by
              rw [ite_eq_left hmono] at hcoeff
              exact hcoeff.symm
            have hmp : mp = Mono.zero := eq_zero_of_mul_eq_zero hmono
            have hpC : p = C cp := by
              apply ext
              intro m
              rw [coeff_C]
              by_cases hm : m = Mono.zero
              · subst m
                rw [← hmp, coeff_eq_of_leadingTerm hpLead]
                simp
              · rw [ite_eq_right hm]
                apply coeff_eq_zero_of_not_mem m p
                intro hmem
                have hle := le_leadingTerm hpLead m hmem
                rw [hmp] at hle
                exact hm (eq_zero_of_isLE hle)
            have hisUnit : GcdOps.isUnit cp = true :=
              (LawfulGcdOps.isUnit_iff cp).mpr ⟨cq, hcoeffUnit⟩
            rw [hpC]
            rw [polyIsUnit, termsList_C, ite_eq_right hcp]
            simp [hisUnit]

/-- The chosen normalization multiplier is a polynomial unit. -/
theorem polyNormUnit_isUnit [IsMonomialOrder cmp] [LawfulGcdOps R]
    (p : MvPoly n R cmp) :
    polyIsUnit (polyNormUnit p) = true := by
  rw [polyIsUnit_iff]
  unfold polyNormUnit
  cases hlead : p.leadingTerm with
  | none =>
      refine ⟨1, ?_⟩
      exact one_mul _
  | some term =>
      rcases term with ⟨m, c⟩
      rcases LawfulGcdOps.normUnit_unit c with ⟨d, hd⟩
      refine ⟨C d, ?_⟩
      change monomial Mono.zero (GcdOps.normUnit c) *
          monomial Mono.zero d = 1
      rw [monomial_mul_monomial, Mono.zero_mul, hd]
      rfl

/-- Polynomial normalization is idempotent. -/
theorem polyNormalize_idem [IsMonomialOrder cmp] [LawfulGcdOps R]
    (p : MvPoly n R cmp) :
    polyNormalize (polyNormalize p) = polyNormalize p := by
  cases hlead : p.leadingTerm with
  | none =>
      have hpzero : p = 0 := (leadingTerm_eq_none_iff p).mp hlead
      subst p
      simp
  | some term =>
      rcases term with ⟨m, c⟩
      have hc : c ≠ 0 := by
        intro hzero
        have hcoeff := (leadingTerm_eq_some_iff p m c).mp hlead |>.1
        exact p.coeff?_ne_zero m (hcoeff.trans (congrArg some hzero))
      rcases LawfulGcdOps.normUnit_unit c with ⟨d, hd⟩
      have hu : GcdOps.normUnit c ≠ 0 := by
        intro hzero
        rw [hzero, Lean.Grind.Semiring.zero_mul] at hd
        exact LawfulGcdOps.one_ne_zero hd.symm
      have hunitLead :
          (C (GcdOps.normUnit c) : MvPoly n R cmp).leadingTerm =
            some (Mono.zero, GcdOps.normUnit c) :=
        leadingTerm_C hu
      have hnormLead : (polyNormalize p).leadingTerm =
          some (m, normalize c) := by
        unfold polyNormalize polyNormUnit
        rw [hlead]
        simpa [normalize] using leadingTerm_mul hlead hunitLead
      have hnormNe : normalize c ≠ 0 := by
        intro hzero
        unfold normalize at hzero
        rcases LawfulGcdOps.no_zero_div c (GcdOps.normUnit c) hzero with
          hczero | huzero
        · exact hc hczero
        · exact hu huzero
      have hnext : GcdOps.normUnit (normalize c) = 1 := by
        have hzero :
            normalize c * (GcdOps.normUnit (normalize c) - 1) = 0 := by
          calc
            normalize c * (GcdOps.normUnit (normalize c) - 1) =
                normalize (normalize c) - normalize c := by
                  unfold normalize
                  grind
            _ = 0 := by rw [LawfulGcdOps.normalize_idem]; grind
        rcases LawfulGcdOps.no_zero_div (normalize c)
            (GcdOps.normUnit (normalize c) - 1) hzero with hzero | hrest
        · exact False.elim (hnormNe hzero)
        · grind
      change polyNormalize p * polyNormUnit (polyNormalize p) = polyNormalize p
      unfold polyNormUnit
      rw [hnormLead]
      simp only
      rw [hnext]
      exact mul_one _

/-- Polynomial normalization sends every polynomial unit to one. -/
theorem polyNormalize_unit [IsMonomialOrder cmp] [LawfulGcdOps R]
    (p : MvPoly n R cmp) (hp : polyIsUnit p = true) :
    polyNormalize p = 1 := by
  cases hterms : p.termsList with
  | nil => simp [polyIsUnit, hterms] at hp
  | cons term terms =>
      cases terms with
      | nil =>
          rcases term with ⟨m, c⟩
          rw [polyIsUnit, hterms] at hp
          change (decide (m = Mono.zero) && GcdOps.isUnit c) = true at hp
          rcases Bool.and_eq_true_iff.mp hp with ⟨hm, hc⟩
          have hmzero : m = Mono.zero := by
            simpa only [decide_eq_true_eq] using hm
          subst m
          rcases (LawfulGcdOps.isUnit_iff c).mp hc with ⟨d, hd⟩
          have hcne : c ≠ 0 := by
            intro hzero
            rw [hzero, Lean.Grind.Semiring.zero_mul] at hd
            exact LawfulGcdOps.one_ne_zero hd.symm
          have hpC : p = C c := by
            apply termsList_inj
            rw [hterms, termsList_C, ite_eq_right hcne]
          have hnorm : c * GcdOps.normUnit c = 1 := by
            exact LawfulGcdOps.normalize_unit c hc
          rw [hpC]
          unfold polyNormalize polyNormUnit
          rw [leadingTerm_C hcne]
          change monomial Mono.zero c *
              monomial Mono.zero (GcdOps.normUnit c) = 1
          rw [monomial_mul_monomial, Mono.zero_mul, hnorm]
          rfl
      | cons next rest => simp [polyIsUnit, hterms] at hp

/-- Polynomial normalization is multiplicative. -/
theorem polyNormalize_mul [IsMonomialOrder cmp] [LawfulGcdOps R]
    (p q : MvPoly n R cmp) :
    polyNormalize (p * q) = polyNormalize p * polyNormalize q := by
  cases hp : p.leadingTerm with
  | none =>
      have hpzero : p = 0 := (leadingTerm_eq_none_iff p).mp hp
      subst p
      rw [MvPoly.zero_mul, polyNormalize_zero]
      exact (MvPoly.zero_mul _).symm
  | some pterm =>
      rcases pterm with ⟨mp, cp⟩
      cases hq : q.leadingTerm with
      | none =>
          have hqzero : q = 0 := (leadingTerm_eq_none_iff q).mp hq
          subst q
          rw [MvPoly.mul_zero, polyNormalize_zero]
          exact (MvPoly.mul_zero _).symm
      | some qterm =>
          rcases qterm with ⟨mq, cq⟩
          have hcp : cp ≠ 0 := by
            intro hzero
            have hcoeff := (leadingTerm_eq_some_iff p mp cp).mp hp |>.1
            exact p.coeff?_ne_zero mp (hcoeff.trans (congrArg some hzero))
          have hcq : cq ≠ 0 := by
            intro hzero
            have hcoeff := (leadingTerm_eq_some_iff q mq cq).mp hq |>.1
            exact q.coeff?_ne_zero mq (hcoeff.trans (congrArg some hzero))
          have hcprod : cp * cq ≠ 0 := by
            intro hzero
            rcases LawfulGcdOps.no_zero_div cp cq hzero with hzero | hzero
            · exact hcp hzero
            · exact hcq hzero
          have hunit : GcdOps.normUnit (cp * cq) =
              GcdOps.normUnit cp * GcdOps.normUnit cq := by
            have hnorm := LawfulGcdOps.normalize_mul cp cq
            have hzero : (cp * cq) *
                (GcdOps.normUnit (cp * cq) -
                  GcdOps.normUnit cp * GcdOps.normUnit cq) = 0 := by
              unfold normalize at hnorm
              grind
            rcases LawfulGcdOps.no_zero_div (cp * cq) _ hzero with
              hzero | hrest
            · exact False.elim (hcprod hzero)
            · grind
          have hlead := leadingTerm_mul hp hq
          unfold polyNormalize polyNormUnit
          rw [hp, hq, hlead]
          simp only
          rw [hunit]
          have hC :
              (C (GcdOps.normUnit cp * GcdOps.normUnit cq) :
                  MvPoly n R cmp) =
                C (GcdOps.normUnit cp) * C (GcdOps.normUnit cq) := by
            change monomial Mono.zero
                (GcdOps.normUnit cp * GcdOps.normUnit cq) =
              monomial Mono.zero (GcdOps.normUnit cp) *
                monomial Mono.zero (GcdOps.normUnit cq)
            rw [monomial_mul_monomial, Mono.zero_mul]
          rw [hC]
          grind

end Hex.MvPoly
