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

omit [Std.LawfulEqCmp cmp] in
private theorem mul_isLE [IsMonomialOrder cmp]
    {a b c d : Mono n} (hab : (cmp a b).isLE) (hcd : (cmp c d).isLE) :
    (cmp (Mono.mul a c) (Mono.mul b d)).isLE := by
  have hleft : (cmp (Mono.mul a c) (Mono.mul b c)).isLE := by
    rw [← IsMonomialOrder.mul_mono (cmp := cmp) a b c]
    exact hab
  have hright : (cmp (Mono.mul b c) (Mono.mul b d)).isLE := by
    rw [Mono.mul_comm b c, Mono.mul_comm b d,
      ← IsMonomialOrder.mul_mono (cmp := cmp) c d b]
    exact hcd
  exact Std.TransCmp.isLE_trans hleft hright

private theorem left_eq_of_mul_eq [IsMonomialOrder cmp]
    {a b c d : Mono n} (hab : (cmp a b).isLE) (hcd : (cmp c d).isLE)
    (hmul : Mono.mul a c = Mono.mul b d) : a = b := by
  cases hcmp : cmp a b with
  | lt =>
      have hleft : cmp (Mono.mul a c) (Mono.mul b c) = .lt := by
        rw [← IsMonomialOrder.mul_mono (cmp := cmp) a b c]
        exact hcmp
      have hright : (cmp (Mono.mul b c) (Mono.mul b d)).isLE := by
        rw [Mono.mul_comm b c, Mono.mul_comm b d,
          ← IsMonomialOrder.mul_mono (cmp := cmp) c d b]
        exact hcd
      have hlt := Std.TransCmp.lt_of_lt_of_isLE hleft hright
      rw [hmul] at hlt
      have hself : cmp (Mono.mul b d) (Mono.mul b d) = .eq :=
        Std.ReflCmp.compare_self
      rw [hself] at hlt
      contradiction
  | eq => exact Std.LawfulEqCmp.eq_of_compare hcmp
  | gt => simp [hcmp] at hab

private theorem mul_left_cancel {a b c : Mono n}
    (h : Mono.mul a b = Mono.mul a c) : b = c := by
  apply Vector.ext
  intro i hi
  let j : Fin n := ⟨i, hi⟩
  have hj := congrArg (fun m : Mono n => m[j]) h
  simp only [Mono.getElem_mul] at hj
  exact Nat.add_left_cancel hj

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

/-- The leading term of a product is the product of the leading terms over a
coefficient domain. -/
theorem leadingTerm_mul [IsMonomialOrder cmp] [LawfulGcdOps R]
    {p q : MvPoly n R cmp} {mp mq : Mono n} {cp cq : R}
    (hp : p.leadingTerm = some (mp, cp))
    (hq : q.leadingTerm = some (mq, cq)) :
    (p * q).leadingTerm = some (Mono.mul mp mq, cp * cq) := by
  have hpc := (leadingTerm_eq_some_iff p mp cp).mp hp |>.1
  have hqc := (leadingTerm_eq_some_iff q mq cq).mp hq |>.1
  have hcp : cp ≠ 0 := by
    intro hzero
    exact p.coeff?_ne_zero mp (hpc.trans (congrArg some hzero))
  have hcq : cq ≠ 0 := by
    intro hzero
    exact q.coeff?_ne_zero mq (hqc.trans (congrArg some hzero))
  have hprod : cp * cq ≠ 0 := by
    intro hzero
    rcases LawfulGcdOps.no_zero_div cp cq hzero with hzero | hzero
    · exact hcp hzero
    · exact hcq hzero
  have hcoeff : coeff (Mono.mul mp mq) (p * q) = cp * cq := by
    rw [coeff_mul]
    have hmem : (mp, mq) ∈ Mono.splits (Mono.mul mp mq) :=
      (Mono.splits_mem_iff ..).mpr rfl
    calc
      (Mono.splits (Mono.mul mp mq)).foldl
          (fun acc ab => acc + coeff ab.1 p * coeff ab.2 q) 0 =
          (Mono.splits (Mono.mul mp mq)).foldl
            (fun acc ab => acc + if ab = (mp, mq) then cp * cq else 0) 0 := by
              apply List.foldl_congr
              intro acc ab hab
              by_cases hpq : ab = (mp, mq)
              · subst ab
                rw [Hex.ite_eq_left rfl, coeff_eq_of_leadingTerm hp,
                  coeff_eq_of_leadingTerm hq]
              · rw [Hex.ite_eq_right hpq]
                by_cases hpa : coeff ab.1 p = 0
                · rw [hpa, Lean.Grind.Semiring.zero_mul]
                · by_cases hqb : coeff ab.2 q = 0
                  · rw [hqb, Lean.Grind.Semiring.mul_zero]
                  · have hma : ab.1 ∈ p.monomials :=
                      (mem_monomials_iff ab.1 p).mpr hpa
                    have hmb : ab.2 ∈ q.monomials :=
                      (mem_monomials_iff ab.2 q).mpr hqb
                    have ha := le_leadingTerm hp ab.1 hma
                    have hb := le_leadingTerm hq ab.2 hmb
                    have hmul := (Mono.splits_mem_iff ..).mp hab
                    have heqa : ab.1 = mp :=
                      left_eq_of_mul_eq ha hb hmul
                    have heqb : ab.2 = mq := by
                      have hmul' : Mono.mul mp ab.2 = Mono.mul mp mq := by
                        exact (congrArg (fun a => Mono.mul a ab.2) heqa).symm.trans hmul
                      exact mul_left_cancel hmul'
                    exact False.elim (hpq (Prod.ext heqa heqb))
      _ = 0 + cp * cq :=
        List.foldl_add_single _ _ _ _ hmem
          (Mono.splits_nodup (Mono.mul mp mq))
      _ = cp * cq := by grind
  apply (leadingTerm_eq_some_iff (p * q) (Mono.mul mp mq) (cp * cq)).mpr
  constructor
  · cases hopt : (p * q).coeff? (Mono.mul mp mq) with
    | none =>
        have : coeff (Mono.mul mp mq) (p * q) = 0 := by
          unfold coeff
          rw [hopt]
          rfl
        exact False.elim (hprod (hcoeff.symm.trans this))
    | some c =>
        have hc : c = cp * cq := by
          have : coeff (Mono.mul mp mq) (p * q) = c := by
            unfold coeff
            rw [hopt]
            rfl
          exact this.symm.trans hcoeff
        exact congrArg some hc
  · intro m hm
    rcases exists_mul_of_mem hm with ⟨a, ha, b, hb, rfl⟩
    exact mul_isLE (le_leadingTerm hp a ha) (le_leadingTerm hq b hb)

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
              rw [hterms, termsList_C, Hex.ite_eq_right hcne]
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
      rw [coeff_zero, coeff_one, Hex.ite_eq_left rfl] at hcoeff
      exact LawfulGcdOps.one_ne_zero hcoeff.symm
    have hqzero : q ≠ 0 := by
      intro hq
      subst q
      rw [mul_zero] at hpq
      have hcoeff := congrArg (coeff (Mono.zero : Mono n)) hpq
      rw [coeff_zero, coeff_one, Hex.ite_eq_left rfl] at hcoeff
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
              · rw [Hex.ite_eq_right hmono] at hcoeff
                exact False.elim (hcprod hcoeff.symm)
            have hcoeffUnit : cp * cq = 1 := by
              rw [Hex.ite_eq_left hmono] at hcoeff
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
              · rw [Hex.ite_eq_right hm]
                apply coeff_eq_zero_of_not_mem m p
                intro hmem
                have hle := le_leadingTerm hpLead m hmem
                rw [hmp] at hle
                exact hm (eq_zero_of_isLE hle)
            have hisUnit : GcdOps.isUnit cp = true :=
              (LawfulGcdOps.isUnit_iff cp).mpr ⟨cq, hcoeffUnit⟩
            rw [hpC]
            rw [polyIsUnit, termsList_C, Hex.ite_eq_right hcp]
            simp [hisUnit]

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
