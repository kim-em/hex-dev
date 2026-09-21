/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexSturmMathlib.Domain
public import HexRealRootsMathlib.TarskiDomain
public import HexRealRootsMathlib.TarskiSigns

public section

namespace HexSturmMathlib

open Hex HexPolyMathlib.Interpret HexRealRootsMathlib

/-- Positive denominator clearing has the same real interpretation as the
existing integer and rational polynomial correspondence. -/
theorem toPolyℝ_clearDenominators (p : DensePoly Rat) :
    toPolyℝ (ZPoly.clearDenominators p).2 =
      Polynomial.C ((ZPoly.clearDenominators p).1 : ℝ) *
        interpret (fun x : Rat => (x : ℝ)) (fun _ => Rat.cast_eq_zero) p := by
  ext i
  have h := congrArg (fun q : DensePoly Rat => q.coeff i) (ZPoly.toRatPoly_clearDenominators p)
  simp only [ZPoly.coeff_toRatPoly, DensePoly.coeff_scale _ _ _ (mul_zero _)] at h
  simp only [coeff_toPolyℝ, Polynomial.coeff_C_mul, coeff_interpret]
  exact_mod_cast h

/-- The rational and integer/dyadic frontends reject exactly the same domains
after positive denominator clearing, on finite ordered dyadic intervals. This
establishes the invalid `none` cases on that domain, not successful-value equality.
Validity is independent of the query polynomial; clearing `g` is unconstrained
by this domain theorem. -/
theorem query_rat_domain (p g : DensePoly Rat) (I : DyadicInterval) :
    (Sturm.query Sturm.orderSign p g (.finite I.lower.toRat) (.finite I.upper.toRat)).isSome =
      (ZPoly.tarskiQuery (ZPoly.clearDenominators p).2 (ZPoly.clearDenominators g).2 I).isSome := by
  have hfield := query_isSome (fun x : Rat => (x : ℝ)) (fun _ => Rat.cast_eq_zero)
    (fun a b => Rat.cast_add a b) (fun a b => Rat.cast_sub a b) (fun a b => Rat.cast_mul a b)
    Sturm.orderSign
    (fun x => (orderSign_spec x).2.1.trans Rat.cast_lt_zero.symm)
    (fun x => (orderSign_spec x).2.2.1.trans Rat.cast_eq_zero.symm)
    Rat.cast_one (fun a => Rat.cast_neg a) (fun a => Rat.cast_inv a)
    (fun n => by simp) (fun x => (orderSign_spec x).1.trans Rat.cast_pos.symm)
    p g (.finite I.lower.toRat) (.finite I.upper.toRat)
  have hc : ((ZPoly.clearDenominators p).1 : ℝ) ≠ 0 := by
    exact_mod_cast ne_of_gt (ZPoly.clearDenominators_pos p)
  have hC : (Polynomial.C ((ZPoly.clearDenominators p).1 : ℝ) : Polynomial ℝ) ≠ 0 :=
    Polynomial.C_ne_zero.mpr hc
  have hsf := (associated_unit_mul_left
    (interpret (fun x : Rat => (x : ℝ)) (fun _ => Rat.cast_eq_zero) p)
    (Polynomial.C ((ZPoly.clearDenominators p).1 : ℝ))
    ((isUnit_iff_ne_zero.mpr hc).map Polynomial.C)).squarefree_iff
  have horder : (I.lower.toRat : ℝ) < (I.upper.toRat : ℝ) := by
    simpa only [toReal_eq_cast_toRat] using (toReal_lt_toReal I.lt)
  have hnz : (ZPoly.clearDenominators p).2 ≠ 0 ↔
      toPolyℝ (ZPoly.clearDenominators p).2 ≠ 0 :=
    not_congr toPolyℝ_eq_zero_iff.symm
  apply Bool.eq_iff_iff.mpr
  rw [hfield, Tarski.integer_domain, hnz, toPolyℝ_clearDenominators]
  simp only [Domain, EndpointLt, Nonvanishing, horder, true_and, hsf,
    mul_ne_zero_iff, Polynomial.eval_mul, Polynomial.eval_C, toReal_eq_cast_toRat]
  constructor
  · rintro ⟨hp, hs, ha, hb⟩
    exact ⟨⟨hC, hp⟩, hs, ⟨hc, ha⟩, hc, hb⟩
  · rintro ⟨⟨_, hp⟩, hs, ⟨_, ha⟩, _, hb⟩
    exact ⟨hp, hs, ha, hb⟩

/-- Positively corresponding rational and integer chains have identical exact
sign arrays at the same finite dyadic endpoint. -/
theorem signs_rat_eq (chain : Array (DensePoly Rat)) (chain' : Array ZPoly)
    (hsize : chain.size = chain'.size)
    (hscale : ∀ i, ∃ c : ℝ, 0 < c ∧
      interpret (fun z : Int => (z : ℝ)) (fun _ => Int.cast_eq_zero) (chain'.getD i 0) =
        Polynomial.C c * interpret (fun z : Rat => (z : ℝ))
          (fun _ => Rat.cast_eq_zero) (chain.getD i 0)) (x : Dyadic) :
    TarskiCertificate.signs Sturm.orderSign (Sturm.endpointSigns Sturm.orderSign) chain (.finite x.toRat) =
      TarskiCertificate.signs Int.sign EndpointSigns.intDyadic chain' (.finite x) := by
  apply Tarski.finite_signs_eq (fun z : Rat => (z : ℝ)) (fun _ => Rat.cast_eq_zero)
    (fun z : Int => (z : ℝ)) (fun _ => Int.cast_eq_zero)
    Sturm.orderSign Int.sign (Sturm.endpointSigns Sturm.orderSign) EndpointSigns.intDyadic
    x.toRat x (HexRealRootsMathlib.Dyadic.toReal x) _ _ _ _ _ _ chain chain' hsize hscale
  · intro p
    exact (orderSign_spec (p.eval x.toRat)).2.2.2
  · intro p
    exact Tarski.integer_signs p (.finite x)
  · intro p
    rw [toReal_eq_cast_toRat, eval_interpret _ _ (fun a b => Rat.cast_add a b)
      (fun a b => Rat.cast_mul a b)]
    exact (orderSign_spec (p.eval x.toRat)).2.1.trans Rat.cast_lt_zero.symm
  · intro p
    rw [Tarski.interpret_int_real, ← toReal_evalDyadic]
    exact Tarski.dyadicSign_neg _
  · intro p
    rw [toReal_eq_cast_toRat, eval_interpret _ _ (fun a b => Rat.cast_add a b)
      (fun a b => Rat.cast_mul a b)]
    exact (orderSign_spec (p.eval x.toRat)).2.2.1.trans Rat.cast_eq_zero.symm
  · intro p
    rw [Tarski.interpret_int_real]
    exact evalSign_zero_iff p x

/-- Arbitrary accepted rational and integer certificates give the same value
after positive denominator clearing. Their literal data need not agree and
neither certificate is assumed to have been produced by a frontend. -/
theorem check_rat_value {Ctx : Type u} [DecidableEq Ctx] (context : Ctx)
    (p g : DensePoly Rat) (I : DyadicInterval) (v w : Int)
    (cert : TarskiCertificate Rat Rat Ctx) (cert' : IntTarskiCertificate)
    (h : Sturm.check Sturm.orderSign context p g
      (.finite I.lower.toRat) (.finite I.upper.toRat) v cert = true)
    (h' : IntTarskiCertificate.check (ZPoly.clearDenominators p).2 (ZPoly.clearDenominators g).2 I w cert' = true) :
    v = w := by
  obtain ⟨hc, hv⟩ := Tarski.check_value Sturm.orderSign (Sturm.endpointSigns Sturm.orderSign)
    context p g (.finite I.lower.toRat) (.finite I.upper.toRat) v cert h
  obtain ⟨hc', hw⟩ := Tarski.check_value Int.sign EndpointSigns.intDyadic ()
    (ZPoly.clearDenominators p).2 (ZPoly.clearDenominators g).2
    (.finite I.lower) (.finite I.upper) w cert' h'
  have hcompare := Tarski.check_compare (fun z : Rat => (z : ℝ)) (fun _ => Rat.cast_eq_zero)
    (fun a b => Rat.cast_add a b) (fun a b => Rat.cast_sub a b) (fun a b => Rat.cast_mul a b)
    (fun n => by simp) Sturm.orderSign
    (fun x => (orderSign_spec x).1.trans Rat.cast_pos.symm)
    (fun z : Int => (z : ℝ)) (fun _ => Int.cast_eq_zero)
    (fun a b => Int.cast_add a b) (fun a b => Int.cast_sub a b) (fun a b => Int.cast_mul a b)
    (fun n => by simp) Int.sign (fun x => Int.sign_eq_one_iff_pos.trans Int.cast_pos.symm)
    p g cert.remainders hc (ZPoly.clearDenominators p).2 (ZPoly.clearDenominators g).2
    cert'.remainders hc' ((ZPoly.clearDenominators p).1 : ℝ) ((ZPoly.clearDenominators g).1 : ℝ)
    (by exact_mod_cast ZPoly.clearDenominators_pos p)
    (by exact_mod_cast ZPoly.clearDenominators_pos g)
    (by rw [Tarski.interpret_int_real, toPolyℝ_clearDenominators])
    (by rw [Tarski.interpret_int_real, toPolyℝ_clearDenominators])
  rw [hv, hw, signs_rat_eq _ _ hcompare.1 hcompare.2 I.lower,
    signs_rat_eq _ _ hcompare.1 hcompare.2 I.upper]

/-- Whole-`Option` agreement of the rational and integer/dyadic frontends
after positive denominator clearing. Both domain rejection and successful
signed values agree, including common factors and zero initial remainders. -/
theorem query_rat_eq (p g : DensePoly Rat) (I : DyadicInterval) :
    Sturm.query Sturm.orderSign p g (.finite I.lower.toRat) (.finite I.upper.toRat) =
      ZPoly.tarskiQuery (ZPoly.clearDenominators p).2 (ZPoly.clearDenominators g).2 I := by
  have hdom := query_rat_domain p g I
  have hv := Sturm.certify_value Sturm.orderSign () p g (.finite I.lower.toRat) (.finite I.upper.toRat)
  have hw : (IntTarskiCertificate.certify (ZPoly.clearDenominators p).2 (ZPoly.clearDenominators g).2 I).map
      TarskiCertificate.value = ZPoly.tarskiQuery (ZPoly.clearDenominators p).2
        (ZPoly.clearDenominators g).2 I := rfl
  rw [← hv, ← hw] at hdom ⊢
  cases hc : Sturm.certify Sturm.orderSign () p g (.finite I.lower.toRat) (.finite I.upper.toRat) with
  | none =>
    cases hd : IntTarskiCertificate.certify (ZPoly.clearDenominators p).2 (ZPoly.clearDenominators g).2 I with
    | none => rfl
    | some cert' => simp only [hc, hd, Option.map_none, Option.map_some,
        Option.isSome_none, Option.isSome_some, Bool.false_eq_true] at hdom
  | some cert =>
    cases hd : IntTarskiCertificate.certify (ZPoly.clearDenominators p).2 (ZPoly.clearDenominators g).2 I with
    | none => simp only [hc, hd, Option.map_none, Option.map_some,
        Option.isSome_none, Option.isSome_some, Bool.true_eq_false] at hdom
    | some cert' =>
      simp only [Option.map_some, Option.some.injEq]
      apply check_rat_value () p g I cert.value cert'.value cert cert'
      · exact certify_checks (fun x : Rat => (x : ℝ)) (fun _ => Rat.cast_eq_zero)
          (fun a b => Rat.cast_add a b) (fun a b => Rat.cast_sub a b) (fun a b => Rat.cast_mul a b)
          Sturm.orderSign (fun x => (orderSign_spec x).2.1.trans Rat.cast_lt_zero.symm)
          Rat.cast_one (fun x => Rat.cast_neg x) (fun x => Rat.cast_inv x)
          (fun x => (orderSign_spec x).1.trans Rat.cast_pos.symm)
          (fun x => (orderSign_spec x).2.2.2) () p g
          (.finite I.lower.toRat) (.finite I.upper.toRat) cert hc
      · exact (Tarski.integer_certify_checks _ _ I cert' hd).1

end HexSturmMathlib
