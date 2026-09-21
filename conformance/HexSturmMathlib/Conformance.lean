/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexSturmMathlib
public import HexRealRootsMathlib.TarskiTests

public section

/-! Universal instantiations of field frontend domain and replay correspondence.
Computational conformance owner: `HexSturm`.
No runtime comparison is used to prove a semantic query value. -/
namespace HexSturmMathlib.Conformance

open Hex DensePoly HexPolyMathlib.Interpret
open HexPoly.InterpretTests

/-- Canonical rationals satisfy the complete mathematical domain theorem. -/
theorem rational_domain (p g : DensePoly Rat) (a b : Endpoint Rat) :
    (Sturm.query Sturm.orderSign p g a b).isSome = true ↔ Domain id (fun _ => Iff.rfl) p a b :=
  query_isSome id (fun _ => Iff.rfl) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)
    Sturm.orderSign (fun x => (orderSign_spec x).2.1) (fun x => (orderSign_spec x).2.2.1)
    rfl (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun x => (orderSign_spec x).1) p g a b

/-- Canonical rational certificates retain exact literal context bindings. -/
theorem rational_checks {Ctx : Type u} [DecidableEq Ctx] (context : Ctx)
    (p g : DensePoly Rat) (a b : Endpoint Rat) (cert : TarskiCertificate Rat Rat Ctx)
    (hc : Sturm.certify Sturm.orderSign context p g a b = some cert) :
    Sturm.check Sturm.orderSign context p g a b cert.value cert = true :=
  certify_checks id (fun _ => Iff.rfl) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)
    Sturm.orderSign (fun x => (orderSign_spec x).2.1) rfl (fun _ => rfl) (fun _ => rfl)
    (fun x => (orderSign_spec x).1) (fun x => (orderSign_spec x).2.2.2) context p g a b cert hc

private theorem value_neg (a : Rep) : value (-a) = -value a := by
  change value (pack (-(raw a).1) (-(raw a).2)) = -value a
  rw [value_pack]
  exact (neg_add (raw a).1 (raw a).2).symm

/-- The same domain theorem applies to genuinely noninjective representations;
no field, ring or order instance is installed on `Rep`. -/
theorem noncanonical_domain (p g : Poly) (a b : Endpoint Rep) :
    (Sturm.query Hex.TarskiTests.Noncanonical.sign p g a b).isSome = true ↔
      Domain value value_eq_zero p a b := by
  apply query_isSome value value_eq_zero value_add value_sub value_mul
    Hex.TarskiTests.Noncanonical.sign
    (fun a => by simp only [Hex.TarskiTests.Noncanonical.sign, Int.sign_neg_iff, Rat.num_neg])
    (fun a => by simp only [Hex.TarskiTests.Noncanonical.sign, Int.sign_eq_zero_iff_zero, Rat.num_eq_zero])
    value_one value_neg value_inv value_natCast
    (fun a => by simp only [Hex.TarskiTests.Noncanonical.sign, Int.sign_eq_one_iff_pos, Rat.num_pos])

/-- info: 'HexSturmMathlib.Conformance.rational_domain' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms rational_domain
/-- info: 'HexSturmMathlib.Conformance.rational_checks' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms rational_checks
/-- info: 'HexSturmMathlib.Conformance.noncanonical_domain' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms noncanonical_domain

/-- info: 'HexSturmMathlib.prepare_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms HexSturmMathlib.prepare_sound
/-- info: 'HexSturmMathlib.prepared_domain' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms HexSturmMathlib.prepared_domain
/-- info: 'HexSturmMathlib.certifyPrepared_checks' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms HexSturmMathlib.certifyPrepared_checks

/-- info: 'HexSturmMathlib.query_rat_domain' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms HexSturmMathlib.query_rat_domain

/-- info: 'HexSturmMathlib.query_rat_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms HexSturmMathlib.query_rat_eq
/-- info: 'HexSturmMathlib.check_rat_value' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms HexSturmMathlib.check_rat_value
/-- info: 'HexRealRootsMathlib.Tarski.check_compare' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms HexRealRootsMathlib.Tarski.check_compare

/-- A genuinely noninjective coefficient interpretation transports supplied
certificates, including their infinite endpoints, without a field instance on `Rep`. -/
theorem noncanonical_transport {Ctx : Type u} [DecidableEq Ctx] (context : Ctx)
    (p g : Poly) (a b : Endpoint Rep) (v : Int) (cert : TarskiCertificate Rep Rep Ctx)
    (h : TarskiCertificate.check Hex.TarskiTests.Noncanonical.sign
      Hex.TarskiTests.Noncanonical.endpointSigns context p g a b v cert = true) :
    Sturm.check (fun q : Rat => q.num.sign) context (mapped p) (mapped g)
      (a.map value) (b.map value) v (cert.map value value_eq_zero value) = true := by
  apply TarskiCertificate.map_checks value value_eq_zero value
    Hex.TarskiTests.Noncanonical.sign (fun q : Rat => q.num.sign) (fun _ => rfl)
    Hex.TarskiTests.Noncanonical.endpointSigns (EndpointSigns.ofSign (fun q : Rat => q.num.sign))
    _ _ value_add value_sub value_mul value_one value_natCast context p g a b v cert h
  · intro a b
    change (value a - value b).num.sign = (value (a - b)).num.sign
    rw [value_sub]
  · intro p a
    change ((mapped p).eval (value a)).num.sign = (value (p.eval a)).num.sign
    rw [DensePoly.Interpret.map_eval value value_eq_zero value_add value_mul]

/-- The actual noncanonical and rational producers agree as whole Options,
including invalid domains and infinite endpoints. -/
theorem noncanonical_query (p g : Poly) (a b : Endpoint Rep) :
    Sturm.query Hex.TarskiTests.Noncanonical.sign p g a b =
      Sturm.query (fun q : Rat => q.num.sign) (mapped p) (mapped g) (a.map value) (b.map value) := by
  have hb (q : Rat) : -1 ≤ q.num.sign ∧ q.num.sign ≤ 1 := by
    rcases Int.sign_trichotomy q.num with h | h | h <;> omega
  have hpoly (q : Poly) : interpret id (fun _ => Iff.rfl) (mapped q) =
      Polynomial.C (1 : Rat) * interpret value value_eq_zero q := by
    rw [Polynomial.C_1, one_mul]
    ext i
    simp only [coeff_interpret, mapped, DensePoly.Interpret.map_coeff, id_eq]
  apply query_congr value value_eq_zero value_add value_sub value_mul value_natCast
    id (fun _ => Iff.rfl) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ => rfl)
    Hex.TarskiTests.Noncanonical.sign (fun q : Rat => q.num.sign)
    (fun q => by simp only [Hex.TarskiTests.Noncanonical.sign, Int.sign_eq_one_iff_pos, Rat.num_pos])
    (fun q => by simp only [Int.sign_eq_one_iff_pos, Rat.num_pos, id_eq])
    (fun q => by simp only [Hex.TarskiTests.Noncanonical.sign, Int.sign_neg_iff, Rat.num_neg])
    (fun q => by simp only [Int.sign_neg_iff, Rat.num_neg, id_eq])
    (fun q => by simp only [Hex.TarskiTests.Noncanonical.sign, Int.sign_eq_zero_iff_zero, Rat.num_eq_zero])
    (fun q => by simp only [Int.sign_eq_zero_iff_zero, Rat.num_eq_zero, id_eq])
    (fun q => hb (value q)) hb value_one value_neg value_inv rfl (fun _ => rfl) (fun _ => rfl)
    p g (mapped p) (mapped g) a b (a.map value) (b.map value) 1 1 (by decide) (by decide)
    (hpoly p) (hpoly g)
  · cases a <;> rfl
  · cases b <;> rfl

namespace Transport

@[expose] def p : DensePoly Rat := ofCoeffs #[-(1 / 2), 0, 1 / 2]
@[expose] def g : DensePoly Rat := C (1 / 3)
@[expose] def remainders : SignedRemainderChain Rat where
  chain := #[p, ofCoeffs #[0, 1 / 6], C (1 / 5)]
  degrees := #[2, 1, 0]
  initial := ⟨1 / 2, 0, 1⟩
  steps := #[⟨3 / 2, ofCoeffs #[0, 9 / 2], 15 / 4⟩]
  terminal := some (2 / 3, ofCoeffs #[0, 5 / 9])

@[expose] def literal : TarskiCertificate Rat Rat (Nat × Nat) where
  context := (11, 23)
  head := p
  queryPoly := g
  lower := .finite (-2)
  upper := .finite 2
  squarefree := { remainders with initial := ⟨1 / 2, 0, 3⟩ }
  remainders := remainders
  lowerSigns := #[1, -1, 1]
  upperSigns := #[1, 1, 1]
  lowerVariations := 2
  upperVariations := 0
  value := 2

/-- A supplied certificate with denominators in every kind of identity.
Its entries and scales were chosen independently of the producer. -/
theorem accepted : Sturm.check Sturm.orderSign (11, 23) p g
    (.finite Hex.TarskiTests.interval.lower.toRat) (.finite Hex.TarskiTests.interval.upper.toRat)
    2 literal = true := by
  simp only [Sturm.check, TarskiCertificate.check, SignedRemainderChain.check,
    ← Array.all_toList, Array.toList_range]
  decide +kernel

/-- Positive clearing translates the literal evidence with its full context. -/
theorem cleared : TarskiCertificate.check Int.sign EndpointSigns.intDyadic (11, 23)
    (ZPoly.clearDenominators p).2 (ZPoly.clearDenominators g).2
    (.finite Hex.TarskiTests.interval.lower) (.finite Hex.TarskiTests.interval.upper) 2
    (TarskiCertificate.clearDenominators p g Hex.TarskiTests.interval literal) = true :=
  DenominatorClearing.certificate_checks _ _ _ _ _ _ accepted

/-- The translated evidence embeds back into a checked rational certificate. -/
theorem embedded : Sturm.check Sturm.orderSign (11, 23)
    (ZPoly.toRatPoly (ZPoly.clearDenominators p).2) (ZPoly.toRatPoly (ZPoly.clearDenominators g).2)
    (.finite Hex.TarskiTests.interval.lower.toRat) (.finite Hex.TarskiTests.interval.upper.toRat) 2
    (TarskiCertificate.toRat (TarskiCertificate.clearDenominators p g Hex.TarskiTests.interval literal)) = true := by
  simpa only [Endpoint.map] using IntCast.certificate_checks (11, 23)
    (ZPoly.clearDenominators p).2 (ZPoly.clearDenominators g).2
    (.finite Hex.TarskiTests.interval.lower) (.finite Hex.TarskiTests.interval.upper) 2
    (TarskiCertificate.clearDenominators p g Hex.TarskiTests.interval literal) cleared

/-- Denominator clearing does not erase the literal context binding. -/
theorem stale : TarskiCertificate.check Int.sign EndpointSigns.intDyadic (11, 24)
    (ZPoly.clearDenominators p).2 (ZPoly.clearDenominators g).2
    (.finite Hex.TarskiTests.interval.lower) (.finite Hex.TarskiTests.interval.upper) 2
    (TarskiCertificate.clearDenominators p g Hex.TarskiTests.interval literal) = false := by
  simp only [TarskiCertificate.check, TarskiCertificate.clearDenominators, TarskiCertificate.fromChains,
    literal, show (((11, 23) : Nat × Nat) ≠ (11, 24)) by decide, decide_false, Bool.false_and]

end Transport

/-- info: 'Hex.TarskiCertificate.map_checks' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hex.TarskiCertificate.map_checks
/-- info: 'HexSturmMathlib.DenominatorClearing.certificate_checks' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms HexSturmMathlib.DenominatorClearing.certificate_checks
/-- info: 'HexSturmMathlib.IntCast.certificate_checks' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms HexSturmMathlib.IntCast.certificate_checks
/-- info: 'HexSturmMathlib.Conformance.Transport.accepted' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Transport.accepted
/-- info: 'HexSturmMathlib.Conformance.Transport.embedded' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Transport.embedded
/-- info: 'HexSturmMathlib.Conformance.noncanonical_transport' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms noncanonical_transport
/-- info: 'HexSturmMathlib.Conformance.noncanonical_query' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms noncanonical_query
/-- info: 'HexSturmMathlib.query_congr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms HexSturmMathlib.query_congr

end HexSturmMathlib.Conformance
