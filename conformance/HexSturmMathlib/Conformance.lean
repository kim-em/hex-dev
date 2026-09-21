/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexSturmMathlib
public import HexRealRootsMathlib.QueryTests

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
    (p g : DensePoly Rat) (a b : Endpoint Rat) (cert : QueryReplay Rat Rat Ctx)
    (hc : Sturm.certify Sturm.orderSign context p g a b = some cert) :
    Sturm.Replay.check Sturm.orderSign context p g a b cert.value cert = true :=
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
    (Sturm.query Hex.QueryTests.Noncanonical.sign p g a b).isSome = true ↔
      Domain value value_eq_zero p a b := by
  apply query_isSome value value_eq_zero value_add value_sub value_mul
    Hex.QueryTests.Noncanonical.sign
    (fun a => by simp only [Hex.QueryTests.Noncanonical.sign, Int.sign_neg_iff, Rat.num_neg])
    (fun a => by simp only [Hex.QueryTests.Noncanonical.sign, Int.sign_eq_zero_iff_zero, Rat.num_eq_zero])
    value_one value_neg value_inv value_natCast
    (fun a => by simp only [Hex.QueryTests.Noncanonical.sign, Int.sign_eq_one_iff_pos, Rat.num_pos])

/-- info: 'HexSturmMathlib.Conformance.rational_domain' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms rational_domain
/-- info: 'HexSturmMathlib.Conformance.rational_checks' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms rational_checks
/-- info: 'HexSturmMathlib.Conformance.noncanonical_domain' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms noncanonical_domain

end HexSturmMathlib.Conformance
