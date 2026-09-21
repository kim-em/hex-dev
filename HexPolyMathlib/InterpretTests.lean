/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexPolyMathlib.Interpret
public import HexPoly.InterpretTests

public section

/-! Companion proof probes for the zero-normalized, noncanonical coefficient fixture.
Only the semantic target has a field instance. All proofs use the actual
production correspondence, including the zero-divisor and raw-gcd conventions. -/
namespace HexPolyMathlib.InterpretTests

open Hex DensePoly HexPoly.InterpretTests
open HexPolyMathlib.Interpret

noncomputable abbrev denote := interpret value value_eq_zero

theorem division (p q : Poly) :
    (denote (divMod p q).1, denote (divMod p q).2) =
      (denote p / denote q, denote p % denote q) :=
  interpret_divMod value value_eq_zero value_sub value_mul value_div p q

theorem bezout (p q : Poly) :
    denote (xgcd p q).left * denote p + denote (xgcd p q).right * denote q =
      denote (xgcd p q).gcd :=
  interpret_bezout value value_eq_zero value_sub value_mul value_div value_add value_one p q

theorem gcd_associated (p q : Poly) :
    Associated (denote (gcd p q)) (EuclideanDomain.gcd (denote p) (denote q)) :=
  interpret_gcd value value_eq_zero value_sub value_mul value_div p q

example (p : Poly) : denote p.derivative = (denote p).derivative :=
  interpret_derivative value value_eq_zero value_natCast value_mul p

example (p : Poly) (x : Rep) : (denote p).eval (value x) = value (p.eval x) :=
  eval_interpret value value_eq_zero value_add value_mul p x

example (p : Poly) : denote (-p) = -denote p :=
  interpret_neg value value_eq_zero value_sub p
example (p q : Poly) : denote (p % q) = denote p % denote q :=
  interpret_mod value value_eq_zero value_sub value_mul value_div p q
example (p : Poly) (hp : p ≠ 0) : (denote (monicize p)).leadingCoeff = 1 :=
  monicize_leading value value_eq_zero value_mul value_inv p hp

example : a ≠ b := by decide +kernel
example : denote a = denote b :=
  (sub_isZero value value_eq_zero value_sub a b).mp (by decide +kernel)
example (p : Poly) : denote (divMod p 0).1 = 0 ∧ denote (divMod p 0).2 = denote p := by
  have h := division p 0
  simpa [denote, interpret_zero] using Prod.mk.inj h

/-- info: 'HexPolyMathlib.InterpretTests.division' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms division
/-- info: 'HexPolyMathlib.InterpretTests.bezout' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms bezout

end HexPolyMathlib.InterpretTests
