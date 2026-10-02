/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexPoly.Interpret
public meta import HexPoly.Interpret
public meta import HexPoly.Dense
public meta import HexPoly.Operations
public meta import HexPoly.Euclid.DivGcd
public import Init.Data.Rat.Lemmas

public section

/-! Ordinary-kernel regression probes for noninjective polynomial interpretation.
The carrier stores a+bX at the root +1 of X²-1, retaining distinct nonzero
representations. It has no ring or field instance. -/
namespace HexPoly.InterpretTests

/-- Only zero is canonical; other representations can have equal denotations. -/
@[expose] def ZeroRep (A : Type) (isZero : A → Bool) := Option {a : A // isZero a = false}

namespace ZeroRep
variable {A : Type} {isZero : A → Bool}
instance : Zero (ZeroRep A isZero) := ⟨none⟩
instance [DecidableEq A] : DecidableEq (ZeroRep A isZero) :=
  inferInstanceAs (DecidableEq (Option {a : A // isZero a = false}))
@[expose] def ofRaw (a : A) : ZeroRep A isZero :=
  if h : isZero a = false then some ⟨a, h⟩ else none

end ZeroRep

-- a+bX interpreted at the selected root +1 of the reducible polynomial X²-1.
@[expose] def atOne (ab : Rat × Rat) : Rat := ab.1 + ab.2
@[expose] def testZero (ab : Rat × Rat) : Bool := decide (atOne ab = 0)
abbrev Rep := ZeroRep (Rat × Rat) testZero

@[expose] def pack (a b : Rat) : Rep := ZeroRep.ofRaw (a, b)
@[expose] def raw : Rep → Rat × Rat
  | none => (0, 0)
  | some a => a.val
@[expose] def value (a : Rep) : Rat := atOne (raw a)
instance : One Rep := ⟨pack 1 0⟩
instance : NatCast Rep := ⟨fun n => pack (n : Rat) 0⟩
instance : Add Rep := ⟨fun a b => pack ((raw a).1 + (raw b).1) ((raw a).2 + (raw b).2)⟩
instance : Sub Rep := ⟨fun a b => pack ((raw a).1 - (raw b).1) ((raw a).2 - (raw b).2)⟩
instance : Neg Rep := ⟨fun a => pack (-(raw a).1) (-(raw a).2)⟩
instance : Mul Rep := ⟨fun a b =>
  pack ((raw a).1 * (raw b).1 + (raw a).2 * (raw b).2)
       ((raw a).1 * (raw b).2 + (raw a).2 * (raw b).1)⟩
instance : Inv Rep := ⟨fun a => pack (value a)⁻¹ 0⟩
instance : Div Rep := ⟨fun a b => pack (value a / value b) 0⟩

theorem value_pack (a b : Rat) : value (pack a b) = a + b := by
  by_cases h : a + b = 0
  · simp [pack, ZeroRep.ofRaw, testZero, atOne, h, value, raw]
    exact Rat.zero_add 0
  · simp [pack, ZeroRep.ofRaw, testZero, atOne, h, value, raw]

theorem value_zero : value (0 : Rep) = 0 := Rat.zero_add 0

theorem value_eq_zero (a : Rep) : value a = 0 ↔ a = 0 := by
  cases a with
  | none =>
    simp [value, raw, atOne, Rat.zero_add, show (0 : Rep) = none from rfl]
    rfl
  | some a =>
    have hn : atOne a.val ≠ 0 := by simpa [testZero] using a.property
    simp [value, raw, hn, show (0 : Rep) = none from rfl]

theorem value_add (a b : Rep) : value (a+b) = value a + value b := by
  change value (pack _ _) = _
  rw [value_pack]
  unfold value atOne
  grind

theorem value_sub (a b : Rep) : value (a-b) = value a - value b := by
  change value (pack _ _) = _
  rw [value_pack]
  unfold value atOne
  grind

theorem value_mul (a b : Rep) : value (a*b) = value a * value b := by
  change value (pack _ _) = _
  rw [value_pack]
  unfold value atOne
  grind

theorem value_div (a b : Rep) : value (a/b) = value a / value b := by
  change value (pack _ 0) = _
  rw [value_pack]
  grind

-- Same selected-root value, different nonzero representations.
@[expose] def root : Rep := pack 0 1
example : root ≠ (1 : Rep) := by decide +kernel
example : value root = value (1 : Rep) := by decide +kernel
example : root - 1 = (0 : Rep) := by decide +kernel
example : value (-root) = -1 := by decide +kernel
example : pack (-1) 1 = (0 : Rep) := by decide +kernel

-- DensePoly's existing zero normalization works without a Field instance.
abbrev Poly := Hex.DensePoly Rep
@[expose] def p : Poly := Hex.DensePoly.ofCoeffs #[1, root - 1]
example : p.size = 1 := by decide +kernel

@[expose] def x : Poly := Hex.DensePoly.ofCoeffs #[0, 1]
@[expose] def a : Poly := x - Hex.DensePoly.C root
@[expose] def b : Poly := x - Hex.DensePoly.C 1
@[expose] def product : Poly := a*b
@[expose] def remainder : Poly := (Hex.DensePoly.divMod product a).2
example : remainder = 0 := by decide +kernel
example : (Hex.DensePoly.gcd product a).natDegree = 1 := by decide +kernel
example : (Hex.DensePoly.xgcd product a).gcd.natDegree = 1 := by decide +kernel

-- Structural polynomial inequality is NOT a semantic identity test.
example : a ≠ b := by decide +kernel
example : a-b = (0 : Poly) := by decide +kernel
example : (Hex.DensePoly.natPow a 2).natDegree = 2 := by decide +kernel
example : (Hex.DensePoly.monicize product).natDegree = 2 := by decide +kernel
-- Monicity is semantic on this representation, not literal leadingCoeff = 1.
example : ¬ (Hex.DensePoly.monicize (Hex.DensePoly.C (pack 0 2))).Monic := by
  unfold Hex.DensePoly.Monic
  decide +kernel
example : value (Hex.DensePoly.monicize (Hex.DensePoly.C (pack 0 2))).leadingCoeff = 1 := by
  decide +kernel


open Hex DensePoly

theorem value_one : value (1 : Rep) = 1 := by decide +kernel

theorem value_natCast (n : Nat) : value (n : Rep) = (n : Rat) := by
  change value (pack (n : Rat) 0) = _
  rw [value_pack, Rat.add_zero]

theorem value_inv (a : Rep) : value a⁻¹ = (value a)⁻¹ := by
  change value (pack _ 0) = _
  rw [value_pack, Rat.add_zero]

abbrev mapped := Interpret.map value value_eq_zero

theorem division_transfer (p q : Poly) :
    (mapped (divMod p q).1, mapped (divMod p q).2) = divMod (mapped p) (mapped q) :=
  Interpret.map_divMod value value_eq_zero value_sub value_mul value_div p q

theorem gcd_transfer (p q : Poly) : mapped (gcd p q) = gcd (mapped p) (mapped q) :=
  Interpret.map_gcd value value_eq_zero value_sub value_mul value_div p q

theorem bezout_transfer (p q : Poly) :
    ({ gcd := mapped (xgcd p q).gcd, left := mapped (xgcd p q).left,
       right := mapped (xgcd p q).right } : XGCDResult Rat) = xgcd (mapped p) (mapped q) :=
  Interpret.map_xgcd value value_eq_zero value_sub value_mul value_div value_add value_one p q

theorem derivative_transfer (p : Poly) : mapped p.derivative = (mapped p).derivative :=
  Interpret.map_derivative value value_eq_zero value_natCast value_mul p

theorem eval_transfer (p : Poly) (a : Rep) : value (p.eval a) = (mapped p).eval (value a) :=
  Interpret.map_eval value value_eq_zero value_add value_mul p a

-- Complete cancellation of the leading term despite unequal stored operands.
example : (ofCoeffs #[1, root] - ofCoeffs #[0, (1 : Rep)]).size = 1 := by decide +kernel
example : (divMod a b).2 = 0 := by decide +kernel
example : mapped (divMod a b).1 = (1 : DensePoly Rat) := by decide +kernel
example : (divMod a 0).2 = a := by decide +kernel
example : (divMod (0 : Poly) a).2 = 0 := by decide +kernel
example : mapped (gcd (0 : Poly) 0) = 0 := by decide +kernel
example : mapped (xgcd product a).left * mapped product +
    mapped (xgcd product a).right * mapped a = mapped (xgcd product a).gcd := by decide +kernel
example : mapped product.derivative = (mapped product).derivative := by decide +kernel
example : value (product.eval root) = 0 := by decide +kernel
example : mapped (monicize product) = monicize (mapped product) :=
  Interpret.map_monicize value value_eq_zero value_mul value_inv product

-- Division must interpret a noncanonical, nonunit leading coefficient.
@[expose] def noncanonicalDivisor : Poly := ofCoeffs #[1, pack 0 2]
example : noncanonicalDivisor.leadingCoeff ≠ pack 2 0 := by decide +kernel
example : value noncanonicalDivisor.leadingCoeff = 2 := by decide +kernel
example : mapped (divMod product noncanonicalDivisor).1 =
    (ofCoeffs #[-5/4, 1/2] : DensePoly Rat) := by decide +kernel
example : mapped (divMod product noncanonicalDivisor).2 = C (9/4 : Rat) := by decide +kernel
example (p : Poly) : mapped (-p) = -mapped p :=
  Interpret.map_neg value value_eq_zero value_sub p
example (p q : Poly) : mapped (p % q) = mapped p % mapped q :=
  Interpret.map_mod value value_eq_zero value_sub value_mul value_div p q

-- Compiled conformance uses the csimp implementations of these same operations.
#guard (divMod a b).2.isZero
#guard mapped (divMod product noncanonicalDivisor).1 == (ofCoeffs #[-5/4, 1/2] : DensePoly Rat)
#guard mapped (divMod product noncanonicalDivisor).2 == C (9/4 : Rat)
#guard (mapped (gcd product a)).natDegree == 1
#guard mapped product.derivative == (mapped product).derivative

/-- info: 'HexPoly.InterpretTests.division_transfer' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms division_transfer
/-- info: 'HexPoly.InterpretTests.bezout_transfer' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms bezout_transfer

/-- info: 'HexPoly.InterpretTests.gcd_transfer' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms gcd_transfer

/-- info: 'HexPoly.InterpretTests.derivative_transfer' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms derivative_transfer

/-- info: 'HexPoly.InterpretTests.eval_transfer' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms eval_transfer

end HexPoly.InterpretTests
