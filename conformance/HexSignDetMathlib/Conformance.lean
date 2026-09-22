/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexSignDetMathlib
public import HexRealRootsMathlib.TarskiTests

public section

/-! Reduction correspondence and ordinary-kernel replay probes.
Computational conformance owner: `HexSignDet`.
These are polynomial sign identities, not Tarski root-sum theorems. -/
namespace Hex.SignDetMathlib.Conformance

open Hex.SignDet HexPolyMathlib.Interpret
open HexPoly.InterpretTests
open scoped Hex

private theorem value_neg (a : Rep) : value (-a) = -value a := by
  change value (pack (-(raw a).1) (-(raw a).2)) = -value a
  rw [value_pack]
  exact (neg_add (raw a).1 (raw a).2).symm

/-- Actual construction and arbitrary replay use the same noninjective
interpretation, with no algebraic field instance on representatives. -/
theorem noncanonical_checks (p : Poly) (qs : List Poly) (es : List Nat)
    (hp : 0 < p.natDegree) (hlen : qs.length = es.length) (he : es.all (· ≤ 2) = true) :
    (Reduction.build Hex.TarskiTests.Noncanonical.sign p qs es).check
      Hex.TarskiTests.Noncanonical.sign p qs es = true := by
  apply Reduction.build_checks value value_eq_zero value_one value_add value_sub value_mul
    value_neg value_inv Hex.TarskiTests.Noncanonical.sign _ _ p qs es hp hlen he
  · intro a
    simp only [Hex.TarskiTests.Noncanonical.sign, Int.sign_eq_one_iff_pos, Rat.num_pos]
  · intro a
    simp only [Hex.TarskiTests.Noncanonical.sign, Int.sign_neg_iff, Rat.num_neg]

/-- An arbitrary accepted noncanonical reduction preserves signs at every
root; the hypothesis does not restrict the certificate to producer output. -/
theorem noncanonical_sign (p : Poly) (qs : List Poly) (es : List Nat) (r : Reduction Rep)
    (h : r.check Hex.TarskiTests.Noncanonical.sign p qs es = true)
    (a : Rat) (hp : (interpret value value_eq_zero p).eval a = 0) :
    SignType.sign ((interpret value value_eq_zero r.result).eval a) =
      SignType.sign ((interpret value value_eq_zero (moment qs es)).eval a) := by
  apply Reduction.check_sign value value_eq_zero value_add value_sub value_mul
    Hex.TarskiTests.Noncanonical.sign _ value_one p qs es r h a hp
  intro a
  simp only [Hex.TarskiTests.Noncanonical.sign, Int.sign_eq_one_iff_pos, Rat.num_pos]

@[expose] def head : DensePoly Rat := DensePoly.ofCoeffs #[-1, 0, 1]
@[expose] def indeterminate : DensePoly Rat := DensePoly.ofCoeffs #[0, 1]

/-- The literal reduction X² = (X²-1) + 1 includes both indexed factors. -/
@[expose] def square : Reduction Rat :=
  ⟨[⟨0, indeterminate, ⟨1, 0, 1⟩⟩, ⟨0, 1, ⟨1, 1, 1⟩⟩], 1⟩

theorem literal_checks : square.check Sturm.orderSign head [indeterminate] [2] = true := by
  decide +kernel

theorem negative_rejected :
    ({ square with steps := [⟨0, indeterminate, ⟨-1, 0, -1⟩⟩, ⟨0, 1, ⟨1, 1, 1⟩⟩] } :
      Reduction Rat).check Sturm.orderSign head [indeterminate] [2] = false := by
  decide +kernel

/-- A negative right scale can preserve the polynomial identity while
reversing the result sign. Kernel replay rejects that exact forgery. -/
theorem flipped_rejected :
    SignedRemainderChain.subIsZero indeterminate (DensePoly.scale (-1) (-indeterminate)) = true ∧
    ({steps := [⟨0, -indeterminate, ⟨1, 0, -1⟩⟩], result := -indeterminate} : Reduction Rat).check
      Sturm.orderSign head [indeterminate] [1] = false ∧
    (-indeterminate).eval 1 = -1 ∧ indeterminate.eval 1 = 1 := by
  decide +kernel

/-- Ordinary-kernel acceptance is consumed by the actual general soundness
theorem, not replaced by a compiled comparison of the final signs. -/
theorem literal_sign (a : Rat) (hp : (interpret id (fun _ => Iff.rfl) head).eval a = 0) :
    SignType.sign ((interpret id (fun _ => Iff.rfl) square.result).eval a) =
      SignType.sign ((interpret id (fun _ => Iff.rfl) (moment [indeterminate] [2])).eval a) := by
  exact Reduction.check_sign id (fun _ => Iff.rfl) (fun _ _ => rfl) (fun _ _ => rfl)
    (fun _ _ => rfl) Sturm.orderSign (fun x => (HexSturmMathlib.orderSign_spec x).1) rfl
    head [indeterminate] [2] square literal_checks a hp

/-- info: 'Hex.SignDetMathlib.Conformance.noncanonical_checks' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms noncanonical_checks
/-- info: 'Hex.SignDetMathlib.Conformance.noncanonical_sign' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms noncanonical_sign
/-- info: 'Hex.SignDetMathlib.Conformance.literal_checks' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms literal_checks
/-- info: 'Hex.SignDetMathlib.Conformance.negative_rejected' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms negative_rejected
/-- info: 'Hex.SignDetMathlib.Conformance.flipped_rejected' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms flipped_rejected
/-- info: 'Hex.SignDetMathlib.Conformance.literal_sign' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms literal_sign
/-- info: 'Hex.SignDet.checkMoment_sign' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms checkMoment_sign

end Hex.SignDetMathlib.Conformance
