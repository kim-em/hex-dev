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

theorem noncanonical_queries (p : Poly) (qs : List Poly) (hp : 0 < p.natDegree) :
    (QueryReduction.build Hex.TarskiTests.Noncanonical.sign p qs).check
      Hex.TarskiTests.Noncanonical.sign p qs = true := by
  apply QueryReduction.build_checks value value_eq_zero value_one value_add value_sub value_mul
    Hex.TarskiTests.Noncanonical.sign _ value_neg value_inv _ p qs hp
  · intro a
    simp only [Hex.TarskiTests.Noncanonical.sign, Int.sign_eq_one_iff_pos, Rat.num_pos]
  · intro a
    simp only [Hex.TarskiTests.Noncanonical.sign, Int.sign_neg_iff, Rat.num_neg]

@[expose] def preparedQueries : QueryReduction Rat :=
  ⟨[⟨0, 1, ⟨1, 1, 1⟩⟩, ⟨1, indeterminate, ⟨1, 0, 1⟩⟩]⟩

theorem queries_checked : preparedQueries.check Sturm.orderSign head
    [indeterminate * indeterminate, indeterminate] = true := by decide +kernel

example : preparedQueries.queries.length = 2 ∧
    ∀ q ∈ preparedQueries.queries, q.isZero = true ∨ q.natDegree < head.natDegree :=
  QueryReduction.check_bounds queries_checked

example : (preparedQueries.slice 1 1).check Sturm.orderSign head [indeterminate] = true :=
  QueryReduction.slice_checks queries_checked 1 1

theorem queries_sign (a : Rat)
    (hp : (interpret id (fun _ => Iff.rfl) head).eval a = 0) :
    preparedQueries.queries.map (fun q => SignType.sign ((interpret id (fun _ => Iff.rfl) q).eval a)) =
      [indeterminate * indeterminate, indeterminate].map
        (fun q => SignType.sign ((interpret id (fun _ => Iff.rfl) q).eval a)) :=
  QueryReduction.check_signs id (fun _ => Iff.rfl) rfl (fun _ _ => rfl) (fun _ _ => rfl)
    (fun _ _ => rfl) Sturm.orderSign (fun x => (HexSturmMathlib.orderSign_spec x).1)
    head _ preparedQueries queries_checked a hp

theorem queries_rejected :
    ({steps := [⟨0, -1, ⟨1, 1, -1⟩⟩]} : QueryReduction Rat).check
      Sturm.orderSign head [indeterminate * indeterminate] = false := by decide +kernel

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

@[expose] def twoSigns : System 2 where
  rows := #v[[0], [1]]
  columns := #v[[-1], [1]]
  counts := #v[1, 1]
  values := #v[2, 0]
  inverse := Matrix.ofRows #v[#v[1, -1], #v[1, 1]]
  denominator := 2

theorem twoSigns_checks : twoSigns.check 1 = true := by decide +kernel

/-- The exact solver theorem consumes a kernel-checked moment system. -/
theorem twoSigns_solved : solveScaled 1 twoSigns.rows twoSigns.columns twoSigns.values
    twoSigns.denominator twoSigns.inverse = .ok twoSigns :=
  solveScaled_eq twoSigns twoSigns_checks

example : (Matrix.rankCert twoSigns.retainedMatrix).rank = twoSigns.positive.length :=
  twoSigns.basis_rank twoSigns_checks

example : (productVector #v[[0], [1]] #v[[2], [0]]).toList =
    [[0, 2], [0, 0], [1, 2], [1, 0]] := by
  rw [productVector_toList]
  decide +kernel

example : tensor (Matrix.identity 0) (Matrix.identity 2) = Matrix.identity 0 := by
  decide +kernel

example : tensor (Matrix.identity 2) (Matrix.identity 0) = Matrix.identity 0 := by
  decide +kernel

/-- info: 'Hex.SignDet.System.retained_rank' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms System.retained_rank
/-- info: 'Hex.SignDet.QueryReduction.slice_checks' depends on axioms: [propext] -/
#guard_msgs in
#print axioms QueryReduction.slice_checks
/-- info: 'Hex.SignDet.Node.check_sign' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Node.check_sign
/-- info: 'Hex.SignDet.derivativesFrom_get' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms derivativesFrom_get
/-- info: 'Hex.SignDetMathlib.Conformance.noncanonical_queries' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms noncanonical_queries
/-- info: 'Hex.SignDetMathlib.Conformance.queries_sign' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms queries_sign
/-- info: 'Hex.SignDetMathlib.Conformance.queries_rejected' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms queries_rejected
/-- info: 'Hex.SignDet.System.basis_columns' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms System.basis_columns
/-- info: 'Hex.SignDet.System.basis_inverse' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms System.basis_inverse
/-- info: 'Hex.SignDet.tensor_inverse' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms tensor_inverse
/-- info: 'Hex.SignDet.momentMatrix_product' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms momentMatrix_product
/-- info: 'Hex.SignDet.Node.product_inverse' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Node.product_inverse
/-- info: 'Hex.SignDet.solveScaled_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms solveScaled_eq
/-- info: 'Hex.SignDetMathlib.Conformance.twoSigns_solved' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms twoSigns_solved

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
