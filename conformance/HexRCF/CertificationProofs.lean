/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRCF.RealCoefficients
public import HexRCF.CertificationInputs
public meta import HexRCF.RealCoefficients
public meta import HexRCF.CertificationInputs
public meta import Lean.Elab.Tactic

public section
namespace Hex.RCF.CertificationProofs
open RealCoefficients CertificationInputs

set_option maxRecDepth 2048
set_option maxHeartbeats 2000000

theorem compound_positive : ∀ x : ℝ,
    x ^ 2 + (realAlgebraic.toReal ^ 2 + 1) > 0 := by rcf

abbrev fieldValue : RealAlgebraicNumber :=
  Coefficients.ofField realAlgebraic (realAlgebraic.toAlgebraic.toQAdjoin ^ 2 + 1)

theorem coordinate_positive : ∀ x : ℝ, x ^ 2 + fieldValue.toReal > 0 := by rcf

theorem guarded_positive : ∀ x : ℝ,
    x ^ 2 + 1 / realAlgebraic.toReal > 0 := by rcf

theorem further_root : ∃ x : ℝ,
    x ^ 2 = realAlgebraic.toReal ∧ 1 < x ∧ x < 2 := by rcf

theorem normalized_positive : ∀ x : ℝ,
    x ^ 2 + (normalized.toReal ^ 2 + 1) > 0 := by rcf

open Lean Meta Qq in
local elab "commonCertificate%" : term => do
  let p : ZPoly := DensePoly.ofList [-2, -7, -1, 4, 1]
  let degree ← mkDecideProof q(0 < polynomial.natDegree)
  CommonTactic.certify p q(polynomial) degree

open Lean Meta Qq in
local elab "wrongCommon%" : term => do
  let saved ← saveState
  let rejected ← try
    let p : ZPoly := DensePoly.ofList [-2, -7, -1, 4, 1]
    let expression : Q(ZPoly) := q(DensePoly.ofList [-3, -7, -1, 4, 1])
    let degree ← mkDecideProof q(0 < ($expression).natDegree)
    let _ ← CommonTactic.certify p expression degree
    pure false
  catch error =>
    pure ((← error.toMessageData.toString).startsWith
      "zpolyIrredProof: multi-prime certificate replay failed")
  saved.restore
  unless rejected do throwError "common certificate proved the wrong polynomial"
  return q(True.intro)

example : True := wrongCommon%

theorem common_certificate : polynomial.CheckedIrreducible := commonCertificate%

abbrev cubicPolynomial : ZPoly := DensePoly.ofList [2, -4, 0, 1]
abbrev cubicSquare : DyadicSquare :=
  ⟨Dyadic.ofIntWithPrec 112416129 26, 0, 24⟩

theorem cubicChecked : cubicPolynomial.CheckedIrreducible :=
  Field.checkedIrreducible cubicPolynomial (.eisenstein 2 0)
    (by decide +kernel) (by decide)

theorem cubicSquarefree : HasOnlySimpleRoots cubicPolynomial := by
  let : cubicPolynomial.CheckedIrreducible := cubicChecked
  exact (HexRootsMathlib.hasOnlySimpleRoots_iff_separable cubicPolynomial
    (by decide)).mpr (ZPoly.CheckedIrreducible.separable cubicPolynomial)

abbrev cubicRoot : RealAlgebraicNumber :=
  Selected.real cubicPolynomial cubicSquare (by decide +kernel) (by decide)
    (by rfl) (by decide) (by decide) cubicChecked cubicSquarefree (by decide +kernel)

-- This genuine degree-six compositum has a new polynomial. The first two
-- frontend certificate languages decline; the public multi-prime route succeeds.
open Lean Meta Qq in
run_meta do
  let (_, _, quadratic) ← FieldRuntime.coefficient q(Real.sqrt 37)
  let common := QAdjoin.common #[cubicRoot.toAlgebraic, quadratic.toAlgebraic]
  let p := common.generator.p
  unless p.natDegree == 6 && p != cubicPolynomial && p != quadratic.toAlgebraic.p do
    throwError "expected a new degree-six common polynomial"
  unless (QuadraticNormCertificate.certify? p).isNone &&
      (HexBerlekampZassenhaus.FactorTactic.searchWitness p).isNone &&
      (certifyIrreducible? p).isSome do
    throwError "common polynomial did not reach the multi-prime certificate language"

set_option maxRecDepth 8192 in
set_option maxHeartbeats 5000000 in
theorem common_multiprime : ∀ x : ℝ,
    x ^ 2 + cubicRoot.toReal + Real.sqrt 37 > 0 := by rcf

abbrev quadraticRoot : RealAlgebraicNumber :=
  Selected.real SquareTwo.polynomial SquareTwo.square (by decide) (by decide)
    (by rfl) (by decide) (by decide) SquareTwo.checked SquareTwo.squarefree (by decide)

-- The current certificate languages do not cover every irreducible common
-- presentation. Pin this input and its first three good-prime patterns;
-- each pattern permits a degree-two factor, so these blocks cannot certify it.
-- Refusal is not a mathematical reducibility claim.
run_meta do
  let common := QAdjoin.common #[realAlgebraic.toAlgebraic, quadraticRoot.toAlgebraic]
  let p := common.generator.p
  unless p.toArray == #[-2, -24, 169, 70, -127, -70, 6, 8, 1] && p.content == 1 do
    throwError "unexpected degree-eight common presentation"
  unless (QuadraticNormCertificate.certify? p).isNone &&
      (HexBerlekampZassenhaus.FactorTactic.searchWitness p).isNone &&
      (certifyIrreducible? p).isNone do
    throwError "expected the documented certificate-language refusal"
  let patterns : Array (Nat × Array Nat) := #[(5, #[2, 6]),
    (7, #[3, 1, 1, 3]), (11, #[2, 2, 2, 2])]
  for (prime, degrees) in patterns do
    let some candidate := smallPrimeCandidates.find? (·.m == prime) |
      throwError "missing prime candidate {prime}"
    let some data := probePrimeData? p candidate |
      throwError "missing good-prime data {prime}"
    unless data.factorsModP.map (·.natDegree) == degrees do
      throwError "unexpected factor pattern at {prime}"

-- Exercise failures without leaving failed declarations or proof admissions.
local elab "expect_certificate_error " message:str : tactic => do
  let saved ← Lean.Elab.Tactic.saveState
  let observed ← try
    Lean.Elab.Tactic.evalTactic (← `(tactic| rcf))
    pure none
  catch error => pure (some (← error.toMessageData.toString))
  saved.restore
  unless observed == some message.getString do
    throwError "unexpected rcf result: {observed}"
  Lean.Elab.Tactic.evalTactic (← `(tactic| exact False.elim (by assumption)))

example (_impossible : False) : ∀ x : ℝ, x ^ 2 + realAlgebraic.toReal < 0 := by
  expect_certificate_error "rcf: the universal sentence is false on the prepared cells"

example (_impossible : False) : ∀ x : ℝ,
    x ^ 2 + 0 / (realAlgebraic.toReal - realAlgebraic.toReal) ≥ 0 := by
  expect_certificate_error "rcf: original closed divisor is zero"

example (_impossible : False) : ∀ x : ℝ,
    x ^ 2 + realAlgebraic.toReal + quadraticRoot.toReal > 0 := by
  expect_certificate_error "rcf: no checked irreducibility witness for this common field"

end Hex.RCF.CertificationProofs

/-- info: 'Hex.RCF.CertificationProofs.compound_positive' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RCF.CertificationProofs.compound_positive

/-- info: 'Hex.RCF.CertificationProofs.coordinate_positive' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RCF.CertificationProofs.coordinate_positive

/-- info: 'Hex.RCF.CertificationProofs.guarded_positive' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RCF.CertificationProofs.guarded_positive

/-- info: 'Hex.RCF.CertificationProofs.further_root' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RCF.CertificationProofs.further_root

/-- info: 'Hex.RCF.CertificationProofs.normalized_positive' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RCF.CertificationProofs.normalized_positive

/-- info: 'Hex.RCF.CertificationProofs.common_certificate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RCF.CertificationProofs.common_certificate

/-- info: 'Hex.RCF.CertificationProofs.common_multiprime' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RCF.CertificationProofs.common_multiprime
