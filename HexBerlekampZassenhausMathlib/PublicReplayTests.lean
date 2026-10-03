/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexBerlekampZassenhausMathlib

public section

/-!
A fresh downstream consumer: ordinary public imports only. Bang tests and
privileged executable imports live in separate modules. Search and quotation
run here, so no theorem about this particular quartic can supply its proof.
-/

namespace HexBerlekampZassenhausMathlib.PublicReplayTests

open Hex
open Polynomial

@[expose] def quartic : ZPoly := DensePoly.ofList [-2, -7, -1, 4, 1]

#guard HexBerlekampZassenhaus.FactorTactic.searchWitness quartic |>.isNone
#guard (certifyIrreducible? quartic).isSome
#guard ((certifyIrreducible? quartic).map fun c => c.perPrime.toList.map (·.p)) == some [11, 5]

open Lean Elab Term in
local elab "generatedCertificate" : term => do
  let some c := certifyIrreducible? (DensePoly.ofList [-2, -7, -1, 4, 1])
    | throwError "no certificate"
  return CertificateSyntax.reifyCertificate c

@[expose] def cert : ZPolyIrreducibilityCertificate := generatedCertificate

/-- Literal replay through public reduction equations. -/
theorem cert_checked : checkMultiPrimeCert quartic cert = true := by cbv

theorem cert_irreducible : ZPoly.Irreducible quartic :=
  zpolyIrreducible_of_checkMultiPrimeCert quartic cert cert_checked

open Lean Elab Term in
local elab "quotedIrreducibility" : term => do
  let f : ZPoly := DensePoly.ofList [-2, -7, -1, 4, 1]
  let some c := certifyIrreducible? f | throwError "no certificate"
  FactorTactic.zpolyIrredProof (← CertificateSyntax.reifyZPoly f) (.multi c)

/-- Direct quotation through the API consumed by optional adapters. -/
theorem quoted_irreducible : ZPoly.Irreducible quartic := quotedIrreducibility

theorem tactic_irreducible : ZPoly.Irreducible quartic := by irreducibility

example : True := by
  irreducibility h : quartic
  guard_hyp h :ₛ ZPoly.Irreducible quartic
  trivial

example : True := by
  irreducibility quartic
  guard_hyp this :ₛ ZPoly.Irreducible quartic
  trivial

theorem transported_irreducible : Irreducible (HexPolyZMathlib.toPolynomial quartic) := by
  irreducibility

theorem polynomial_irreducible : Irreducible ((X : Polynomial ℤ) ^ 4 +
    4 * X ^ 3 - X ^ 2 - 7 * X - 2) := by
  irreducibility

theorem sum_irreducible : ZPoly.Irreducible
    (DensePoly.ofList [-2, -7, -1] + DensePoly.ofList [0, 0, 0, 4, 1]) := by
  irreducibility

/-- A mixed free/multi-prime cover through the `Hex.ZPoly` consumer. -/
noncomputable def zFactored : ZPoly.Factored (DensePoly.ofList [-1, 1] * quartic) :=
  factor_poly (DensePoly.ofList [-1, 1] * quartic)

example : zFactored.factors = [DensePoly.ofList [-1, 1], quartic] := by rfl

/-- The parsed `Polynomial ℤ` cover consumer. -/
noncomputable def pFactored : Hex.FactoredPoly
    ((X - 1) * (X ^ 4 + 4 * X ^ 3 - X ^ 2 - 7 * X - 2) : Polynomial ℤ) :=
  factor_poly ((X - 1) * (X ^ 4 + 4 * X ^ 3 - X ^ 2 - 7 * X - 2) : Polynomial ℤ)

example : pFactored.factors.length = 2 := by rfl

/-- A nontrivial single-prime witness alongside the multi-prime factor. -/
noncomputable def mixedFactored : ZPoly.Factored (DensePoly.ofList [-2, 0, 1] * quartic) :=
  factor_poly (DensePoly.ofList [-2, 0, 1] * quartic)

example : mixedFactored.factors = [DensePoly.ofList [-2, 0, 1], quartic] := by rfl

-- Missing degree evidence, an out-of-range block index, malformed modular
-- factor metadata, and a certificate bound to a different input all reject.
theorem missing_obstructions :
    checkMultiPrimeCert quartic { cert with degreeObstructions := #[] } = false := by cbv

theorem invalid_index : checkMultiPrimeCert quartic
    { cert with degreeObstructions := #[⟨1, 2⟩, ⟨2, 1⟩] } = false := by cbv

theorem invalid_degrees : checkMultiPrimeCert quartic
    { cert with perPrime := #[{ cert.perPrime[0] with factorDegrees := #[1, 3] },
        cert.perPrime[1]] } = false := by cbv

theorem wrong_polynomial :
    checkMultiPrimeCert (DensePoly.ofList [-3, -7, -1, 4, 1]) cert = false := by cbv

theorem wrong_cover : checkMultiPrimeCover [DensePoly.ofList [-3, -7, -1, 4, 1]]
    [] [(quartic, cert)] = false := by cbv

open Lean Elab Term in
local elab "replayFalse" : term => CertificateReplay.checkProof (mkConst ``Bool.false)

/-- error: `decide_cbv` failed: the proposition evaluates to `false` -/
#guard_msgs in
example : false = true := replayFalse

-- Free-layer routes continue to work under the same ordinary imports.
theorem single_prime : Irreducible ((X : Polynomial ℤ) ^ 2 - 2) := by irreducibility

theorem eisenstein_shift : Irreducible ((X : Polynomial ℤ) ^ 4 + 1) := by irreducibility

theorem primitive_linear : ZPoly.Irreducible (DensePoly.ofList [-1, 1]) := by irreducibility

theorem prime_constant : ZPoly.Irreducible (DensePoly.C 7) := by irreducibility

end HexBerlekampZassenhausMathlib.PublicReplayTests

/-- info: 'HexBerlekampZassenhausMathlib.PublicReplayTests.cert_checked' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms HexBerlekampZassenhausMathlib.PublicReplayTests.cert_checked

/-- info: 'HexBerlekampZassenhausMathlib.PublicReplayTests.cert_irreducible' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms HexBerlekampZassenhausMathlib.PublicReplayTests.cert_irreducible

/-- info: 'HexBerlekampZassenhausMathlib.PublicReplayTests.quoted_irreducible' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms HexBerlekampZassenhausMathlib.PublicReplayTests.quoted_irreducible

/-- info: 'HexBerlekampZassenhausMathlib.PublicReplayTests.tactic_irreducible' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms HexBerlekampZassenhausMathlib.PublicReplayTests.tactic_irreducible

/-- info: 'HexBerlekampZassenhausMathlib.PublicReplayTests.transported_irreducible' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms HexBerlekampZassenhausMathlib.PublicReplayTests.transported_irreducible

/-- info: 'HexBerlekampZassenhausMathlib.PublicReplayTests.polynomial_irreducible' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms HexBerlekampZassenhausMathlib.PublicReplayTests.polynomial_irreducible

/-- info: 'HexBerlekampZassenhausMathlib.PublicReplayTests.zFactored' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms HexBerlekampZassenhausMathlib.PublicReplayTests.zFactored

/-- info: 'HexBerlekampZassenhausMathlib.PublicReplayTests.pFactored' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms HexBerlekampZassenhausMathlib.PublicReplayTests.pFactored

/-- info: 'HexBerlekampZassenhausMathlib.PublicReplayTests.missing_obstructions' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms HexBerlekampZassenhausMathlib.PublicReplayTests.missing_obstructions

/-- info: 'HexBerlekampZassenhausMathlib.PublicReplayTests.invalid_index' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms HexBerlekampZassenhausMathlib.PublicReplayTests.invalid_index

/-- info: 'HexBerlekampZassenhausMathlib.PublicReplayTests.invalid_degrees' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms HexBerlekampZassenhausMathlib.PublicReplayTests.invalid_degrees

/-- info: 'HexBerlekampZassenhausMathlib.PublicReplayTests.wrong_polynomial' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms HexBerlekampZassenhausMathlib.PublicReplayTests.wrong_polynomial

/-- info: 'HexBerlekampZassenhausMathlib.PublicReplayTests.wrong_cover' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms HexBerlekampZassenhausMathlib.PublicReplayTests.wrong_cover

/-- info: 'HexBerlekampZassenhausMathlib.PublicReplayTests.single_prime' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms HexBerlekampZassenhausMathlib.PublicReplayTests.single_prime

/-- info: 'HexBerlekampZassenhausMathlib.PublicReplayTests.eisenstein_shift' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms HexBerlekampZassenhausMathlib.PublicReplayTests.eisenstein_shift

/-- info: 'HexBerlekampZassenhausMathlib.PublicReplayTests.primitive_linear' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms HexBerlekampZassenhausMathlib.PublicReplayTests.primitive_linear

/-- info: 'HexBerlekampZassenhausMathlib.PublicReplayTests.prime_constant' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms HexBerlekampZassenhausMathlib.PublicReplayTests.prime_constant


/-- info: 'HexBerlekampZassenhausMathlib.PublicReplayTests.sum_irreducible' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms HexBerlekampZassenhausMathlib.PublicReplayTests.sum_irreducible

/-- info: 'HexBerlekampZassenhausMathlib.PublicReplayTests.mixedFactored' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms HexBerlekampZassenhausMathlib.PublicReplayTests.mixedFactored
