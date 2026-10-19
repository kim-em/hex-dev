/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexBerlekampZassenhausTheory.FactorTactic

public section

/-! Direct ordinary import of the quotation API, without the umbrella. -/

namespace HexBerlekampZassenhausTheory.QuotationTests

open Hex Lean Elab Term

@[expose] def quartic : ZPoly := DensePoly.ofList [-2, -7, -1, 4, 1]

local elab "quoteMulti" f:term : term => do
  let fE ← elabTerm f (some (mkConst ``Hex.ZPoly))
  synthesizeSyntheticMVarsNoPostponing
  let fE ← instantiateMVars fE
  let some c := certifyIrreducible? (DensePoly.ofList [-2, -7, -1, 4, 1])
    | throwError "no certificate"
  FactorTactic.zpolyIrredProof fE (.multi c)

theorem quoted : ZPoly.Irreducible quartic := quoteMulti quartic

/--
error: zpolyIrredProof: multi-prime certificate replay failed
`decide_cbv` failed: the proposition evaluates to `false`
-/
#guard_msgs in
example : ZPoly.Irreducible (DensePoly.ofList [-3, -7, -1, 4, 1]) :=
  quoteMulti (DensePoly.ofList [-3, -7, -1, 4, 1])

local elab "generatedCertificate" : term => do
  let some c := certifyIrreducible? (DensePoly.ofList [-2, -7, -1, 4, 1])
    | throwError "no certificate"
  return CertificateSyntax.reifyCertificate c

@[expose] def cert : ZPolyIrreducibilityCertificate := generatedCertificate

theorem nonprimitive : checkMultiPrimeCert (2 * quartic) cert = false := by cbv

@[expose] def compositeBlock : PrimeFactorData where
  p := 9
  bounds := ⟨by decide, by decide⟩
  factorDegrees := #[]
  factorPolys := #[]
  factorCerts := #[]

theorem composite_prime : checkMultiPrimeCert quartic
    { perPrime := #[compositeBlock], degreeObstructions := #[] } = false := by cbv

end HexBerlekampZassenhausTheory.QuotationTests

/-- info: 'HexBerlekampZassenhausTheory.QuotationTests.quoted' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms HexBerlekampZassenhausTheory.QuotationTests.quoted

/-- info: 'HexBerlekampZassenhausTheory.QuotationTests.nonprimitive' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms HexBerlekampZassenhausTheory.QuotationTests.nonprimitive

/-- info: 'HexBerlekampZassenhausTheory.QuotationTests.composite_prime' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms HexBerlekampZassenhausTheory.QuotationTests.composite_prime
