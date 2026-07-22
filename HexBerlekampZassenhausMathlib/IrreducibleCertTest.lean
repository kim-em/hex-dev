/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public meta import HexBerlekampZassenhausMathlib.IrreducibleCert
public import HexBerlekampZassenhausMathlib.IrreducibleCert
-- The `irreducible_cert` proofs attach `Eq.refl true` for each certificate
-- check, so the kernel must reduce `checkIrreducibleCertLinear` (and its
-- Berlekamp pow-chain replay) plus the `Array`/`DensePoly` `==` comparisons.
-- Expose those executable checker bodies and the efficient `Array` DecidableEq.
import all HexBerlekampZassenhaus.PrimeSelection
import all HexBerlekampZassenhaus.Records
import all HexBerlekampZassenhaus.Certificate
import all HexBerlekampZassenhaus.ChoosePrimeData
import all HexBerlekampZassenhaus.ReassemblyProofs
import all HexBerlekampZassenhaus.Lattice
import all HexBerlekampZassenhaus.BhksCandidates
import all HexBerlekampZassenhaus.BhksRecover
import all HexBerlekampZassenhaus.Recombination
import all HexBerlekampZassenhaus.FactorEntryPoints
import all HexBerlekampZassenhaus.IrreducibleCore
import all HexBerlekampZassenhaus.RecombineProofs
import all HexBerlekampZassenhaus.TrialProofs
import all HexBerlekampZassenhaus.QuadraticRootProofs
import all HexBerlekampZassenhaus.PrimitivityProofs
import all HexBerlekampZassenhaus.ProductProofs
import all HexBerlekamp.Irreducibility
import all Init.Data.Array.DecidableEq

public section
set_option backward.proofsInPublic true

/-!
End-to-end tests for certificate reification and the `irreducible_cert`
tactic, on the generator guard polynomials from the compiled-generator PR
(#8552 Part 1): two monic quadratics, a linear polynomial (empty certificate),
and the inert-prime cubic `x³ - x - 1`.

The round-trip tests reify each generated certificate, typecheck the resulting
`Expr`, evaluate it back to a value, and compare it field-by-field with the
original through the canonical `certificateData` serialization.
-/

namespace HexBerlekampZassenhausMathlib.IrreducibleCertTest

open Lean

/-- `x² + 2`, irreducible with inert prime 3. -/
def quadTwo : Hex.ZPoly := Hex.DensePoly.ofCoeffs #[2, 0, 1]

/-- `x² + x + 1`, irreducible with inert prime 5. -/
def quadOmega : Hex.ZPoly := Hex.DensePoly.ofCoeffs #[1, 1, 1]

/-- `x + 3`, irreducible of degree 1 (empty certificate: no candidate factor
degrees to obstruct). -/
def linearThree : Hex.ZPoly := Hex.DensePoly.ofCoeffs #[3, 1]

/-- `x³ - x - 1`, irreducible with inert prime 3: the single inert block
obstructs every proper factor degree at once. -/
def cubicInert : Hex.ZPoly := Hex.DensePoly.ofCoeffs #[-1, -1, 0, 1]

/-- Reify the generated certificate (and the polynomial itself), typecheck
them, evaluate them back, and compare with the originals; also confirm the
evaluated copy still passes the kernel checker's compiled form. -/
private meta def roundTrips (f : Hex.ZPoly) : MetaM Bool := do
  match Hex.certifyIrreducible? f with
  | none => return false
  | some cert => do
      let certE := Hex.CertReify.reifyCertificate cert
      Meta.check certE
      let cert' ← IrreducibleCert.evalCertificate certE
      let fE ← Hex.CertReify.reifyZPoly f
      Meta.check fE
      let f' ← IrreducibleCert.evalZPoly fE
      return Hex.CertReify.certificateData cert == Hex.CertReify.certificateData cert'
        && f.toArray == f'.toArray
        && Hex.checkIrreducibleCertLinear f' cert'

run_meta do
  for (name, f) in [("quadTwo", quadTwo), ("quadOmega", quadOmega),
      ("linearThree", linearThree), ("cubicInert", cubicInert)] do
    unless (← roundTrips f) do
      throwError "certificate reification round-trip failed for {name}"

/-! ### The tactic, end to end -/

example : Irreducible (HexPolyZMathlib.toPolynomial quadTwo) := by
  irreducible_cert

example : Irreducible (HexPolyZMathlib.toPolynomial quadOmega) := by
  irreducible_cert

example : Irreducible (HexPolyZMathlib.toPolynomial linearThree) := by
  irreducible_cert

theorem cubicInert_irreducible :
    Irreducible (HexPolyZMathlib.toPolynomial cubicInert) := by
  irreducible_cert

/--
info: 'HexBerlekampZassenhausMathlib.IrreducibleCertTest.cubicInert_irreducible' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms cubicInert_irreducible

/-! ### Clean failure on generator-declined inputs -/

/-- `x² - 1`, reducible: the generator declines and the tactic fails with a
diagnostic instead of handing the kernel a bogus certificate. -/
def reducibleQuad : Hex.ZPoly := Hex.DensePoly.ofCoeffs #[-1, 0, 1]

/--
error: irreducible_cert: certifyIrreducible? produced no certificate for
  reducibleQuad
The polynomial is reducible, non-primitive, or constant, or it is irreducible but its modular factorizations are balanced at every admissible prime (e.g. Swinnerton-Dyer polynomials), which the per-prime degree-sum obstruction language cannot certify.
-/
#guard_msgs in
example : Irreducible (HexPolyZMathlib.toPolynomial reducibleQuad) := by
  irreducible_cert

end HexBerlekampZassenhausMathlib.IrreducibleCertTest
