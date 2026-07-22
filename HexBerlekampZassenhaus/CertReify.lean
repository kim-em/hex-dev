/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexBerlekamp.CertReify
public import HexBerlekampZassenhaus.Certificate
public import Lean

public section

/-!
Elaboration-time reification of `Hex.ZPoly` values and the
`Hex.ZPolyIrreducibilityCertificate` tower as literal `Expr`s, for the
certificate-backed tactics (`irreducibility`, `factor_poly`). Builds on the
`FpPoly`-level reifiers in `HexBerlekamp.CertReify`; see that module for the
smart-constructor discipline (every proof obligation is a `_ = true` slot the
kernel discharges by reduction on literal data).
-/

namespace Hex.CertReify

open Lean

/-- Reify a `PrimeFactorData` block as a constructor application over its
reified prime, degree array, factor array, and nested Rabin certificates. -/
def reifyPrimeFactorData (d : Hex.PrimeFactorData) : Expr :=
  match d with
  | { p := p, bounds := bounds, factorDegrees := degrees, factorPolys := polys,
      factorCerts := certs } =>
      let pE := mkNatLit p
      let boundsE := reifyBounds pE
      let degreesE := arrayLit (mkConst ``Nat) (degrees.toList.map mkNatLit)
      let polysE := arrayLit (fpPolyType pE boundsE)
        (polys.toList.map fun g =>
          reifyFpPolyOfNats pE boundsE (@fpCoeffNats p bounds g))
      let certsE := arrayLit (mkConst ``Hex.Berlekamp.IrreducibilityCertificate)
        (certs.toList.map reifyRabinCert)
      mkApp5 (mkConst ``Hex.PrimeFactorData.mk) pE boundsE degreesE polysE certsE

/-- Reify a `DegreeObstruction` as a constructor application. -/
def reifyDegreeObstruction (o : Hex.DegreeObstruction) : Expr :=
  mkApp2 (mkConst ``Hex.DegreeObstruction.mk)
    (mkNatLit o.targetDegree) (mkNatLit o.primeIndex)

/-- Reify a full `ZPolyIrreducibilityCertificate` as a literal `Expr`. -/
def reifyCertificate (cert : Hex.ZPolyIrreducibilityCertificate) : Expr :=
  mkApp2 (mkConst ``Hex.ZPolyIrreducibilityCertificate.mk)
    (arrayLit (mkConst ``Hex.PrimeFactorData)
      (cert.perPrime.toList.map reifyPrimeFactorData))
    (arrayLit (mkConst ``Hex.DegreeObstruction)
      (cert.degreeObstructions.toList.map reifyDegreeObstruction))

/-- Reify a `ZPoly` as `Hex.DensePoly.ofCoeffs #[…]` with literal `Int`
coefficients. -/
def reifyZPoly (f : Hex.ZPoly) : Lean.Meta.MetaM Expr := do
  Lean.Meta.mkAppM ``Hex.DensePoly.ofCoeffs
    #[arrayLit (mkConst ``Int) (f.toArray.toList.map toExpr)]

/-- Serialized view of a per-prime certificate block. -/
def primeFactorDataData (d : Hex.PrimeFactorData) :
    Nat × List Nat × List (List Nat) ×
      List (Nat × Nat × List (List Nat) × List (List Nat × List Nat)) :=
  match d with
  | { p := p, bounds := bounds, factorDegrees := degrees, factorPolys := polys,
      factorCerts := certs } =>
      (p, degrees.toList, polys.toList.map fun g => @fpCoeffNats p bounds g,
        certs.toList.map rabinCertData)

/-- Serialized view of a full integer irreducibility certificate. -/
def certificateData (cert : Hex.ZPolyIrreducibilityCertificate) :
    List (Nat × List Nat × List (List Nat) ×
        List (Nat × Nat × List (List Nat) × List (List Nat × List Nat))) ×
      List (Nat × Nat) :=
  (cert.perPrime.toList.map primeFactorDataData,
    cert.degreeObstructions.toList.map fun o => (o.targetDegree, o.primeIndex))

end Hex.CertReify
