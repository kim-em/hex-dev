/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexBerlekampZassenhaus
public import Lean

public section

/-!
Elaboration-time reification of `Hex.ZPolyIrreducibilityCertificate` values as
literal `Expr`s, for the `irreducible_cert` tactic.

The reifier rebuilds every layer of the certificate tower from *public
constructor functions* rather than raw structure-field literals, so all proof
and instance obligations are supplied by the constructors themselves:

- `Hex.ZMod64 p` residues via `Hex.ZMod64.ofNat p n` (reduction proof from the
  smart constructor);
- `Hex.FpPoly p` values via `Hex.FpPoly.ofCoeffs #[…]` (normalization proof
  from the smart constructor);
- `Hex.ZPoly` values via `Hex.DensePoly.ofCoeffs #[…]`;
- `Hex.ZMod64.Bounds p` instance fields via `boundsOfDecide`, whose single
  Boolean hypothesis the kernel discharges by reducing an `Eq.refl true`;
- the structure layers (`RabinBezoutWitness`, `IrreducibilityCertificate`,
  `PrimeFactorData`, `DegreeObstruction`, `ZPolyIrreducibilityCertificate`)
  as constructor applications over the reified pieces.

Every emitted proof obligation is a `_ = true` slot filled with `Eq.refl true`,
so the kernel verifies the reified data by reduction alone; nothing in the
output depends on elaborator-side evaluation.

The round-trip tests live in `HexBerlekampZassenhausMathlib.IrreducibleCertTest`
next to the tactic examples: each reified certificate is typechecked,
evaluated back to a value, and compared field-by-field with the original.
-/

namespace HexBerlekampZassenhausMathlib.CertReify

open Lean

/--
Rebuild a `ZMod64.Bounds` instance from a single kernel-decidable Boolean
check. The reifier emits `boundsOfDecide p (Eq.refl true)` in every reified
instance slot, so the kernel discharges both bounds by reduction.
-/
theorem boundsOfDecide (p : Nat)
    (h : (decide (0 < p) && decide (p < 2 ^ 31)) = true) :
    Hex.ZMod64.Bounds p := by
  rw [Bool.and_eq_true] at h
  exact ⟨of_decide_eq_true h.1, of_decide_eq_true h.2⟩

/-- The literal proof `Eq.refl true`, accepted in any `b = true` slot whose
left-hand side the kernel can reduce to `true`. -/
def reflTrue : Expr :=
  mkApp2 (mkConst ``Eq.refl [Level.one]) (mkConst ``Bool) (mkConst ``Bool.true)

/-- Literal `Array` expression `(List.toArray [x₁, …, xₙ] : Array ty)`. -/
def arrayLit (ty : Expr) (xs : List Expr) : Expr :=
  let nil := mkApp (mkConst ``List.nil [Level.zero]) ty
  let listE := xs.foldr (fun x acc => mkApp3 (mkConst ``List.cons [Level.zero]) ty x acc) nil
  mkApp2 (mkConst ``List.toArray [Level.zero]) ty listE

/-- Reified `ZMod64.Bounds p` instance: `boundsOfDecide p (Eq.refl true)`. -/
def reifyBounds (pE : Expr) : Expr :=
  mkApp2 (mkConst ``boundsOfDecide) pE reflTrue

/-- The type `Hex.ZMod64 p` at a reified prime and bounds instance. -/
def zmodType (pE boundsE : Expr) : Expr :=
  mkApp2 (mkConst ``Hex.ZMod64) pE boundsE

/-- The type `Hex.FpPoly p` at a reified prime and bounds instance. -/
def fpPolyType (pE boundsE : Expr) : Expr :=
  mkApp2 (mkConst ``Hex.FpPoly) pE boundsE

/-- Reify a `ZMod64 p` residue from its canonical `Nat` representative as
`Hex.ZMod64.ofNat p n`. -/
def reifyZMod64 (pE boundsE : Expr) (n : Nat) : Expr :=
  mkApp3 (mkConst ``Hex.ZMod64.ofNat) pE (mkNatLit n) boundsE

/-- Reify an `FpPoly p` from the canonical `Nat` representatives of its
coefficients as `Hex.FpPoly.ofCoeffs #[…]`. -/
def reifyFpPolyOfNats (pE boundsE : Expr) (coeffs : List Nat) : Expr :=
  mkApp3 (mkConst ``Hex.FpPoly.ofCoeffs) pE boundsE
    (arrayLit (zmodType pE boundsE) (coeffs.map (reifyZMod64 pE boundsE)))

/-- Canonical `Nat` representatives of an `FpPoly p`'s coefficient array. -/
def fpCoeffNats {p : Nat} [Hex.ZMod64.Bounds p] (g : Hex.FpPoly p) : List Nat :=
  g.toArray.toList.map Hex.ZMod64.toNat

/-- Reify a `RabinBezoutWitness p` as a constructor application over reified
`FpPoly` values. -/
def reifyRabinWitness {p : Nat} [bounds : Hex.ZMod64.Bounds p]
    (pE boundsE : Expr) (w : Hex.Berlekamp.RabinBezoutWitness p) : Expr :=
  mkApp4 (mkConst ``Hex.Berlekamp.RabinBezoutWitness.mk) pE boundsE
    (reifyFpPolyOfNats pE boundsE (fpCoeffNats w.left))
    (reifyFpPolyOfNats pE boundsE (fpCoeffNats w.right))

/-- Reify a nested Rabin `IrreducibilityCertificate` as a constructor
application over its reified prime, pow chain, and Bezout witnesses. -/
def reifyRabinCert (cert : Hex.Berlekamp.IrreducibilityCertificate) : Expr :=
  match cert with
  | { p := p, bounds := bounds, n := n, powChain := powChain, bezout := bezout } =>
      let pE := mkNatLit p
      let boundsE := reifyBounds pE
      let powChainE := arrayLit (fpPolyType pE boundsE)
        (powChain.toList.map fun g =>
          reifyFpPolyOfNats pE boundsE (@fpCoeffNats p bounds g))
      let bezoutE := arrayLit
        (mkApp2 (mkConst ``Hex.Berlekamp.RabinBezoutWitness) pE boundsE)
        (bezout.toList.map fun w => @reifyRabinWitness p bounds pE boundsE w)
      mkApp5 (mkConst ``Hex.Berlekamp.IrreducibilityCertificate.mk)
        pE boundsE (mkNatLit n) powChainE bezoutE

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

/-! ### Serialized views for round-trip testing

The round-trip tests (in `HexBerlekampZassenhausMathlib.IrreducibleCertTest`)
evaluate a reified certificate back to a value and compare it with the
original. The certificate tower has no derivable `BEq` (its `FpPoly` fields
live at per-block primes), so the comparison goes through these canonical
serializations to plain `Nat` data.
-/

/-- Serialized view of a nested Rabin certificate. -/
def rabinCertData (cert : Hex.Berlekamp.IrreducibilityCertificate) :
    Nat × Nat × List (List Nat) × List (List Nat × List Nat) :=
  match cert with
  | { p := p, bounds := bounds, n := n, powChain := powChain, bezout := bezout } =>
      (p, n, powChain.toList.map fun g => @fpCoeffNats p bounds g,
        bezout.toList.map fun w =>
          (@fpCoeffNats p bounds w.left, @fpCoeffNats p bounds w.right))

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

end HexBerlekampZassenhausMathlib.CertReify
