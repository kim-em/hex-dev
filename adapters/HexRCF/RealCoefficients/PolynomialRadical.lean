/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRCF.RealCoefficients.PolynomialBounds
public import HexRCF.RealCoefficients.RadicalCheck
public import HexMvGcd
public section

namespace Hex.RCF.RealCoefficients.PolynomialRadical
open Hex PolynomialBounds

/-- Propose a root-preserving reduction using the owner's multivariate gcd.
The complete coefficient content in the quantified mainVar is retained:
removing its multiplicities would violate the certificate's degree bound.
Only exact identities accepted by the existing replay checker are returned. -/
def build {Ctx : Type u} [DecidableEq Ctx] (context : Ctx)
    (product : DensePoly (Poly n)) : Option (RadicalCert (Poly n) Ctx) :=
  if product.isZero then none else
    let mainVar := Fin.last n
    let flat := MvPoly.ofUnivariate (cmp := Mono.lex) mainVar Mono.lex product
    let content := MvPoly.contentIn mainVar Mono.lex flat
    let primitive := MvPoly.primPartIn mainVar Mono.lex flat
    let core := MvPoly.constIn (cmp := Mono.lex) mainVar Mono.lex content * MvPoly.radical primitive
    match MvPoly.divExact? flat core with
    | none => none
    | some quotient =>
      match MvPoly.divExact? (Mono.powBySq core (product.natDegree + 1)) quotient with
      | none => none
      | some cofactor =>
        let cert : RadicalCert (Poly n) Ctx := {
          context
          core := MvPoly.toUnivariate mainVar Mono.lex core
          quotient := MvPoly.toUnivariate mainVar Mono.lex quotient
          cofactor := MvPoly.toUnivariate mainVar Mono.lex cofactor
          exponent := product.natDegree }
        if cert.check context product then some cert else none

/-- Native proposal success entails the same literal identities used in replay.
Frozen proof construction uses the certificate, not this producer theorem. -/
theorem build_checked {Ctx : Type u} [DecidableEq Ctx] (context : Ctx)
    (product : DensePoly (Poly n)) (cert : RadicalCert (Poly n) Ctx)
    (produced : build context product = some cert) : cert.check context product = true := by
  unfold build at produced
  split at produced
  · contradiction
  · dsimp only at produced
    split at produced
    · contradiction
    · split at produced
      · contradiction
      · split at produced
        · cases Option.some.inj produced
          assumption
        · contradiction

end Hex.RCF.RealCoefficients.PolynomialRadical
