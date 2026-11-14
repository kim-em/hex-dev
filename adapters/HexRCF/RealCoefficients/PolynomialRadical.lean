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

private def candidate {Ctx : Type u} [DecidableEq Ctx] (context : Ctx)
    (product : DensePoly (Poly n)) (core quotient : Poly (n + 1)) (exponent : Nat) :
    Option (RadicalCert (Poly n) Ctx) :=
  match MvPoly.divExact? (Mono.powBySq core (exponent + 1)) quotient with
  | none => none
  | some cofactor =>
    let cert : RadicalCert (Poly n) Ctx := {
      context
      core := MvPoly.toUnivariate (Fin.last n) Mono.lex core
      quotient := MvPoly.toUnivariate (Fin.last n) Mono.lex quotient
      cofactor := MvPoly.toUnivariate (Fin.last n) Mono.lex cofactor
      exponent }
    if cert.check context product then some cert else none

private theorem candidate_checked {Ctx : Type u} [DecidableEq Ctx] (context : Ctx)
    (product : DensePoly (Poly n)) (core quotient : Poly (n + 1)) (exponent : Nat)
    (cert : RadicalCert (Poly n) Ctx)
    (produced : candidate context product core quotient exponent = some cert) :
    cert.check context product = true := by
  unfold candidate at produced
  split at produced
  · contradiction
  · dsimp only at produced
    split at produced
    · cases Option.some.inj produced
      assumption
    · contradiction

/-- Propose a root-preserving reduction using the owner's multivariate gcd.
The complete coefficient content in the quantified variable is retained.
Search from the smallest exponent; squarefree products need only exponent zero.
Only identities accepted by the existing replay checker are returned. -/
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
      (List.range (product.natDegree + 1)).findSome? (candidate context product core quotient)

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
    · obtain ⟨exponent, _, found⟩ := List.exists_of_findSome?_eq_some produced
      exact candidate_checked context product _ _ exponent cert found

end Hex.RCF.RealCoefficients.PolynomialRadical
