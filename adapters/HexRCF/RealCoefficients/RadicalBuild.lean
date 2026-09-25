/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRCF.RealCoefficients.RadicalCheck
public import HexPoly.Euclid

public section

/-! Propose a squarefree root carrier using ordinary coefficient division. -/

namespace Hex.RCF.RealCoefficients.RadicalBuild

open Hex

/-- Remove repeated factors by a polynomial gcd. The checker verifies both
root-preserving identities and rejects nonzero remainders; the later prepared
Sturm domain independently verifies that the proposed core is squarefree. -/
def build {E : Type u} {Ctx : Type v} [Zero E] [One E] [Add E] [Sub E]
    [Mul E] [NatCast E] [Div E] [DecidableEq E] [DecidableEq Ctx]
    (context : Ctx) (product : DensePoly E) : Option (RadicalCert E Ctx) :=
  let repeated := DensePoly.gcd product product.derivativeImpl
  let core := product / repeated
  let quotient := repeated
  let exponent := product.natDegree
  let cofactor := DensePoly.natPow core (exponent + 1) / quotient
  let cert : RadicalCert E Ctx := ⟨context, core, quotient, cofactor, exponent⟩
  if cert.check context product then some cert else none

/-- A successful proposal satisfies the actual root-preserving replay check. -/
theorem build_checked {E : Type u} {Ctx : Type v} [Zero E] [One E] [Add E]
    [Sub E] [Mul E] [NatCast E] [Div E] [DecidableEq E] [DecidableEq Ctx]
    (context : Ctx) (product : DensePoly E) (cert : RadicalCert E Ctx)
    (h : build context product = some cert) :
    cert.check context product = true := by
  unfold build at h
  dsimp only at h
  split at h
  · next hc =>
      cases Option.some.inj h
      exact hc
  · simp at h

end Hex.RCF.RealCoefficients.RadicalBuild
