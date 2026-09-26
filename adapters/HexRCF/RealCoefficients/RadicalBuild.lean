/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRCF.RealCoefficients.RadicalCheck
public import HexPoly.Euclid

public section

/-! Propose a radical certificate using the existing dense-polynomial gcd. -/

namespace Hex.RCF.RealCoefficients.RadicalCert

variable {E : Type u} {Ctx : Type v} [Zero E] [DecidableEq E]
variable [One E] [Add E] [Sub E] [Mul E] [Div E] [NatCast E] [DecidableEq Ctx]

private def candidate (context : Ctx) (core quotient : DensePoly E)
    (exponent : Nat) : RadicalCert E Ctx :=
  { context, core, quotient, exponent
    cofactor := (DensePoly.divMod
      (DensePoly.natPow core (exponent + 1)) quotient).1 }

private def search (context : Ctx) (product core quotient : DensePoly E) :
    List Nat → Option (RadicalCert E Ctx)
  | [] => none
  | exponent :: rest =>
      let cert := candidate context core quotient exponent
      if cert.check context product then some cert
      else search context product core quotient rest

omit [NatCast E] in
private theorem search_checked (context : Ctx) (product core quotient : DensePoly E)
    (steps : List Nat) (cert : RadicalCert E Ctx)
    (h : search context product core quotient steps = some cert) :
    cert.check context product = true := by
  induction steps with
  | nil => simp [search] at h
  | cons exponent rest ih =>
      let proposed := candidate context core quotient exponent
      by_cases hc : proposed.check context product = true
      · have heq : proposed = cert := by
          simpa [search, proposed, hc] using h
        subst cert
        exact hc
      · have hf : proposed.check context product = false := by
          cases hvalue : proposed.check context product <;> simp_all
        have hrest : search context product core quotient rest = some cert := by
          simpa [search, proposed, hf] using h
        exact ih hrest

/-- Quotient by the derivative gcd proposes a reduced core. A bounded search
then supplies the second radical identity. Only candidates accepted by the
literal checker are returned; failure makes no claim about the root set. -/
def build (context : Ctx) (product : DensePoly E) : Option (RadicalCert E Ctx) :=
  if product.isZero then none
  else
    let gcd := DensePoly.gcd product product.derivativeImpl
    let core := (DensePoly.divMod product gcd).1
    let quotient := (DensePoly.divMod product core).1
    search context product core quotient (List.range (product.natDegree + 1))

/-- A successful producer result is accepted by the exact replay checker. -/
theorem build_checked (context : Ctx) (product : DensePoly E)
    (cert : RadicalCert E Ctx) (h : build context product = some cert) :
    cert.check context product = true := by
  unfold build at h
  split at h
  · contradiction
  · exact search_checked context product _ _ _ cert h

end Hex.RCF.RealCoefficients.RadicalCert
