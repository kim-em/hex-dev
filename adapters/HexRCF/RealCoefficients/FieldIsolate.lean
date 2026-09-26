/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRCF.RealCoefficients.IsolationCheck

public section

/-! Propose ordered dyadic root intervals from the shared prepared Tarski query.
Every proposal is later checked by `IsolationReplay.build`; this search carries
no semantic proof obligation. -/

namespace Hex.RCF.RealCoefficients.FieldIsolate

variable {E : Type u} [Zero E] [DecidableEq E] [One E] [Add E] [Sub E]
  [Mul E] [NatCast E] [Neg E] [Inv E]

private def count? (sign : E → Int) (point : Dyadic → E)
    (head : DensePoly E) (total : TarskiCertificate E E Unit)
    (lower upper : Dyadic) : Option Int := do
  if !(decide (lower < upper)) || sign (head.eval (point lower)) == 0 ||
      sign (head.eval (point upper)) == 0 then
    none
  else
    some <| (TarskiCertificate.fromChains sign (EndpointSigns.ofSign sign) ()
      head 1 (.finite (point lower)) (.finite (point upper))
      total.squarefree total.remainders).value

private def bracket? (sign : E → Int) (point : Dyadic → E)
    (head : DensePoly E) (total : TarskiCertificate E E Unit) :
    Nat → Nat → Option (Dyadic × Dyadic)
  | 0, _ => none
  | fuel + 1, exponent =>
      let bound := Dyadic.ofInt ((2 : Int) ^ exponent)
      let lower := -bound
      match count? sign point head total lower bound with
      | some n =>
          if n == total.value then some (lower, bound)
          else bracket? sign point head total fuel (exponent + 1)
      | none => bracket? sign point head total fuel (exponent + 1)

private def pivot? (sign : E → Int) (point : Dyadic → E)
    (head : DensePoly E) (lower upper : Dyadic) : Nat → Option Dyadic
  | 0 => none
  | fuel + 1 =>
      let mid := (lower + upper) >>> (1 : Int)
      if decide (lower < mid) && decide (mid < upper) &&
          sign (head.eval (point mid)) != 0 then
        some mid
      else pivot? sign point head lower mid fuel

private def visit? (sign : E → Int) (point : Dyadic → E)
    (head : DensePoly E) (total : TarskiCertificate E E Unit) :
    Nat → Dyadic → Dyadic → Int → Option (List DyadicInterval)
  | _, _, _, 0 => some []
  | _, lower, upper, 1 =>
      if h : lower < upper then some [⟨lower, upper, h⟩] else none
  | 0, _, _, _ => none
  | fuel + 1, lower, upper, n => do
      if n < 0 then none
      else
        let mid ← pivot? sign point head lower upper (head.natDegree + 1)
        let left ← count? sign point head total lower mid
        let right ← count? sign point head total mid upper
        if left + right != n then none
        else
          let before ← visit? sign point head total fuel lower mid left
          let after ← visit? sign point head total fuel mid upper right
          some (before ++ after)

private def gap? (sign : E → Int) (point : Dyadic → E)
    (head : DensePoly E) (total : TarskiCertificate E E Unit)
    (left right : DyadicInterval) : Nat → Nat → Option (DyadicInterval × DyadicInterval)
  | 0, _ => none
  | fuel + 1, shift =>
      if left.upper < right.lower then some (left, right)
      else if left.upper != right.lower then none
      else
        let width := if left.width ≤ right.width then left.width else right.width
        let delta := width >>> (Int.ofNat shift)
        let upper := left.upper - delta
        let lower := right.lower + delta
        if hu : left.lower < upper then
          if hl : lower < right.upper then
            if count? sign point head total left.lower upper == some 1 &&
                count? sign point head total lower right.upper == some 1 then
              some (⟨left.lower, upper, hu⟩, ⟨lower, right.upper, hl⟩)
            else gap? sign point head total left right fuel (shift + 1)
          else gap? sign point head total left right fuel (shift + 1)
        else gap? sign point head total left right fuel (shift + 1)

private def separate? (sign : E → Int) (point : Dyadic → E)
    (head : DensePoly E) (total : TarskiCertificate E E Unit) :
    Nat → List DyadicInterval → Option (List DyadicInterval)
  | _, [] => some []
  | _, [single] => some [single]
  | 0, _ => none
  | fuel + 1, left :: right :: rest => do
      let (left', right') ← gap? sign point head total left right 64 2
      let tail ← separate? sign point head total fuel (right' :: rest)
      some (left' :: tail)

/-- A bounded bisection search over exact root counts. Failure leaves the
caller free to use another proposal strategy. -/
def propose? (sign : E → Int) (point : Dyadic → E)
    (head : DensePoly E) : Option IsolationCert :=
  match Sturm.prepare sign head .negInf .posInf with
  | none => none
  | some domain =>
      let total : TarskiCertificate E E Unit :=
        Sturm.certifyPrepared () domain (1 : DensePoly E)
      if total.value < 0 then none
      else if total.value == 0 then some ⟨#[]⟩
      else do
        let (lower, upper) ← bracket? sign point head total 32 0
        let intervals ← visit? sign point head total 128 lower upper total.value
        let intervals ← separate? sign point head total intervals.length intervals
        some ⟨intervals.toArray⟩

end Hex.RCF.RealCoefficients.FieldIsolate
