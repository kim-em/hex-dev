/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRCF.RealCoefficients.IsolationCheck
public import HexRealAlgebraic.Roots
public import HexRealAlgebraic.Laws

public section

namespace Hex.RCF.RealCoefficients

/-- Enclose a canonical real algebraic value with a strict dyadic margin.
The extra unit also gives exact rational roots nonzero-width intervals. -/
def rootInterval (root : RealAlgebraicNumber) (precision : Nat) : Option DyadicInterval :=
  let ball := root.approxBall precision
  let margin := Dyadic.ofInt 1 >>> (precision : Int)
  let lower := ball.re - ball.radius - margin
  let upper := ball.re + ball.radius + margin
  if h : lower < upper then some ⟨lower, upper, h⟩ else none

/-- Use the existing algebraic root solver to propose ordinary real cells.
This is a search result: callers must check coverage, counts and separation. -/
def proposeIsolations [RealAlgebraicNumber.Laws]
    (head : DensePoly RealAlgebraicNumber) (precision : Nat) : Option IsolationCert := do
  let roots ← (RealAlgebraicPoly.ofArray head.toArray).roots.finite?
  let intervals ← roots.mapM fun r => rootInterval r.root precision
  return ⟨intervals⟩

/-- Certify the existing solver's proposals at one requested precision.
A failed attempt does not assert that no roots exist; the caller may refine
precision. Replay checks recorded chains and never invokes this search. -/
def isolateAt [RealAlgebraicNumber.Laws] {Ctx : Type u} [DecidableEq Ctx]
    (context : Ctx) (head : DensePoly RealAlgebraicNumber) (precision : Nat) :
    Option (IsolationReplay RealAlgebraicNumber Ctx) :=
  match proposeIsolations head precision with
  | none => none
  | some isolations => IsolationReplay.build RealAlgebraicNumber.sign
      (fun d => RealAlgebraicNumber.ofRat d.toRat) context head isolations

/-- Every successful attempt supplies evidence accepted by the actual generic
isolation checker, independently of the root solver's implementation. -/
theorem isolateAt_checked [RealAlgebraicNumber.Laws] {Ctx : Type u} [DecidableEq Ctx]
    (context : Ctx) (head : DensePoly RealAlgebraicNumber) (precision : Nat)
    (cert : IsolationReplay RealAlgebraicNumber Ctx)
    (h : isolateAt context head precision = some cert) :
    cert.check RealAlgebraicNumber.sign (fun d => RealAlgebraicNumber.ofRat d.toRat)
      context head = true := by
  unfold isolateAt at h
  split at h
  · contradiction
  · exact (IsolationReplay.build_checked _ _ _ _ _ _ h).2

end Hex.RCF.RealCoefficients
