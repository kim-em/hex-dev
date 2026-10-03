/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRealAlgebraic.Order
public import HexNumberField.Convert

public section

namespace Hex.RealAlgebraicNumber

/-- A disc separated from the imaginary axis fixes the sign of its real part. -/
@[expose] def ballSign? (ball : DyadicComplexBall) : Option Int :=
  if ball.radius < ball.re then some 1
  else if ball.re < -ball.radius then some (-1)
  else none

/-- Decide a real field coordinate using its existing generator enclosure.
Only an inconclusive probe refines the generator. The canonical conversion
remains the exact fallback when both finite probes are inconclusive. -/
@[expose] def signField (generator : RealAlgebraicNumber)
    (value : QAdjoin generator.toAlgebraic) : Int :=
  let polynomial := value.coeffs
  if polynomial.size ≤ 1 then
    let q := polynomial.coeff 0
    if q < 0 then -1 else if q = 0 then 0 else 1
  else
    let representative := generator.toAlgebraic.rep
    let precision := Max.max (16 : Int) representative.1.square.prec
    match ballSign? (PolyQuot.evalRatBall polynomial representative.1.square precision) with
    | some sign => sign
    | none =>
      match ballSign? (value.approx representative generator.toAlgebraic.rep_mk 32).2 with
      | some sign => sign
      | none =>
        match ofAlgebraic? value.toAlgebraicNumber with
        | some result => result.sign
        | none => Hex.panicWith 0 "signField: nonreal coordinate of a real generator"

end Hex.RealAlgebraicNumber
