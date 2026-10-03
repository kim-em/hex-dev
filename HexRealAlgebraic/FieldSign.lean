/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRealAlgebraic.Order
public import HexNumberField.Convert
public import HexNumberField.Roots

public section

namespace Hex.RealAlgebraicNumber

/-- A disc separated from the imaginary axis fixes the sign of its real part. -/
@[expose] def ballSign? (ball : DyadicComplexBall) : Option Int :=
  if ball.radius < ball.re then some 1
  else if ball.re < -ball.radius then some (-1)
  else none

namespace FieldSign

/-- Read the existing enclosure with a minimum of sixteen coefficient bits. -/
@[expose] def initial? (generator : RealAlgebraicNumber)
    (value : QAdjoin generator.toAlgebraic) : Option Int :=
  let rep := generator.toAlgebraic.rep
  ballSign? (PolyQuot.evalRatBall value.coeffs rep.1.square
    (Max.max (16 : Int) rep.1.square.prec))

/-- A modest absolute-precision probe before constructing an evaluation eliminant. -/
@[expose] def refined? (generator : RealAlgebraicNumber)
    (value : QAdjoin generator.toAlgebraic) : Option Int :=
  ballSign? (value.approx generator.toAlgebraic.rep generator.toAlgebraic.rep_mk 32).2

/-- An integer polynomial vanishing at the selected coordinate value. -/
@[expose] def eliminant (generator : RealAlgebraicNumber)
    (value : QAdjoin generator.toAlgebraic) : ZPoly :=
  PolyQuot.Roots.normEliminant (DensePoly.ofList [-value, 1])

/-- The finite reciprocal-Cauchy endpoint for the existing guarded approximation. -/
@[expose] def endpoint? (generator : RealAlgebraicNumber)
    (value : QAdjoin generator.toAlgebraic) : Option Int :=
  let precision := evalDisambiguationLimit (eliminant generator value) 1
  ballSign? (value.approx generator.toAlgebraic.rep generator.toAlgebraic.rep_mk
    (precision : Int)).2

end FieldSign

/-- Decide a real field coordinate using its existing generator enclosure.
Only inconclusive probes refine the generator. The final probe uses a finite
precision derived from an evaluation eliminant, without canonical conversion. -/
@[expose] def signField (generator : RealAlgebraicNumber)
    (value : QAdjoin generator.toAlgebraic) : Int :=
  let polynomial := value.coeffs
  if polynomial.size ≤ 1 then
    let q := polynomial.coeff 0
    if q < 0 then -1 else if q = 0 then 0 else 1
  else
    match FieldSign.initial? generator value with
    | some sign => sign
    | none =>
      match FieldSign.refined? generator value with
      | some sign => sign
      | none =>
        match FieldSign.endpoint? generator value with
        | some sign => sign
        | none => Hex.panicWith 0 "signField: finite precision endpoint failed"

end Hex.RealAlgebraicNumber
