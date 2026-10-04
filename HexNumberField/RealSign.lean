/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexNumberField.Nearest
public import HexNumberField.Convert
public import HexNumberField.Roots

public section

namespace Hex.QAdjoin

/-- A disc separated from the imaginary axis fixes the sign of its real part. -/
@[expose] def ballSign? (ball : DyadicComplexBall) : Option Int :=
  if ball.radius < ball.re then some 1
  else if ball.re < -ball.radius then some (-1)
  else none

namespace SignApprox

/-- Read the existing enclosure with a minimum of sixteen coefficient bits. -/
@[expose] def initial? (generator : AlgebraicNumber)
    (value : QAdjoin generator) : Option Int :=
  let rep := generator.rep
  ballSign? (PolyQuot.evalRatBall value.coeffs rep.1.square
    (Max.max (16 : Int) rep.1.square.prec))

/-- A modest absolute-precision probe before constructing an evaluation eliminant. -/
@[expose] def refined? (generator : AlgebraicNumber)
    (value : QAdjoin generator) : Option Int :=
  ballSign? (value.approx generator.rep generator.rep_mk 32).2

/-- An integer polynomial vanishing at the selected coordinate value. -/
@[expose] def eliminant (generator : AlgebraicNumber)
    (value : QAdjoin generator) : ZPoly :=
  PolyQuot.Roots.normEliminant (DensePoly.ofList [-value, 1])

/-- The finite reciprocal-Cauchy endpoint. Approximation guard bits already absorb
Horner error amplification, so the output-radius majorant is one. -/
@[expose] def endpoint? (generator : AlgebraicNumber)
    (value : QAdjoin generator) : Option Int :=
  let precision := evalDisambiguationLimit (eliminant generator value) 1
  ballSign? (value.approx generator.rep generator.rep_mk
    (precision : Int)).2

end SignApprox

/-- Checked sign in the generator's real embedding; reject nonreal generators. -/
@[expose] def signApprox? {generator : AlgebraicNumber}
    (value : QAdjoin generator) : Option Int :=
  if generator.isReal then
    let polynomial := value.coeffs
    if polynomial.size ≤ 1 then
      let q := polynomial.coeff 0
      some (if q < 0 then -1 else if q = 0 then 0 else 1)
    else
      match SignApprox.initial? generator value with
      | some sign => some sign
      | none =>
        match SignApprox.refined? generator value with
        | some sign => some sign
        | none => SignApprox.endpoint? generator value
  else none

/-- Total sign for a real generator. The companion proves the fallback unreachable. -/
@[expose] def signApprox {generator : AlgebraicNumber}
    (value : QAdjoin generator) (_real : generator.isReal = true) : Int :=
  (signApprox? value).getD (Hex.panicWith 0 "signApprox: finite precision endpoint failed")

end Hex.QAdjoin

namespace Hex
/-- Interpret an integer sign as comparison with zero. -/
@[expose] def orderOfSign (sign : Int) : Ordering := compare sign 0
end Hex
