/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import HexRCF.BoundedSource.Positive
import HexRCF.BoundedSource.Negative
import HexRCF.BoundedSource.Cubic
import HexRCF.SourceIdentityCases
import HexRCF.RealCoefficients.CubeTwo
import HexRCF.RealCoefficients.ScalarPacket

namespace Hex.RCF.BoundedSourceInputs
open Hex Hex.RealClosure Hex.SignDet Hex.RCF.RealCoefficients
open Hex.RCF.SelectedRootTests Hex.RCF.SourceIdentityCases
set_option maxRecDepth 32768
set_option maxHeartbeats 12000000

theorem positiveWitness : atomWitness SquareTwo.polynomial SquareTwo.square := by decide +kernel
theorem positivePrecision : (mahlerPrec SquareTwo.polynomial : Int) ≤ SquareTwo.square.prec := by decide +kernel
theorem cubicWitness : atomWitness CubeTwo.polynomial CubeTwo.square := by decide +kernel
theorem cubicPrecision : (mahlerPrec CubeTwo.polynomial : Int) ≤ CubeTwo.square.prec := by decide +kernel
theorem cubicSelected :
    (Field.literalRep CubeTwo.polynomial CubeTwo.square cubicWitness cubicPrecision).root.re =
      (2 : ℝ) ^ (1 / 3 : ℝ) :=
  (CubeTwo.coordinate_value _ _ _).symm.trans (CubeTwo.value _ _ _ (by decide +kernel))

private theorem value (literal : Codec.Json) (q : DensePoly Rat)
    (same : ScalarPacket.key Data.base.codec literal = embed q) :
    HexPolyTheory.Interpret.interpret Data.rational.value Data.rational.zero_iff
      (ScalarPacket.key Data.base.codec literal) = LiteralSign.realPoly q := by
  rw [same]
  exact embed_value q

theorem positiveEquation :
    HexPolyTheory.Interpret.interpret Data.rational.value Data.rational.zero_iff
      (ScalarPacket.key Data.base.codec BoundedSource.Positive.equation) =
      LiteralSign.realPoly (ZPoly.toRatPoly SquareTwo.polynomial) :=
  value _ _ (by decide +kernel)
theorem positiveMargin :
    HexPolyTheory.Interpret.interpret Data.rational.value Data.rational.zero_iff
      (ScalarPacket.key Data.base.codec BoundedSource.Positive.margin) =
      LiteralSign.realPoly (SourceIdentity.margin SquareTwo.square) :=
  value _ _ (by decide +kernel)
theorem negativeEquation :
    HexPolyTheory.Interpret.interpret Data.rational.value Data.rational.zero_iff
      (ScalarPacket.key Data.base.codec BoundedSource.Negative.equation) =
      LiteralSign.realPoly (ZPoly.toRatPoly SquareTwo.polynomial) :=
  value _ _ (by decide +kernel)
theorem negativeMargin :
    HexPolyTheory.Interpret.interpret Data.rational.value Data.rational.zero_iff
      (ScalarPacket.key Data.base.codec BoundedSource.Negative.margin) =
      LiteralSign.realPoly (SourceIdentity.margin negativeSquare) :=
  value _ _ (by decide +kernel)
theorem cubicEquation :
    HexPolyTheory.Interpret.interpret Data.rational.value Data.rational.zero_iff
      (ScalarPacket.key Data.base.codec BoundedSource.Cubic.equation) =
      LiteralSign.realPoly (ZPoly.toRatPoly CubeTwo.polynomial) :=
  value _ _ (by decide +kernel)
theorem cubicMargin :
    HexPolyTheory.Interpret.interpret Data.rational.value Data.rational.zero_iff
      (ScalarPacket.key Data.base.codec BoundedSource.Cubic.margin) =
      LiteralSign.realPoly (SourceIdentity.margin CubeTwo.square) :=
  value _ _ (by decide +kernel)
end Hex.RCF.BoundedSourceInputs
