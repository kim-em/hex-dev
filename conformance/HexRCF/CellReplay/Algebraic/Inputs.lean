/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import HexRCF.CellReplay.Algebraic.Schema
import HexRCF.CellReplay.Algebraic.Literals
import HexRCF.RealCoefficients.RowOperations
namespace Hex.RCF.RealCoefficients.CellReplayTests.Algebraic.Inputs
open Hex Hex.RealClosure Hex.RealClosure.Tower Hex.SignDet
open Hex.RCF.SelectedRootTests Hex.RCF.RealCoefficients
open Schema
def polynomialAt (facts : List (Algebraic.SignFact Data.native)) : parent.Poly :=
  @RepresentationSpecialize.polynomial parent.Value _ _
    (Algebraic.Element.cachedOne Data.reduction Data.reduction_eq facts)
    (Algebraic.Element.cachedAdd Data.reduction Data.reduction_eq facts)
    (Algebraic.Element.cachedMul Data.reduction Data.reduction_eq facts)
    (Algebraic.Element.cachedNeg Data.reduction Data.reduction_eq facts)
    (Algebraic.Element.cachedNatCast Data.reduction Data.reduction_eq facts) _ values atom

def queriesAt (facts : List (Algebraic.SignFact Data.native)) : List parent.Poly :=
  @RepresentationSpecialize.prepare parent.Value _ _
    (Algebraic.Element.cachedOne Data.reduction Data.reduction_eq facts)
    (Algebraic.Element.cachedAdd Data.reduction Data.reduction_eq facts)
    (Algebraic.Element.cachedMul Data.reduction Data.reduction_eq facts)
    (Algebraic.Element.cachedNeg Data.reduction Data.reduction_eq facts)
    (Algebraic.Element.cachedNatCast Data.reduction Data.reduction_eq facts) _ values formula

def tableAt (facts : List (Algebraic.SignFact Data.native)) :=
  @RootTable.read parent.Value Signature _ _ _
    (Algebraic.Element.cachedOne Data.reduction Data.reduction_eq facts)
    (Algebraic.Element.cachedAdd Data.reduction Data.reduction_eq facts)
    (Algebraic.Element.cachedSub Data.reduction Data.reduction_eq facts)
    (Algebraic.Element.cachedMul Data.reduction Data.reduction_eq facts)
    (Algebraic.Element.cachedNatCast Data.reduction Data.reduction_eq facts)
    (Algebraic.Element.signCodec Data.base.codec facts) Signature.codec parent.sign parent.signature []
    (Inputs.polynomialAt facts) .negInf .posInf Literals.roots

end Hex.RCF.RealCoefficients.CellReplayTests.Algebraic.Inputs
