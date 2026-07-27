/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexNumberFieldTower.Arithmetic
public meta import HexNumberFieldTower.Arithmetic

public section

/-!
# Checked tower embeddings

The rational smart constructor builds a one-level tower from a checked
irreducible integer polynomial and a selected refined isolation. Its defining
relation is the monic rational associate of that polynomial, and its generator
uses the same absolute root after harmless global-sign normalization.
-/
namespace Hex.NumberTower

/-! Compiled one-level embedding checks. -/

private def embedSqrtTwoPoly : ZPoly := DensePoly.ofList [-2, 0, 1]

private def embedSqrtTwoSquare : DyadicSquare :=
  ⟨Dyadic.ofIntWithPrec 181 7, 0, 8⟩

private def embedSqrtTwoRep : RefinedIsolation embedSqrtTwoPoly :=
  ⟨⟨embedSqrtTwoSquare, by decide⟩, by decide⟩

private def embedSqrtTwoRoot : SimpleRoot embedSqrtTwoPoly :=
  SimpleRoot.mk embedSqrtTwoRep

#guard
    if hirred : ZPoly.isIrreducible embedSqrtTwoPoly = true then
      letI : ZPoly.CheckedIrreducible embedSqrtTwoPoly :=
        ⟨hirred, by decide⟩
      if hsimple : HasOnlySimpleRoots embedSqrtTwoPoly then
        let extension := ofQAdjoin (x := embedSqrtTwoRoot)
          hsimple embedSqrtTwoRep rfl
        extension.tower.dim = 2 && extension.tower.height = 1 &&
          coeffs (extension.gen * extension.gen) = #[2, 0] &&
          coeffs (extension.gen⁻¹) = #[0, 1 / 2] &&
          coeffs (extension.embed (ofRat rat 3)) = #[3, 0] &&
          extension.root.p = embedSqrtTwoPoly
      else
        false
    else
      false

-- A negative-leading presentation exercises the constructor's sign
-- normalization while retaining the same monic quotient relation.
private def embedNegSqrtTwoPoly : ZPoly := DensePoly.ofList [2, 0, -1]

private def embedNegSqrtTwoRep : RefinedIsolation embedNegSqrtTwoPoly :=
  ⟨⟨embedSqrtTwoSquare, by decide⟩, by decide⟩

private def embedNegSqrtTwoRoot : SimpleRoot embedNegSqrtTwoPoly :=
  SimpleRoot.mk embedNegSqrtTwoRep

#guard
    if hirred : ZPoly.isIrreducible embedNegSqrtTwoPoly = true then
      letI : ZPoly.CheckedIrreducible embedNegSqrtTwoPoly :=
        ⟨hirred, by decide⟩
      if hsimple : HasOnlySimpleRoots embedNegSqrtTwoPoly then
        let extension := ofQAdjoin (x := embedNegSqrtTwoRoot)
          hsimple embedNegSqrtTwoRep rfl
        extension.root.p = embedSqrtTwoPoly &&
          coeffs (extension.gen * extension.gen) = #[2, 0]
      else
        false
    else
      false

end Hex.NumberTower
