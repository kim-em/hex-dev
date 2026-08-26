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
  ⟨⟨embedSqrtTwoSquare, .ofWitness (by decide)⟩, by decide⟩

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
          extension.root.p = embedSqrtTwoPoly &&
          extension.root.rep.1.square = embedSqrtTwoSquare
      else
        false
    else
      false

-- A negative-leading presentation exercises the constructor's sign
-- normalization while retaining the same monic quotient relation.
private def embedNegSqrtTwoPoly : ZPoly := DensePoly.ofList [2, 0, -1]

private def embedNegSqrtTwoRep : RefinedIsolation embedNegSqrtTwoPoly :=
  ⟨⟨embedSqrtTwoSquare, .ofWitness (by decide)⟩, by decide⟩

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
          extension.root.rep.1.square = embedSqrtTwoSquare &&
          coeffs (extension.gen * extension.gen) = #[2, 0]
      else
        false
    else
      false

-- The negative conjugate must stay negative; quotient arithmetic alone cannot
-- distinguish this fixed embedding from the positive-root presentation.
private def embedNegRootSquare : DyadicSquare :=
  ⟨Dyadic.ofIntWithPrec (-181) 7, 0, 8⟩

private def embedNegRootRep : RefinedIsolation embedSqrtTwoPoly :=
  ⟨⟨embedNegRootSquare, .ofWitness (by decide)⟩, by decide⟩

private def embedNegRoot : SimpleRoot embedSqrtTwoPoly :=
  SimpleRoot.mk embedNegRootRep

#guard
    if hirred : ZPoly.isIrreducible embedSqrtTwoPoly = true then
      letI : ZPoly.CheckedIrreducible embedSqrtTwoPoly :=
        ⟨hirred, by decide⟩
      if hsimple : HasOnlySimpleRoots embedSqrtTwoPoly then
        let extension := ofQAdjoin (x := embedNegRoot)
          hsimple embedNegRootRep rfl
        extension.root.rep.1.square = embedNegRootSquare &&
          extension.root.rep.1.square != embedSqrtTwoSquare
      else
        false
    else
      false

-- A rational root is already in the base tower and must not create a second,
-- height-one representation of `ℚ`.
private def embedThreeHalvesPoly : ZPoly := DensePoly.ofList [-3, 2]

private def embedThreeHalvesSquare : DyadicSquare :=
  ⟨Dyadic.ofIntWithPrec 3 1, 0, 8⟩

private def embedThreeHalvesRep : RefinedIsolation embedThreeHalvesPoly :=
  ⟨⟨embedThreeHalvesSquare, .ofWitness (by decide)⟩, by decide⟩

private def embedThreeHalvesRoot : SimpleRoot embedThreeHalvesPoly :=
  SimpleRoot.mk embedThreeHalvesRep

#guard
    if hirred : ZPoly.isIrreducible embedThreeHalvesPoly = true then
      letI : ZPoly.CheckedIrreducible embedThreeHalvesPoly :=
        ⟨hirred, by decide⟩
      if hsimple : HasOnlySimpleRoots embedThreeHalvesPoly then
        let extension := ofQAdjoin (x := embedThreeHalvesRoot)
          hsimple embedThreeHalvesRep rfl
        extension.tower.height = 0 && extension.tower.dim = 1 &&
          coeffs extension.gen = #[3 / 2] &&
          coeffs (extension.embed (ofRat rat 7)) = #[7]
      else
        false
    else
      false

-- Non-unit leading coefficients exercise the rational monic normalization,
-- not merely the global-sign case.
private def embedSqrtThreeHalvesPoly : ZPoly :=
  DensePoly.ofList [-3, 0, 2]

private def embedSqrtThreeHalvesSquare : DyadicSquare :=
  ⟨Dyadic.ofIntWithPrec 157 7, 0, 9⟩

private def embedSqrtThreeHalvesRep :
    RefinedIsolation embedSqrtThreeHalvesPoly :=
  ⟨⟨embedSqrtThreeHalvesSquare, .ofWitness (by decide)⟩, by decide⟩

private def embedSqrtThreeHalvesRoot :
    SimpleRoot embedSqrtThreeHalvesPoly :=
  SimpleRoot.mk embedSqrtThreeHalvesRep

#guard
    if hirred : ZPoly.isIrreducible embedSqrtThreeHalvesPoly = true then
      letI : ZPoly.CheckedIrreducible embedSqrtThreeHalvesPoly :=
        ⟨hirred, by decide⟩
      if hsimple : HasOnlySimpleRoots embedSqrtThreeHalvesPoly then
        let extension := ofQAdjoin (x := embedSqrtThreeHalvesRoot)
          hsimple embedSqrtThreeHalvesRep rfl
        extension.root.rep.1.square = embedSqrtThreeHalvesSquare &&
          coeffs (extension.gen * extension.gen) = #[3 / 2, 0]
      else
        false
    else
      false

end Hex.NumberTower
