/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexDet.Basic
public import HexDet.Field
public import HexResultant.ExactDiv
public import HexMvGcd.Instances

public section

/-!
Dense-polynomial recipes.

A dense polynomial over a coefficient ring with an exact quotient has one
itself, by the recursive division `Hex.instExactDivLawsDensePoly` supplies. Those
carriers select Bareiss through `Hex.exactDiv`, which divides by nonconstant
pivots exactly.

One instance covers the whole dense-polynomial row: `Hex.DensePoly F` at the
supported fields, and `Hex.ZPoly`, which is `Hex.DensePoly Int` and so shares it
rather than receiving a second recipe through the alias. Decidable equality is
needed even on this division-free route, because the executable polynomial
representation is normalized.

The executable finite-field polynomials reach this recipe through the
coefficient instances their own libraries supply: `Hex.instCommRingFpPoly` from
`HexMvGcd`, and the exactness of the residue division from `HexDet.Field`.
-/

namespace Hex.Det

universe u

/-- Exactness of the recursive polynomial division over prime residues, restated
at the canonical coefficient `Zero`. `Hex.FpPoly p` spells its coefficient `Zero`
as `HexModArith`'s, while the generic dense-polynomial instances spell it through
the lightweight ring, and instance search does not unfold between them. -/
instance instExactDivLawsFpPoly {p : Nat} [ZMod64.Bounds p] [ZMod64.PrimeModulus p] :
    Hex.ExactDivLaws (FpPoly p) :=
  Hex.instExactDivLawsDensePoly (R := ZMod64 p)

/-- The dense-polynomial recipe: Bareiss over the recursive exact quotient. -/
instance instDetOpsDensePoly {R : Type u} [Lean.Grind.CommRing R] [DecidableEq R]
    [Div R] [Hex.ExactDivLaws R] : DetOps (DensePoly R) where
  policy := quotientPolicy

-- Pin the selected recipe: a missing coefficient instance would silently fall
-- back to the Berkowitz default rather than fail to resolve. `Hex.ZPoly` is this
-- instance at `Int`, and the alias adds no second recipe.
example : (DetOps.policy (R := DensePoly Rat)).arm = Arm.bareiss := rfl

example : (DetOps.policy (R := DensePoly Int)).arm = Arm.bareiss := rfl

/-- The same recipe at `Hex.FpPoly p`, which instance search reaches only when
the coefficient `Zero` is spelled the way that type spells it. This is literally
`instDetOpsDensePoly` at `Hex.ZMod64 p`, restated at that spelling, so the two
paths cannot drift apart. -/
instance instDetOpsFpPoly {p : Nat} [ZMod64.Bounds p] [ZMod64.PrimeModulus p] :
    DetOps (FpPoly p) :=
  instDetOpsDensePoly (R := ZMod64 p)

example {p : Nat} [ZMod64.Bounds p] [ZMod64.PrimeModulus p] :
    (DetOps.policy (R := FpPoly p)).arm = Arm.bareiss := rfl

end Hex.Det
