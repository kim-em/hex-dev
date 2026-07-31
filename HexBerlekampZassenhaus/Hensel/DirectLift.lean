/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexBerlekampZassenhaus.Modular.PrimePlan

public section
set_option backward.proofsInPublic true

/-!
# One direct-coordinate Hensel lift
-/

namespace Hex

/-- Validated recovery precision for one direct modular plan. There is no
`B = 0` meaning: construction fixes the ordinary Mignotte recovery bound and
the corresponding positive Hensel exponent. -/
structure DirectLiftPlan
    (core : SquareFreeInput) (modular : DirectPrimePlan core) where
deriving DecidableEq

namespace DirectLiftPlan

/-- The unique recovery plan indexed by a square-free part and its selected modular
factorization. -/
@[expose]
def canonical (core : SquareFreeInput) (modular : DirectPrimePlan core) :
    DirectLiftPlan core modular :=
  ⟨⟩

/-- Ordinary direct Mignotte coefficient bound. -/
@[expose]
def coeffBound {core : SquareFreeInput} {modular : DirectPrimePlan core}
    (_plan : DirectLiftPlan core modular) : Nat :=
  ZPoly.defaultFactorCoeffBound core.poly

/-- Recovery precision derived from the indexed polynomial, bound, and prime. -/
@[expose]
def precision {core : SquareFreeInput} {modular : DirectPrimePlan core}
    (plan : DirectLiftPlan core modular) : Nat :=
  precisionForCoeffBound plan.coeffBound modular.data.p

end DirectLiftPlan

/-- Token for the one direct-coordinate Hensel lift owned by a lift plan.
The lifted data is derived from the indices rather than stored, so a basis
from another square-free part or precision cannot be inserted. -/
structure DirectLiftedBasis
    {core : SquareFreeInput} {modular : DirectPrimePlan core}
    (plan : DirectLiftPlan core modular) where

namespace DirectLiftedBasis

/-- Construct the unique basis token for a recovery plan. -/
@[expose]
def canonical {core : SquareFreeInput} {modular : DirectPrimePlan core}
    (plan : DirectLiftPlan core modular) : DirectLiftedBasis plan :=
  ⟨⟩

/-- Execute the lift determined by the indexed recovery plan. -/
@[expose]
def data {core : SquareFreeInput} {modular : DirectPrimePlan core}
    {plan : DirectLiftPlan core modular}
    (_basis : DirectLiftedBasis plan) : LiftData :=
  ZPoly.directLiftData core.poly plan.coeffBound modular.data

end DirectLiftedBasis

/-- Stable identity of a factor in the one direct lifted basis. -/
abbrev DirectLiftedIndex (basis : LiftData) : Type :=
  Fin basis.liftedFactors.size

/-- Fetch a lifted factor by its stable basis index. -/
@[expose]
def directLiftedFactor (basis : LiftData)
    (i : DirectLiftedIndex basis) : ZPoly :=
  basis.liftedFactors[i]

/-- Recovery plan at the ordinary direct Mignotte bound. -/
@[expose]
def directLiftPlan
    (core : SquareFreeInput) (modular : DirectPrimePlan core) :
    DirectLiftPlan core modular :=
  DirectLiftPlan.canonical core modular

/-- Execute the unique Hensel lift owned by a direct recovery plan. -/
@[expose]
def directLiftedBasis
    (core : SquareFreeInput) (modular : DirectPrimePlan core)
    (plan : DirectLiftPlan core modular) :
    DirectLiftedBasis plan :=
  DirectLiftedBasis.canonical plan

end Hex
