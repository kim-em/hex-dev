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
    (core : CoreProblem) (modular : DirectPrimePlan core) :
    DirectLiftPlan core modular :=
  DirectLiftPlan.canonical core modular

/-- Execute the unique Hensel lift owned by a direct recovery plan. -/
@[expose]
def directLiftedBasis
    (core : CoreProblem) (modular : DirectPrimePlan core)
    (plan : DirectLiftPlan core modular) :
    DirectLiftedBasis plan :=
  DirectLiftedBasis.canonical plan

end Hex
