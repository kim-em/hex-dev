/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexBerlekampZassenhaus.Modular.PrimePlan
public import HexBerlekampZassenhausMathlib.ModPFactorization

public section
set_option backward.proofsInPublic true

/-!
# Correctness of the direct prime plan
-/

namespace HexBerlekampZassenhausMathlib

/-- A selected direct plan describes the normalized modular image of its own
indexed core. -/
theorem directPrimePlan_modPFactorization
    (core : Hex.CoreProblem) (plan : Hex.DirectPrimePlan core)
    (hplan : Hex.directPrimePlan? core = some plan)
    (hprim : Hex.ZPoly.Primitive core.poly)
    (hlc_pos : 0 < Hex.DensePoly.leadingCoeff core.poly)
    (hpos : 0 < core.poly.degree?.getD 0) :
    ModPFactorization core.poly plan.data :=
  modPFactorization_of_probePrimeData
    (Hex.directPrimePlan?_selected_spec core plan hplan)
    hprim hlc_pos hpos

end HexBerlekampZassenhausMathlib

