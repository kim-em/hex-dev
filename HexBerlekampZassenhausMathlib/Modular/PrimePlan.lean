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

/-- The complete proof-facing contract of a selected direct prime.  Consumers
need the semantic factorization, the cached Berlekamp form for the singleton
certificate, and the small-prime bound used by the CLD resultant estimate. -/
structure DirectPrimeFacts
    (core : Hex.ZPoly) (data : Hex.PrimeChoiceData) : Prop where
  factorization : ModPFactorization core data
  berlekampForm : Hex.factorsModPBerlekampForm core data
  p_le : data.p ≤ 500

/-- A selected direct plan describes the normalized modular image of its own
indexed core. -/
theorem directPrimePlan_modPFactorization
    (core : Hex.SquareFreeInput) (plan : Hex.DirectPrimePlan core)
    (hplan : Hex.directPrimePlan? core = some plan)
    (hprim : Hex.ZPoly.Primitive core.poly)
    (hlc_pos : 0 < Hex.DensePoly.leadingCoeff core.poly)
    (hpos : 0 < core.poly.degree?.getD 0) :
    ModPFactorization core.poly plan.data :=
  modPFactorization_of_probePrimeData
    (Hex.directPrimePlan?_selected_spec core plan hplan)
    hprim hlc_pos hpos

/-- A successful direct plan supplies exactly the modular facts used by the
classical and lattice proof cones. -/
theorem directPrimePlan_facts
    (core : Hex.SquareFreeInput) (plan : Hex.DirectPrimePlan core)
    (hplan : Hex.directPrimePlan? core = some plan)
    (hprim : Hex.ZPoly.Primitive core.poly)
    (hlc_pos : 0 < Hex.DensePoly.leadingCoeff core.poly)
    (hpos : 0 < core.poly.degree?.getD 0) :
    DirectPrimeFacts core.poly plan.data where
  factorization :=
    directPrimePlan_modPFactorization core plan hplan hprim hlc_pos hpos
  berlekampForm :=
    Hex.probePrimeData?_form core.poly plan.selected.candidate plan.data
      (Hex.directPrimePlan?_selected_spec core plan hplan)
  p_le :=
    Hex.directPrimePlan?_selected_p_le_500 core plan hplan

end HexBerlekampZassenhausMathlib
