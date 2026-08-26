/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexBerlekampZassenhausMathlib.LatticeFactorization

public section
set_option backward.proofsInPublic true

/-!
# Totality of the CLD lattice method

The exact-span argument lives in `LatticeFactorization`. This module lifts its cap-level
success theorem through normalization and the public raw and `Factorization`
entry points.
-/

namespace HexBerlekampZassenhausMathlib

/-- The public-cap raw lattice method cannot decline once direct prime planning
succeeds. -/
theorem factorLatticeFactorsWithBound_ne_none_of_directPrimePlan
    (f : Hex.ZPoly)
    (hprime :
      Hex.directPrimePlan?
          ⟨(Hex.normalizeForFactor f).squareFreeCore⟩ ≠ none) :
    Hex.factorLatticeFactorsWithBound f (Hex.latticePrecisionCap f) ≠ none := by
  by_cases hf : f = 0
  · subst f
    rw [Hex.factorLatticeFactorsWithBound_zero]
    simp
  · rw [Hex.factorLatticeFactorsWithBound]
    by_cases hdeg :
        (Hex.normalizeForFactor f).squareFreeCore.degree?.getD 0 = 0
    · rw [if_pos hdeg]
      simp
    · rw [if_neg hdeg]
      have hB_ne : Hex.latticePrecisionCap f ≠ 0 := by
        have hcore_lc_pos :=
          Hex.squareFreeCore_leadingCoeff_pos_of_ne_zero f hf
        have hcore_ne :
            (Hex.normalizeForFactor f).squareFreeCore ≠ 0 :=
          zpoly_ne_zero_of_pos_lc hcore_lc_pos
        have hbound_pos :=
          Hex.ZPoly.defaultFactorCoeffBound_pos_of_ne_zero hcore_ne
        have hbound_le :=
          Hex.defaultFactorCoeffBound_squareFreeCore_le_latticePrecisionCap f
        omega
      rw [if_neg hB_ne]
      cases hquad :
          Hex.quadraticIntegerRootFactors?
            (Hex.normalizeForFactor f).squareFreeCore with
      | some factors =>
          simp
      | none =>
          simp only
          cases hplan :
              Hex.directPrimePlan?
                ⟨(Hex.normalizeForFactor f).squareFreeCore⟩ with
          | none =>
              exact absurd hplan hprime
          | some plan =>
              have hcore_lc_pos :=
                Hex.squareFreeCore_leadingCoeff_pos_of_ne_zero f hf
              have hcore_pos :
                  0 <
                    (Hex.normalizeForFactor f).squareFreeCore.degree?.getD 0 :=
                Nat.pos_of_ne_zero hdeg
              have hcore_prim :=
                IntReductionMod.normalizeForFactor_squareFreeCore_primitive_of_ne_zero
                  f hf
              let prime :=
                directPrimePlan_facts
                  ⟨(Hex.normalizeForFactor f).squareFreeCore⟩ plan hplan
                  hcore_prim hcore_lc_pos hcore_pos
              have hcore_ne_none :=
                latticeCoreFactorsWithBound_ne_none
                  (Hex.normalizeForFactor f).squareFreeCore
                  (Hex.latticePrecisionCap f) plan.data prime
                  hcore_lc_pos hcore_pos hcore_prim
                  (IntReductionMod.normalizeForFactor_squareFreeCore_toPolynomial_squarefree
                    f hf)
                  (Hex.bhksRecoveryFloor_squareFreeCore_le_latticePrecisionCap f)
                  hB_ne
                  (Hex.two_mul_bhksBound_squareFreeCore_lt_pow_cap
                    f plan.data prime.factorization.prime.two_le)
              cases hcore :
                  Hex.latticeCoreFactorsWithBound
                    (Hex.normalizeForFactor f).squareFreeCore
                    (Hex.latticePrecisionCap f) plan.data with
              | none =>
                  exact absurd hcore hcore_ne_none
              | some coreFactors =>
                  unfold Hex.factorLatticeFactorsWithPlan
                  simp [hdeg, hB_ne, hquad]
                  exact hcore_ne_none

/-- The factorization-valued lattice method is likewise total under successful
direct prime planning. -/
theorem factorLattice_ne_none_of_directPrimePlan
    (f : Hex.ZPoly)
    (hprime :
      Hex.directPrimePlan?
          ⟨(Hex.normalizeForFactor f).squareFreeCore⟩ ≠ none) :
    Hex.factorLattice f ≠ none := by
  have hraw :=
    factorLatticeFactorsWithBound_ne_none_of_directPrimePlan f hprime
  rw [Hex.factorLattice, Hex.factorLatticeWithBound]
  cases h :
      Hex.factorLatticeFactorsWithBound f (Hex.latticePrecisionCap f) with
  | none =>
      exact absurd h hraw
  | some factors =>
      simp

end HexBerlekampZassenhausMathlib
