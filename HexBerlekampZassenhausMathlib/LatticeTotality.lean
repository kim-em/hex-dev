/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexBerlekampZassenhausMathlib.LatticeTier

public section
set_option backward.proofsInPublic true

/-!
# Conditional totality of the CLD lattice tier

The deep BHKS span and recovery argument lives in `LatticeTier`. This module
lifts its cap-level success theorem through normalization and the public raw
and `Factorization` entry points.
-/

namespace HexBerlekampZassenhausMathlib

/-- The public-cap raw lattice tier cannot decline once the monic-transform
prime selector succeeds. -/
theorem factorLatticeFactorsWithBound_ne_none_of_toMonicPrimeData
    (f : Hex.ZPoly)
    (hprime :
      Hex.ZPoly.toMonicPrimeData?
          (Hex.normalizeForFactor f).squareFreeCore ≠ none) :
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
          cases hselected :
              Hex.ZPoly.toMonicPrimeData?
                (Hex.normalizeForFactor f).squareFreeCore with
          | none =>
              exact absurd hselected hprime
          | some primeData =>
              have hcore_ne_none :=
                latticeCoreFactorsWithBound_ne_none_of_toMonicPrimeData
                  f hf primeData hselected hdeg
              cases hcore :
                  Hex.latticeCoreFactorsWithBound
                    (Hex.normalizeForFactor f).squareFreeCore
                    (Hex.latticePrecisionCap f) primeData with
              | none =>
                  exact absurd hcore hcore_ne_none
              | some coreFactors =>
                  simp [hcore]

/-- The factorization-valued lattice tier is likewise total under successful
monic-transform prime selection. -/
theorem factorLattice_ne_none_of_toMonicPrimeData
    (f : Hex.ZPoly)
    (hprime :
      Hex.ZPoly.toMonicPrimeData?
          (Hex.normalizeForFactor f).squareFreeCore ≠ none) :
    Hex.factorLattice f ≠ none := by
  have hraw :=
    factorLatticeFactorsWithBound_ne_none_of_toMonicPrimeData f hprime
  rw [Hex.factorLattice, Hex.factorLatticeWithBound]
  cases h :
      Hex.factorLatticeFactorsWithBound f (Hex.latticePrecisionCap f) with
  | none =>
      exact absurd h hraw
  | some factors =>
      simp

end HexBerlekampZassenhausMathlib
