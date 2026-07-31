/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexBerlekampZassenhausMathlib.Classical.Factorization
public import HexBerlekampZassenhausMathlib.LatticeTier

public section
set_option backward.proofsInPublic true

/-!
# Irreducibility of factors returned by the classical and total methods

The classical branch is proved directly from `factorDirectCore_factored`.
There is no scaled-coordinate fallback or per-piece refinement theorem in this
bridge.
-/

namespace HexBerlekampZassenhausMathlib

open Polynomial

/-- Every recordable raw factor returned by the direct classical tier is
irreducible. -/
theorem factorClassicalFactors_factor_irreducible
    (f : Hex.ZPoly) (hf : f ≠ 0)
    {cf : Array Hex.ZPoly}
    (hcf : Hex.factorClassicalFactors f = some cf)
    {raw : Hex.ZPoly}
    (hmem : raw ∈ cf.toList)
    (hrec :
      Hex.shouldRecordPolynomialFactor (Hex.normalizeFactorSign raw) = true) :
    Hex.ZPoly.Irreducible raw := by
  have hcore_pos :=
    Hex.squareFreeCore_leadingCoeff_pos_of_ne_zero f hf
  have hcore_prim :=
    IntReductionMod.normalizeForFactor_squareFreeCore_primitive_of_ne_zero f hf
  simp only [Hex.factorClassicalFactors, Hex.runClassical] at hcf
  by_cases hdeg :
      (Hex.normalizeForFactor f).squareFreeCore.degree?.getD 0 = 0
  · rw [if_pos hdeg] at hcf
    obtain rfl := Option.some.inj hcf
    have hcomplete :=
      Hex.reassemblyExpansionComplete_constant_of_ne_zero f hf hdeg
    rcases
        Hex.reassemblePolynomialFactors_mem_xPower_or_core_of_expansionComplete
          _ _ raw hcomplete hmem with hx | hcore
    · exact Hex.xPowerFactorArray_irreducible _ raw hx
    · exfalso
      have hraw_one : raw = 1 := by
        have hraw_core :
            raw = (Hex.normalizeForFactor f).squareFreeCore := by
          simpa using hcore
        rw [hraw_core,
          Hex.squareFreeCore_eq_one_of_constant_of_ne_zero f hf hdeg]
      rw [hraw_one, Hex.normalizeFactorSign_one,
        Hex.shouldRecordPolynomialFactor_one] at hrec
      exact absurd hrec (by decide)
  · rw [if_neg hdeg] at hcf
    cases hquad :
        Hex.quadraticIntegerRootFactors?
          (Hex.normalizeForFactor f).squareFreeCore with
    | some coreFactors =>
        simp only [hquad] at hcf
        obtain rfl := Option.some.inj hcf
        refine
          Hex.reassemblePolynomialFactors_factor_irreducible_of_complete_and_core_irreducible
            _ _ ?_ ?_ hmem
        · exact
            IntReductionMod.reassemblyExpansionComplete_quadraticIntegerRootFactors_of_ne_zero
                f hf hquad
        · intro factor hfactor
          exact
            Hex.quadraticIntegerRootFactors?_factor_irreducible_of_primitive
              hcore_pos hcore_prim hquad hfactor
    | none =>
        simp only [hquad] at hcf
        cases hplan :
            Hex.directPrimePlan?
              (Hex.SquareFreeInput.ofNormalized (Hex.normalizeForFactor f)) with
        | none =>
            simp [hplan] at hcf
        | some modular =>
            simp only [hplan] at hcf
            generalize hrun :
                Hex.factorDirectCoreOfPlan
                  (Hex.SquareFreeInput.ofNormalized (Hex.normalizeForFactor f))
                  modular = outcome at hcf
            cases outcome with
            | declined reason stats => simp at hcf
            | factored coreFactors stats =>
                simp only at hcf
                cases hcf
                have hcore_degree :
                    0 <
                      (Hex.normalizeForFactor f).squareFreeCore.degree?.getD 0 :=
                  Nat.pos_of_ne_zero hdeg
                have hcore_squarefree :
                    Squarefree
                      (HexPolyZMathlib.toPolynomial
                        (Hex.normalizeForFactor f).squareFreeCore) :=
                  IntReductionMod.normalizeForFactor_squareFreeCore_toPolynomial_squarefree
                      f hf
                have hspec :
                    DirectFactorListSpec
                        (Hex.normalizeForFactor f).squareFreeCore
                        coreFactors.toList :=
                  factorDirectCoreOfPlan_factored
                    (Hex.SquareFreeInput.ofNormalized (Hex.normalizeForFactor f))
                    modular hplan hcore_prim hcore_pos hcore_degree
                    hcore_squarefree hrun
                have hcomplete :=
                  IntReductionMod.reassemblyExpansionComplete_of_irreducible_squarefree_cover_of_norm
                      f hf coreFactors
                      (fun g hg =>
                        (Hex.ZPoly.Irreducible_iff_polynomialIrreducible g).mpr
                          (hspec.irreducible g hg))
                      (by simpa using hspec.product)
                      hspec.normalized hspec.degreePos
                exact
                  Hex.reassemblePolynomialFactors_factor_irreducible_of_complete_and_core_irreducible
                    _ _ hcomplete
                    (fun g hg =>
                      (Hex.ZPoly.Irreducible_iff_polynomialIrreducible g).mpr
                        (hspec.irreducible g hg))
                    hmem

/-- Hybrid raw-factor irreducibility, dispatching over direct classical,
lattice, and trial sources. -/
theorem factorFactors_factor_irreducible
    (f : Hex.ZPoly) (hf : f ≠ 0)
    {raw : Hex.ZPoly}
    (hmem : raw ∈ (Hex.factorFactors f).toList)
    (hrec :
      Hex.shouldRecordPolynomialFactor (Hex.normalizeFactorSign raw) = true) :
    Hex.ZPoly.Irreducible raw := by
  rcases Hex.factorFactors_mem_source f hmem with
    ⟨cf, hcf, hraw⟩ |
      ⟨modular, cf, hplan, hcf, hraw⟩ | htrial
  · exact factorClassicalFactors_factor_irreducible f hf
      hcf hraw hrec
  · exact
      factorLatticeFactorsWithPlan_factor_irreducible
        f hf modular hplan hcf hraw hrec
  · exact
      factorTrialFactorsWithBound_factor_irreducible
        f hf htrial hrec

end HexBerlekampZassenhausMathlib
