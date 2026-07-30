/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexBerlekampZassenhausMathlib.HotPathAdmissibility
public import HexBerlekampZassenhausMathlib.LatticeTotality
public import HexBerlekampZassenhausMathlib.Relift

public section
set_option backward.proofsInPublic true

/-!
Product contracts and source-sensitive facts for the cost-based BZ dispatcher.

The executable dispatcher still checks the packed products before accepting a
modular answer.  The theorems here show those checks are redundant for every
successful classical or lattice result; keeping the facts outside the
Mathlib-free implementation avoids pulling the recursive re-lift proof into the
executable library.
-/

namespace HexBerlekampZassenhausMathlib

private theorem shouldRecord_of_degree_pos
    {g : Hex.ZPoly} (hdeg : 0 < g.degree?.getD 0) :
    Hex.shouldRecordPolynomialFactor g = true := by
  have hzero : g ≠ 0 := by
    intro h
    rw [h] at hdeg
    simp at hdeg
  have hone : g ≠ 1 := by
    intro h
    subst g
    change 0 < (Hex.DensePoly.C (1 : Int)).degree?.getD 0 at hdeg
    simp at hdeg
  have hnegone : g ≠ Hex.DensePoly.C (-1 : Int) := by
    intro h
    rw [h, Hex.DensePoly.degree?_C_getD] at hdeg
    omega
  unfold Hex.shouldRecordPolynomialFactor
  simp [hzero, hone, hnegone]

/-- Reassembly preserves the packed product when the supplied core factors
multiply to the normalized square-free core and all have positive degree and
normalized sign. -/
private theorem packed_reassembly_product
    (f : Hex.ZPoly) (hf : f ≠ 0) (coreFactors : Array Hex.ZPoly)
    (hprod : Array.polyProduct coreFactors =
      (Hex.normalizeForFactor f).squareFreeCore)
    (hnorm : ∀ g ∈ coreFactors.toList, Hex.normalizeFactorSign g = g)
    (hdeg : ∀ g ∈ coreFactors.toList, 0 < g.degree?.getD 0) :
    Hex.Factorization.product
        (Hex.factorizationOfFactors f
          (Hex.reassemblePolynomialFactors (Hex.normalizeForFactor f) coreFactors)) = f := by
  apply Hex.factorizationOfFactors_product_of_raw_product_of_all_recorded_normalized
  · exact Hex.reassemblePolynomialFactors_product_eq_input f coreFactors hprod
  · exact Hex.reassemblePolynomialFactors_normalizeFactorSign_of_ne_zero
      f hf coreFactors hnorm
  · exact Hex.reassemblePolynomialFactors_shouldRecord_of_ne_zero
      f hf coreFactors (fun g hg => shouldRecord_of_degree_pos (hdeg g hg))

/-- Every successful bounded classical-tier raw result reconstructs the input
after packing into `Factorization`.  In particular, the dispatcher's classical
product guard cannot fail. -/
theorem factorClassicalFactorsWithBound_product
    (f : Hex.ZPoly) (B : Nat) {cf : Array Hex.ZPoly}
    (hcf : Hex.factorClassicalFactorsWithBound f B = some cf) :
    Hex.Factorization.product (Hex.factorizationOfFactors f cf) = f := by
  by_cases hf : f = 0
  · subst f
    exact Hex.factorizationOfFactors_product_of_zero cf
  simp only [Hex.factorClassicalFactorsWithBound] at hcf
  by_cases hdeg : (Hex.normalizeForFactor f).squareFreeCore.degree?.getD 0 = 0
  · rw [if_pos hdeg] at hcf
    obtain rfl := Option.some.inj hcf
    simpa [Hex.factorTrialWithBound, Hex.factorTrialFactorsWithBound, hdeg]
      using Hex.factorTrialWithBound_product f B
  · rw [if_neg hdeg] at hcf
    cases hquad :
        Hex.quadraticIntegerRootFactors? (Hex.normalizeForFactor f).squareFreeCore with
    | some coreFactors =>
        rw [hquad] at hcf
        obtain rfl := Option.some.inj hcf
        simpa [Hex.factorTrialWithBound, Hex.factorTrialFactorsWithBound, hdeg, hquad]
          using Hex.factorTrialWithBound_product f B
    | none =>
        rw [hquad] at hcf
        obtain ⟨coreFactors, hcore, rfl⟩ := Option.map_eq_some_iff.mp hcf
        have hcore_pos := Hex.squareFreeCore_leadingCoeff_pos_of_ne_zero f hf
        have hcore_prim :=
          IntReductionMod.normalizeForFactor_squareFreeCore_primitive_of_ne_zero f hf
        have hcore_squarefree :=
          IntReductionMod.normalizeForFactor_squareFreeCore_toPolynomial_squarefree
            f hf
        have hshape := classicalCoreFactorsM1OrM2_shape
          (Hex.normalizeForFactor f).squareFreeCore B hcore_prim hcore_pos
          (Nat.pos_of_ne_zero hdeg) hcore_squarefree hcore
        exact packed_reassembly_product f hf coreFactors
          hshape.1 hshape.2.1 hshape.2.2

/-- Every successful bounded lattice-tier raw result reconstructs the input
after packing into `Factorization`.  In particular, the dispatcher's lattice
product guard cannot fail. -/
theorem factorLatticeFactorsWithBound_product
    (f : Hex.ZPoly) (B : Nat) {cf : Array Hex.ZPoly}
    (hcf : Hex.factorLatticeFactorsWithBound f B = some cf) :
    Hex.Factorization.product (Hex.factorizationOfFactors f cf) = f := by
  by_cases hf : f = 0
  · subst f
    exact Hex.factorizationOfFactors_product_of_zero cf
  simp only [Hex.factorLatticeFactorsWithBound] at hcf
  by_cases hdeg : (Hex.normalizeForFactor f).squareFreeCore.degree?.getD 0 = 0
  · rw [if_pos hdeg] at hcf
    obtain rfl := Option.some.inj hcf
    simpa [Hex.factorTrialWithBound, Hex.factorTrialFactorsWithBound, hdeg]
      using Hex.factorTrialWithBound_product f B
  · rw [if_neg hdeg] at hcf
    by_cases hB : B = 0
    · simp [hB] at hcf
    · rw [if_neg hB] at hcf
      cases hquad :
          Hex.quadraticIntegerRootFactors? (Hex.normalizeForFactor f).squareFreeCore with
      | some coreFactors =>
          rw [hquad] at hcf
          obtain rfl := Option.some.inj hcf
          simpa [Hex.factorTrialWithBound, Hex.factorTrialFactorsWithBound, hdeg, hquad]
            using Hex.factorTrialWithBound_product f B
      | none =>
          rw [hquad] at hcf
          cases hprime :
              Hex.ZPoly.toMonicPrimeData? (Hex.normalizeForFactor f).squareFreeCore with
          | none => simp [hprime] at hcf
          | some primeData =>
              rw [hprime] at hcf
              obtain ⟨coreFactors, hcore, rfl⟩ := Option.map_eq_some_iff.mp hcf
              have hcore_pos := Hex.squareFreeCore_leadingCoeff_pos_of_ne_zero f hf
              exact packed_reassembly_product f hf coreFactors
                (Hex.latticeCoreFactorsWithBound_polyProduct _ _ _ hcore)
                (Hex.latticeCoreFactorsWithBound_normalizeFactorSign _ _ _
                  hcore_pos hcore)
                (Hex.latticeCoreFactorsWithBound_degree_pos _ _ _
                  (Nat.pos_of_ne_zero hdeg) hcore)

/-- `Factorization`-level product contract for a successful classical tier. -/
theorem factorClassicalWithBound_product_of_some
    (f : Hex.ZPoly) (B : Nat) {fac : Hex.Factorization}
    (h : Hex.factorClassicalWithBound f B = some fac) :
    fac.product = f := by
  unfold Hex.factorClassicalWithBound at h
  obtain ⟨cf, hcf, rfl⟩ := Option.map_eq_some_iff.mp h
  exact factorClassicalFactorsWithBound_product f B hcf

/-- `Factorization`-level product contract for a successful lattice tier. -/
theorem factorLatticeWithBound_product_of_some
    (f : Hex.ZPoly) (B : Nat) {fac : Hex.Factorization}
    (h : Hex.factorLatticeWithBound f B = some fac) :
    fac.product = f := by
  unfold Hex.factorLatticeWithBound at h
  obtain ⟨cf, hcf, rfl⟩ := Option.map_eq_some_iff.mp h
  exact factorLatticeFactorsWithBound_product f B hcf

/-- If the lattice tier is known not to decline, the raw hybrid result comes
from a modular tier: classical success wins, otherwise lattice success does.
The packed-product theorems discharge both executable acceptance guards. -/
theorem factorFactors_modular_of_lattice
    (f : Hex.ZPoly)
    (hlattice :
      Hex.factorLatticeFactorsWithBound f (Hex.latticePrecisionCap f) ≠ none) :
    (∃ cf,
      Hex.factorClassicalFactorsWithBound f
          (Hex.ZPoly.defaultFactorCoeffBound f) = some cf ∧
        Hex.factorFactors f = cf) ∨
      (∃ cf,
        Hex.factorClassicalFactorsWithBound f
            (Hex.ZPoly.defaultFactorCoeffBound f) = none ∧
          Hex.factorLatticeFactorsWithBound f
              (Hex.latticePrecisionCap f) = some cf ∧
          Hex.factorFactors f = cf) := by
  unfold Hex.factorFactors
  cases hclassical :
      Hex.factorClassicalFactorsWithBound f
        (Hex.ZPoly.defaultFactorCoeffBound f) with
  | some cf =>
      have hprod := factorClassicalFactorsWithBound_product f
        (Hex.ZPoly.defaultFactorCoeffBound f) hclassical
      refine Or.inl ⟨cf, rfl, ?_⟩
      change (if (Hex.factorizationOfFactors f cf).product = f then cf
        else Hex.factorTrialFactorsWithBound f
          (Hex.ZPoly.defaultFactorCoeffBound f)) = cf
      exact if_pos hprod
  | none =>
      obtain ⟨cf, hlattice_eq⟩ := Option.ne_none_iff_exists.mp hlattice
      have hprod := factorLatticeFactorsWithBound_product f
        (Hex.latticePrecisionCap f) hlattice_eq.symm
      refine Or.inr ⟨cf, rfl, hlattice_eq.symm, ?_⟩
      rw [← hlattice_eq]
      change (if (Hex.factorizationOfFactors f cf).product = f then cf
        else Hex.factorTrialFactorsWithBound f
          (Hex.ZPoly.defaultFactorCoeffBound f)) = cf
      exact if_pos hprod

/-- Successful monic-transform prime selection rules out the trial backstop:
the hybrid result is tagged with the successful modular source branch. -/
theorem factorFactors_modular_of_toMonicPrimeData
    (f : Hex.ZPoly)
    (hprime :
      Hex.ZPoly.toMonicPrimeData?
          (Hex.normalizeForFactor f).squareFreeCore ≠ none) :
    (∃ cf,
      Hex.factorClassicalFactorsWithBound f
          (Hex.ZPoly.defaultFactorCoeffBound f) = some cf ∧
        Hex.factorFactors f = cf) ∨
      (∃ cf,
        Hex.factorClassicalFactorsWithBound f
            (Hex.ZPoly.defaultFactorCoeffBound f) = none ∧
          Hex.factorLatticeFactorsWithBound f
              (Hex.latticePrecisionCap f) = some cf ∧
          Hex.factorFactors f = cf) := by
  exact factorFactors_modular_of_lattice f
    (factorLatticeFactorsWithBound_ne_none_of_toMonicPrimeData f hprime)

/-- A hot-path good prime for the positive-degree normalized square-free core
forces the hybrid dispatcher to return a branch-tagged modular result. -/
theorem factorFactors_modular_of_normalizedCore_good
    (f : Hex.ZPoly)
    (hdeg : 0 <
      (HexPolyZMathlib.toPolynomial
        (Hex.normalizeForFactor f).squareFreeCore).degree)
    (hgood : ∃ c ∈ Hex.hotPathCandidates,
      @Hex.isGoodPrime
        (Hex.normalizeForFactor f).squareFreeCore c.p c.bounds = true) :
    (∃ cf,
      Hex.factorClassicalFactorsWithBound f
          (Hex.ZPoly.defaultFactorCoeffBound f) = some cf ∧
        Hex.factorFactors f = cf) ∨
      (∃ cf,
        Hex.factorClassicalFactorsWithBound f
            (Hex.ZPoly.defaultFactorCoeffBound f) = none ∧
          Hex.factorLatticeFactorsWithBound f
              (Hex.latticePrecisionCap f) = some cf ∧
          Hex.factorFactors f = cf) := by
  exact factorFactors_modular_of_toMonicPrimeData f
    (HotPath.toMonic_ne_none_of_good hdeg hgood)

/-- The strict hot-path primorial bound for a nonzero input's normalized core
also forces a branch-tagged modular result, excluding every trial route. -/
theorem factorFactors_modular_of_normalizedCore_lt_primorial
    (f : Hex.ZPoly) (hf : f ≠ 0)
    (hdeg : 0 <
      (HexPolyZMathlib.toPolynomial
        (Hex.normalizeForFactor f).squareFreeCore).degree)
    (hlt : Int.natAbs
      ((HexPolyZMathlib.toPolynomial
          (Hex.normalizeForFactor f).squareFreeCore).leadingCoeff *
        (HexPolyZMathlib.toPolynomial
          (Hex.normalizeForFactor f).squareFreeCore).discr) <
        Hex.hotPathPrimorial) :
    (∃ cf,
      Hex.factorClassicalFactorsWithBound f
          (Hex.ZPoly.defaultFactorCoeffBound f) = some cf ∧
        Hex.factorFactors f = cf) ∨
      (∃ cf,
        Hex.factorClassicalFactorsWithBound f
            (Hex.ZPoly.defaultFactorCoeffBound f) = none ∧
          Hex.factorLatticeFactorsWithBound f
              (Hex.latticePrecisionCap f) = some cf ∧
          Hex.factorFactors f = cf) := by
  exact factorFactors_modular_of_toMonicPrimeData f
    (HotPath.normalizedCore_toMonic_ne_none_of_lt_primorial hf hdeg hlt)

end HexBerlekampZassenhausMathlib
