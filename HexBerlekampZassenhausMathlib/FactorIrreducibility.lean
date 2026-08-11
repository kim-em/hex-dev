/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexBerlekampZassenhausMathlib.Classical.Factorization
public import HexBerlekampZassenhausMathlib.LatticeFactorization
public import HexBerlekampZassenhausMathlib.QuadraticNormIrreducible

public section
set_option backward.proofsInPublic true

/-!
# Irreducibility of factors returned by the classical and total methods

The classical branch is proved directly from `factorDirectCore_factored`.
There is no scaled-coordinate fallback or per-piece refinement theorem in this
correspondence.
-/

namespace HexBerlekampZassenhausMathlib

open Polynomial

/-- Every recordable raw factor returned by the direct classical method is
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
  simp only [Hex.factorClassicalFactors, Hex.runClassical,
    Hex.classicalInput] at hcf
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
        split at hcf
        · simp [Hex.ClassicalInput.run] at hcf
        · rename_i modular hplan
          split at hcf
          -- The budget-gated iterated-quadratic-norm certificate answered the
          -- whole square-free core as one irreducible factor.
          · rename_i hcert
            simp only [Hex.ClassicalInput.run] at hcf
            obtain rfl := Option.some.inj hcf
            have hcore_irr :
                Hex.ZPoly.Irreducible (Hex.normalizeForFactor f).squareFreeCore :=
              (Hex.ZPoly.Irreducible_iff_polynomialIrreducible _).mpr
                (irreducible_of_quadraticNormCertified hcert)
            have hsingle :
                ∀ q ∈ (#[(Hex.normalizeForFactor f).squareFreeCore] : Array Hex.ZPoly).toList,
                  q = (Hex.normalizeForFactor f).squareFreeCore := by
              intro q hq
              simpa using hq
            refine
              Hex.reassemblePolynomialFactors_factor_irreducible_of_complete_and_core_irreducible
                _ _ ?_ (fun q hq => (hsingle q hq) ▸ hcore_irr) hmem
            refine
              IntReductionMod.reassemblyExpansionComplete_of_irreducible_squarefree_cover_of_norm
                f hf _ (fun q hq => (hsingle q hq) ▸ hcore_irr) ?_ ?_ ?_
            · simp [Hex.ZPoly.polyProduct_singleton]
            · intro q hq
              rw [hsingle q hq]
              exact Hex.normalizeFactorSign_eq_self_of_leadingCoeff_nonneg _
                (le_of_lt hcore_pos)
            · intro q hq
              rw [hsingle q hq]
              exact Nat.pos_of_ne_zero hdeg
          · simp only [Hex.ClassicalInput.run, Hex.runClassicalPlan] at hcf
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

/-- A member of an array product that is nonzero is itself nonzero. -/
private theorem mem_ne_zero_of_polyProduct_ne_zero
    (pieces : Array Hex.ZPoly) (piece : Hex.ZPoly)
    (hproduct : Array.polyProduct pieces ≠ 0)
    (hmem : piece ∈ pieces.toList) :
    piece ≠ 0 := by
  intro hpiece
  subst piece
  rw [List.mem_iff_append] at hmem
  obtain ⟨before, after, hpieces⟩ := hmem
  apply hproduct
  have harray : pieces = before.toArray ++ #[0] ++ after.toArray := by
    apply Array.toList_inj.mp
    rw [hpieces]
    simp
  rw [harray]
  rw [Hex.ZPoly.polyProduct_append, Hex.ZPoly.polyProduct_append,
    Hex.ZPoly.polyProduct_singleton]
  rw [Hex.DensePoly.mul_comm_poly (S := Int) _ 0,
    Hex.DensePoly.zero_mul, Hex.DensePoly.zero_mul]

/-- Every flattened factor returned by classical replay is irreducible, as
long as every proposed input piece is nonzero. -/
private theorem replayClassicalList_factor_irreducible
    (pieces : List Hex.ZPoly)
    (hnonzero : ∀ piece ∈ pieces, piece ≠ 0) :
    ∀ {factors : Array Hex.ZPoly} {raw : Hex.ZPoly},
      Hex.replayClassicalList pieces = some factors →
      raw ∈ factors.toList →
      Hex.shouldRecordPolynomialFactor (Hex.normalizeFactorSign raw) = true →
      Hex.ZPoly.Irreducible raw := by
  induction pieces with
  | nil =>
      intro factors raw hreplay hmem _hrecord
      simp [Hex.replayClassicalList] at hreplay
      subst factors
      simp at hmem
  | cons piece pieces ih =>
      intro factors raw hreplay hmem hrecord
      cases hpiece : Hex.factorClassicalFactors piece with
      | none =>
          simp [Hex.replayClassicalList, hpiece] at hreplay
      | some pieceFactors =>
          cases htail : Hex.replayClassicalList pieces with
          | none =>
              simp [Hex.replayClassicalList, hpiece, htail] at hreplay
          | some tailFactors =>
              simp only [Hex.replayClassicalList, hpiece, htail] at hreplay
              obtain rfl := Option.some.inj hreplay
              rw [Array.toList_append, List.mem_append] at hmem
              rcases hmem with hhead | htailMem
              · exact factorClassicalFactors_factor_irreducible
                  piece (hnonzero piece (by simp)) hpiece hhead hrecord
              · exact ih
                  (fun q hq => hnonzero q (by simp [hq]))
                  htail htailMem hrecord

/-- A successful proposal is irreducible factorwise because its flattened
array is exactly the output of proved classical factorization calls. -/
theorem proposedFactorization_factor_irreducible
    (f : Hex.ZPoly) (hf : f ≠ 0)
    (result : Hex.ProposedFactorization f)
    {raw : Hex.ZPoly}
    (hmem : raw ∈ result.factors.toList)
    (hrec :
      Hex.shouldRecordPolynomialFactor (Hex.normalizeFactorSign raw) = true) :
    Hex.ZPoly.Irreducible raw := by
  apply replayClassicalList_factor_irreducible result.pieces.toList
  · intro piece hpiece
    apply mem_ne_zero_of_polyProduct_ne_zero result.pieces piece
    · rw [result.pieces_product]
      exact hf
    · exact hpiece
  · exact result.replay
  · exact hmem
  · exact hrec

/-- Hybrid raw-factor irreducibility, selecting over proposal replay, direct
classical, lattice, and trial sources. -/
theorem factorFactors_factor_irreducible
    (f : Hex.ZPoly) (hf : f ≠ 0)
    {raw : Hex.ZPoly}
    (hmem : raw ∈ (Hex.factorFactors f).toList)
    (hrec :
      Hex.shouldRecordPolynomialFactor (Hex.normalizeFactorSign raw) = true) :
    Hex.ZPoly.Irreducible raw := by
  rcases Hex.factorFactors_mem_source f hmem with
    ⟨result, hraw⟩ |
      ⟨cf, hcf, hraw⟩ |
        ⟨modular, cf, hplan, hcf, hraw⟩ | htrial
  · exact proposedFactorization_factor_irreducible f hf result hraw hrec
  · exact factorClassicalFactors_factor_irreducible f hf
      hcf hraw hrec
  · exact
      factorLatticeFactorsWithPlan_factor_irreducible
        f hf modular hplan hcf hraw hrec
  · exact
      factorTrialFactorsWithBound_factor_irreducible
        f hf htrial hrec

end HexBerlekampZassenhausMathlib
