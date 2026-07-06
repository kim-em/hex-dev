/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public meta import HexArith.Nat.Prime
public meta import HexBerlekamp.Factor
public meta import HexBerlekamp.Irreducibility
public meta import HexHensel.Basic
public meta import HexHensel.Multifactor
public meta import HexHensel.QuadraticMultifactor
public meta import HexMatrix.Basic
public meta import HexPolyZ.Mignotte
public meta import HexLLL.Basic
public import HexArith.Nat.Prime
public import HexBerlekamp.Factor
public import HexBerlekamp.Irreducibility
public import HexHensel.Multifactor
public import HexHensel.QuadraticMultifactor
public import HexLLL.Basic
-- Needed so `decide`/`rfl` over `DensePoly`/`Array` equality reduces in the
-- kernel: the core `Array.instDecidableEq` delegates its nonempty case to the
-- non-`@[expose]` `Array.instDecidableEqImpl`, which is otherwise opaque under
-- the module system. Drop once that impl is exposed upstream (lean4).
import all Init.Data.Array.DecidableEq

public import HexBerlekampZassenhaus.RecombineProofs
public meta import HexBerlekampZassenhaus.RecombineProofs
import all HexBerlekampZassenhaus.PrimeSelection
import all HexBerlekampZassenhaus.Records
import all HexBerlekampZassenhaus.Certificate
import all HexBerlekampZassenhaus.ChoosePrimeData
import all HexBerlekampZassenhaus.ReassemblyProofs
import all HexBerlekampZassenhaus.Lattice
import all HexBerlekampZassenhaus.BhksCandidates
import all HexBerlekampZassenhaus.BhksRecover
import all HexBerlekampZassenhaus.Recombination
import all HexBerlekampZassenhaus.FactorEntryPoints
import all HexBerlekampZassenhaus.IrreducibleCore
import all HexBerlekampZassenhaus.RecombineProofs

public section
set_option backward.proofsInPublic true

/-!
This module collects the trial-division and integer-root correctness proofs.
-/
namespace Hex

/-- Each factor emitted by the size-ordered classical recombination core has
positive `degree?`, provided `core` itself has positive degree. Classical analog
of `exhaustiveIntegerTrialCoreFactorsWithBound_degree_pos`: the recombination
factors are primitive and `normalizeFactorSign`-fixed with `shouldRecord = true`
(all supplied by `classicalCoreFactorsWithBound_spec`), so
`degree_pos_of_primitive_norm_record` applies; the singleton short-circuit is
`core`, whose positive degree is the sole hypothesis. -/
theorem classicalCoreFactorsWithBound_degree_pos
    (core : ZPoly) (B : Nat) (primeData : PrimeChoiceData)
    (hcore_deg : 0 < core.degree?.getD 0)
    {cf : Array ZPoly}
    (h : classicalCoreFactorsWithBound core B primeData = some cf) :
    ∀ factor ∈ cf.toList, 0 < factor.degree?.getD 0 := by
  rcases classicalCoreFactorsWithBound_spec core B primeData h with
    hsing | ⟨_, hnorm, hprim, hrecord⟩
  · intro factor hmem
    rw [hsing] at hmem
    have hfactor : factor = core := by simpa using hmem
    rw [hfactor]; exact hcore_deg
  · intro factor hmem
    exact degree_pos_of_primitive_norm_record factor
      (hprim factor hmem) (hnorm factor hmem) (hrecord factor hmem)

/-- Structural case-split for the van Hoeij lattice-tier core. Every `some cf`
result of `latticeCoreFactorsWithBound` is either the singleton `#[core]` (the
small-mod arm, the loop's certificate-backed early stop, and the cap all-ones
certification arm) or a `bhksRecoveryCoreWithBound` success (the CLD-split arm,
via `latticeCoreWithBound_some_spec`). The trio
`latticeCoreFactorsWithBound_{polyProduct,normalizeFactorSign,degree_pos}`
below are thin consumers, mirroring the classical structural trio. -/
private theorem latticeCoreFactorsWithBound_spec
    (core : ZPoly) (B : Nat) (primeData : PrimeChoiceData)
    {cf : Array ZPoly}
    (h : latticeCoreFactorsWithBound core B primeData = some cf) :
    cf = #[core] ∨
      bhksRecoveryCoreWithBound core B primeData (initialHenselPrecision B)
        (ZPoly.quadraticDoublingSteps B + 2) = some cf := by
  rw [latticeCoreFactorsWithBound] at h
  split at h
  · exact Or.inl (Option.some.inj h).symm
  · split at h
    · rename_i coreFactors hlattice
      rcases latticeCoreWithBound_some_spec hlattice with hfast | ⟨hsing, _⟩
      · exact Or.inr ((Option.some.inj h) ▸ hfast)
      · exact Or.inl ((Option.some.inj h) ▸ hsing)
    · split at h
      · split at h
        · exact Or.inl (Option.some.inj h).symm
        · exact absurd h.symm (Option.some_ne_none cf)
      · exact absurd h.symm (Option.some_ne_none cf)

/-- PolyProduct identity for the van Hoeij lattice-tier core: every emitted
factor array multiplies back to `core`. Mirror of
`classicalCoreFactorsWithBound_polyProduct`; the singleton arms are immediate
and the CLD-split arm reuses `bhksRecoveryCoreWithBound_product`. -/
theorem latticeCoreFactorsWithBound_polyProduct
    (core : ZPoly) (B : Nat) (primeData : PrimeChoiceData)
    {cf : Array ZPoly}
    (h : latticeCoreFactorsWithBound core B primeData = some cf) :
    Array.polyProduct cf = core := by
  rcases latticeCoreFactorsWithBound_spec core B primeData h with hsing | hfast
  · rw [hsing]; exact ZPoly.polyProduct_singleton core
  · exact bhksRecoveryCoreWithBound_product core B primeData _ _ cf hfast

/-- Each factor emitted by the van Hoeij lattice-tier core is fixed by
`normalizeFactorSign`, provided `core` has positive leading coefficient. Mirror
of `classicalCoreFactorsWithBound_normalizeFactorSign`: the CLD-split factors
are sign-normalized by construction, and the singleton arms are `core`, fixed
by its positive leading coefficient. -/
theorem latticeCoreFactorsWithBound_normalizeFactorSign
    (core : ZPoly) (B : Nat) (primeData : PrimeChoiceData)
    (hcore_pos : 0 < DensePoly.leadingCoeff core)
    {cf : Array ZPoly}
    (h : latticeCoreFactorsWithBound core B primeData = some cf) :
    ∀ factor ∈ cf.toList, normalizeFactorSign factor = factor := by
  rcases latticeCoreFactorsWithBound_spec core B primeData h with hsing | hfast
  · intro factor hmem
    rw [hsing] at hmem
    have hfactor : factor = core := by simpa using hmem
    rw [hfactor]
    exact normalizeFactorSign_eq_self_of_leadingCoeff_nonneg core (by omega)
  · exact bhksRecoveryCoreWithBound_some_normalizeFactorSign hfast

/-- Each factor emitted by the van Hoeij lattice-tier core has positive
`degree?`, provided `core` itself has positive degree. Mirror of
`classicalCoreFactorsWithBound_degree_pos`: the CLD-split factors have positive
degree by construction, and the singleton arms are `core`, whose positive
degree is the sole hypothesis. -/
theorem latticeCoreFactorsWithBound_degree_pos
    (core : ZPoly) (B : Nat) (primeData : PrimeChoiceData)
    (hcore_deg : 0 < core.degree?.getD 0)
    {cf : Array ZPoly}
    (h : latticeCoreFactorsWithBound core B primeData = some cf) :
    ∀ factor ∈ cf.toList, 0 < factor.degree?.getD 0 := by
  rcases latticeCoreFactorsWithBound_spec core B primeData h with hsing | hfast
  · intro factor hmem
    rw [hsing] at hmem
    have hfactor : factor = core := by simpa using hmem
    rw [hfactor]; exact hcore_deg
  · exact bhksRecoveryCoreWithBound_some_degree_pos hfast

private theorem polyProduct_push (factors : Array ZPoly) (factor : ZPoly) :
    Array.polyProduct (factors.push factor) =
      Array.polyProduct factors * factor := by
  cases factors with
  | mk xs =>
      induction xs generalizing factor with
      | nil =>
          simp [Array.polyProduct, ZPoly.one_mul_zpoly]
      | cons x xs ih =>
          simp [Array.polyProduct, List.foldl_cons] at ih ⊢

private theorem splitIntegerRootFactorsAux_product
    (target : ZPoly) (roots : List Int) (fuel : Nat) :
    ∀ factors residual,
      splitIntegerRootFactorsAux target roots fuel = (factors, residual) →
        residual * Array.polyProduct factors = target := by
  induction fuel generalizing target roots with
  | zero =>
      intro factors residual hsplit
      rw [splitIntegerRootFactorsAux] at hsplit
      injection hsplit with hfactors hresidual
      subst factors
      subst residual
      exact DensePoly.mul_one_right_poly (S := Int) target
  | succ fuel ih =>
      intro factors residual hsplit
      cases roots with
      | nil =>
          rw [splitIntegerRootFactorsAux] at hsplit
          injection hsplit with hfactors hresidual
          subst factors
          subst residual
          exact DensePoly.mul_one_right_poly (S := Int) target
      | cons root roots =>
          unfold splitIntegerRootFactorsAux at hsplit
          cases hquot : exactQuotient? target (linearFactorForRoot root) with
          | none =>
              simp [hquot] at hsplit
              exact ih target roots factors residual hsplit
          | some quotient =>
              simp [hquot] at hsplit
              cases hrest : splitIntegerRootFactorsAux quotient roots fuel with
              | mk restFactors restResidual =>
                  simp [hrest] at hsplit
                  rcases hsplit with ⟨hfactors, hresidual⟩
                  subst factors
                  subst residual
                  have hrec :
                      restResidual * Array.polyProduct restFactors = quotient :=
                    ih quotient roots restFactors restResidual hrest
                  have hquot_prod :
                      quotient * linearFactorForRoot root = target :=
                    exactQuotient?_product hquot
                  calc
                    restResidual *
                        Array.polyProduct (#[linearFactorForRoot root] ++ restFactors) =
                        restResidual *
                          (linearFactorForRoot root * Array.polyProduct restFactors) := by
                          rw [ZPoly.polyProduct_append, ZPoly.polyProduct_singleton]
                    _ = restResidual *
                          (Array.polyProduct restFactors * linearFactorForRoot root) := by
                          rw [DensePoly.mul_comm_poly (S := Int)
                            (linearFactorForRoot root) (Array.polyProduct restFactors)]
                    _ = (restResidual * Array.polyProduct restFactors) *
                          linearFactorForRoot root := by
                          rw [DensePoly.mul_assoc_poly (S := Int)]
                    _ = quotient * linearFactorForRoot root := by
                          rw [hrec]
                    _ = target := hquot_prod

private theorem splitIntegerRootFactorsAux_normalizeFactorSign
    (target : ZPoly) (roots : List Int) (fuel : Nat) :
    ∀ factors residual,
      splitIntegerRootFactorsAux target roots fuel = (factors, residual) →
        ∀ factor ∈ factors.toList, normalizeFactorSign factor = factor := by
  induction fuel generalizing target roots with
  | zero =>
      intro factors residual hsplit factor hmem
      rw [splitIntegerRootFactorsAux] at hsplit
      injection hsplit with hfactors hresidual
      subst factors
      simp at hmem
  | succ fuel ih =>
      intro factors residual hsplit factor hmem
      cases roots with
      | nil =>
          rw [splitIntegerRootFactorsAux] at hsplit
          injection hsplit with hfactors hresidual
          subst factors
          simp at hmem
      | cons root roots =>
          unfold splitIntegerRootFactorsAux at hsplit
          cases hquot : exactQuotient? target (linearFactorForRoot root) with
          | none =>
              simp [hquot] at hsplit
              exact ih target roots factors residual hsplit factor hmem
          | some quotient =>
              simp [hquot] at hsplit
              cases hrest : splitIntegerRootFactorsAux quotient roots fuel with
              | mk restFactors restResidual =>
                  simp [hrest] at hsplit
                  rcases hsplit with ⟨hfactors, hresidual⟩
                  subst factors
                  subst residual
                  rw [Array.toList_append] at hmem
                  simp at hmem
                  cases hmem with
                  | inl hroot =>
                      rw [hroot]
                      exact normalizeFactorSign_linearFactorForRoot root
                  | inr hrest_mem =>
                      exact ih quotient roots restFactors restResidual hrest factor (by
                        simpa using hrest_mem)

private theorem splitIntegerRootFactorsAux_shouldRecord
    (target : ZPoly) (roots : List Int) (fuel : Nat) :
    ∀ factors residual,
      splitIntegerRootFactorsAux target roots fuel = (factors, residual) →
        ∀ factor ∈ factors.toList, shouldRecordPolynomialFactor factor = true := by
  induction fuel generalizing target roots with
  | zero =>
      intro factors residual hsplit factor hmem
      rw [splitIntegerRootFactorsAux] at hsplit
      injection hsplit with hfactors hresidual
      subst factors
      simp at hmem
  | succ fuel ih =>
      intro factors residual hsplit factor hmem
      cases roots with
      | nil =>
          rw [splitIntegerRootFactorsAux] at hsplit
          injection hsplit with hfactors hresidual
          subst factors
          simp at hmem
      | cons root roots =>
          unfold splitIntegerRootFactorsAux at hsplit
          cases hquot : exactQuotient? target (linearFactorForRoot root) with
          | none =>
              simp [hquot] at hsplit
              exact ih target roots factors residual hsplit factor hmem
          | some quotient =>
              simp [hquot] at hsplit
              cases hrest : splitIntegerRootFactorsAux quotient roots fuel with
              | mk restFactors restResidual =>
                  simp [hrest] at hsplit
                  rcases hsplit with ⟨hfactors, hresidual⟩
                  subst factors
                  subst residual
                  rw [Array.toList_append] at hmem
                  simp at hmem
                  cases hmem with
                  | inl hroot =>
                      rw [hroot]
                      exact shouldRecordPolynomialFactor_linearFactorForRoot root
                  | inr hrest_mem =>
                      exact ih quotient roots restFactors restResidual hrest factor (by
                        simpa using hrest_mem)

private theorem splitIntegerRootFactorsAux_irreducible
    (target : ZPoly) (roots : List Int) (fuel : Nat) :
    ∀ factors residual,
      splitIntegerRootFactorsAux target roots fuel = (factors, residual) →
        ∀ factor ∈ factors.toList, ZPoly.Irreducible factor := by
  induction fuel generalizing target roots with
  | zero =>
      intro factors residual hsplit factor hmem
      rw [splitIntegerRootFactorsAux] at hsplit
      injection hsplit with hfactors hresidual
      subst factors
      simp at hmem
  | succ fuel ih =>
      intro factors residual hsplit factor hmem
      cases roots with
      | nil =>
          rw [splitIntegerRootFactorsAux] at hsplit
          injection hsplit with hfactors hresidual
          subst factors
          simp at hmem
      | cons root roots =>
          unfold splitIntegerRootFactorsAux at hsplit
          cases hquot : exactQuotient? target (linearFactorForRoot root) with
          | none =>
              simp [hquot] at hsplit
              exact ih target roots factors residual hsplit factor hmem
          | some quotient =>
              simp [hquot] at hsplit
              cases hrest : splitIntegerRootFactorsAux quotient roots fuel with
              | mk restFactors restResidual =>
                  simp [hrest] at hsplit
                  rcases hsplit with ⟨hfactors, hresidual⟩
                  subst factors
                  subst residual
                  rw [Array.toList_append] at hmem
                  simp at hmem
                  cases hmem with
                  | inl hroot =>
                      rw [hroot]
                      exact irreducible_linearFactorForRoot root
                  | inr hrest_mem =>
                      exact ih quotient roots restFactors restResidual hrest factor (by
                        simpa using hrest_mem)

/-- Factors emitted by the integer-root splitter are monic linear root factors,
and hence irreducible. This is the theorem-level wrapper used by the
quadratic-root branch before any optional residual factor is appended. -/
theorem splitIntegerRootFactorsAux_factor_irreducible
    {target : ZPoly} {roots : List Int} {fuel : Nat}
    {factors : Array ZPoly} {residual factor : ZPoly}
    (hsplit : splitIntegerRootFactorsAux target roots fuel = (factors, residual))
    (hmem : factor ∈ factors.toList) :
    ZPoly.Irreducible factor :=
  splitIntegerRootFactorsAux_irreducible target roots fuel factors residual
    hsplit factor hmem

private theorem splitIntegerRootFactorsAux_polyProduct_leadingCoeff_pos
    (target : ZPoly) (roots : List Int) (fuel : Nat) :
    ∀ factors residual,
      splitIntegerRootFactorsAux target roots fuel = (factors, residual) →
        0 < DensePoly.leadingCoeff (Array.polyProduct factors) := by
  induction fuel generalizing target roots with
  | zero =>
      intro factors residual hsplit
      rw [splitIntegerRootFactorsAux] at hsplit
      injection hsplit with hfactors hresidual
      subst factors
      change 0 < DensePoly.leadingCoeff (DensePoly.C (1 : Int))
      simp [DensePoly.leadingCoeff, DensePoly.coeffs_C_of_ne_zero
        (by decide : (1 : Int) ≠ 0)]
  | succ fuel ih =>
      intro factors residual hsplit
      cases roots with
      | nil =>
          rw [splitIntegerRootFactorsAux] at hsplit
          injection hsplit with hfactors hresidual
          subst factors
          change 0 < DensePoly.leadingCoeff (DensePoly.C (1 : Int))
          simp [DensePoly.leadingCoeff, DensePoly.coeffs_C_of_ne_zero
            (by decide : (1 : Int) ≠ 0)]
      | cons root roots =>
          unfold splitIntegerRootFactorsAux at hsplit
          cases hquot : exactQuotient? target (linearFactorForRoot root) with
          | none =>
              simp [hquot] at hsplit
              exact ih target roots factors residual hsplit
          | some quotient =>
              simp [hquot] at hsplit
              cases hrest : splitIntegerRootFactorsAux quotient roots fuel with
              | mk restFactors restResidual =>
                  simp [hrest] at hsplit
                  rcases hsplit with ⟨hfactors, hresidual⟩
                  subst factors
                  subst residual
                  rw [ZPoly.polyProduct_append, ZPoly.polyProduct_singleton]
                  apply ZPoly.leadingCoeff_mul_pos_of_pos
                  · rw [leadingCoeff_linearFactorForRoot]
                    omega
                  · exact ih quotient roots restFactors restResidual hrest

/-- The factors emitted by `splitIntegerRootFactorsAux` are exactly the
images of some sublist of the input `roots` list under `linearFactorForRoot`.
Sibling of `splitIntegerRootFactorsAux_product` / `_irreducible` / etc.
Consumed by the #4785 pairwise non-association proof to read off the
distinct-roots invariant via `List.Sublist`-then-`Nodup` transfer. -/
private theorem splitIntegerRootFactorsAux_factors_distinct_roots
    (target : ZPoly) (roots : List Int) (fuel : Nat) :
    ∀ factors residual,
      splitIntegerRootFactorsAux target roots fuel = (factors, residual) →
        ∃ rs : List Int, rs.Sublist roots ∧
          factors.toList = rs.map linearFactorForRoot := by
  induction fuel generalizing target roots with
  | zero =>
      intro factors residual hsplit
      rw [splitIntegerRootFactorsAux] at hsplit
      injection hsplit with hfactors hresidual
      subst factors
      refine ⟨[], ?_, ?_⟩
      · exact List.nil_sublist roots
      · simp
  | succ fuel ih =>
      intro factors residual hsplit
      cases roots with
      | nil =>
          rw [splitIntegerRootFactorsAux] at hsplit
          injection hsplit with hfactors hresidual
          subst factors
          refine ⟨[], ?_, ?_⟩
          · exact List.nil_sublist _
          · simp
      | cons root roots =>
          unfold splitIntegerRootFactorsAux at hsplit
          cases hquot : exactQuotient? target (linearFactorForRoot root) with
          | none =>
              simp [hquot] at hsplit
              rcases ih target roots factors residual hsplit with
                ⟨rs, hsub, hshape⟩
              exact ⟨rs, hsub.cons root, hshape⟩
          | some quotient =>
              simp [hquot] at hsplit
              cases hrest : splitIntegerRootFactorsAux quotient roots fuel with
              | mk restFactors restResidual =>
                  simp [hrest] at hsplit
                  rcases hsplit with ⟨hfactors, hresidual⟩
                  subst factors
                  subst residual
                  rcases ih quotient roots restFactors restResidual hrest with
                    ⟨rs, hsub, hshape⟩
                  refine ⟨root :: rs, ?_, ?_⟩
                  · exact hsub.cons_cons root
                  · rw [Array.toList_append]
                    simp [hshape]

/-- Public wrapper of the splitter distinct-roots invariant: factors emitted
by `splitIntegerRootFactorsAux` are `linearFactorForRoot rᵢ` for some sublist
`rs` of the input `roots`. Composed with `roots.Nodup` (e.g. via
`integerRootCandidates_nodup`) to read off pairwise distinctness of the
factor roots, used by the #4785 linear-vs-linear pairwise non-association
case. -/
theorem splitIntegerRootFactorsAux_factors_form
    {target : ZPoly} {roots : List Int} {fuel : Nat}
    {factors : Array ZPoly} {residual : ZPoly}
    (hsplit : splitIntegerRootFactorsAux target roots fuel = (factors, residual)) :
    ∃ rs : List Int, rs.Sublist roots ∧
      factors.toList = rs.map linearFactorForRoot :=
  splitIntegerRootFactorsAux_factors_distinct_roots target roots fuel
    factors residual hsplit

/-- Each candidate emitted by `trialDivisionCandidatesOfDegree B d` has degree
exactly `d`, positive leading coefficient, and passes `shouldRecord`. -/
private theorem mem_trialDivisionCandidatesOfDegree {B d : Nat} {p : ZPoly}
    (hmem : p ∈ trialDivisionCandidatesOfDegree B d) :
    p.degree?.getD 0 = d ∧ 0 < DensePoly.leadingCoeff p ∧
      shouldRecordPolynomialFactor p = true := by
  unfold trialDivisionCandidatesOfDegree at hmem
  rcases List.mem_filterMap.mp hmem with ⟨coeffs, _hcoeffs, heq⟩
  by_cases hcheck :
      (DensePoly.ofCoeffs coeffs.toArray).degree?.getD 0 = d ∧
        0 < DensePoly.leadingCoeff (DensePoly.ofCoeffs coeffs.toArray) ∧
        shouldRecordPolynomialFactor (DensePoly.ofCoeffs coeffs.toArray) = true
  · rw [if_pos hcheck] at heq
    cases heq
    exact hcheck
  · rw [if_neg hcheck] at heq
    contradiction

/-- Each candidate emitted by `trialDivisionCandidatesUpTo B maxDeg` has
positive degree, positive leading coefficient, and passes `shouldRecord`. -/
private theorem mem_trialDivisionCandidatesUpTo {B maxDeg : Nat} {p : ZPoly}
    (hmem : p ∈ trialDivisionCandidatesUpTo B maxDeg) :
    0 < p.degree?.getD 0 ∧ 0 < DensePoly.leadingCoeff p ∧
      shouldRecordPolynomialFactor p = true := by
  unfold trialDivisionCandidatesUpTo at hmem
  rcases List.mem_flatMap.mp hmem with ⟨d, _hd_range, hpd⟩
  obtain ⟨hdeg, hlc, hrec⟩ := mem_trialDivisionCandidatesOfDegree hpd
  refine ⟨?_, hlc, hrec⟩
  rw [hdeg]; omega

/-- Every integer with absolute value at most `B` is enumerated by
`boundedIntegerList B`. -/
private theorem mem_boundedIntegerList_of_natAbs_le {B : Nat} {z : Int}
    (hz : z.natAbs ≤ B) :
    z ∈ boundedIntegerList B := by
  unfold boundedIntegerList
  rw [List.mem_map]
  rcases Int.natAbs_eq z with hpos | hneg
  · refine ⟨z.natAbs + B, ?_, ?_⟩
    · rw [List.mem_range]
      omega
    · have hcalc :
          (Int.ofNat (z.natAbs + B) - Int.ofNat B) =
            Int.ofNat z.natAbs := by
        change ((↑(z.natAbs + B) : Int) - (↑B : Int)) =
          (↑z.natAbs : Int)
        rw [Int.natCast_add]
        omega
      exact hcalc.trans hpos.symm
  · refine ⟨B - z.natAbs, ?_, ?_⟩
    · rw [List.mem_range]
      omega
    · have hcalc :
          (Int.ofNat (B - z.natAbs) - Int.ofNat B) =
            -Int.ofNat z.natAbs := by
        change ((↑(B - z.natAbs) : Int) - (↑B : Int)) =
          -(↑z.natAbs : Int)
        rw [Int.ofNat_sub hz]
        omega
      exact hcalc.trans hneg.symm

/-- Every coefficient list whose entries are bounded by `B` is generated by
`boundedCoefficientVectors B` at its own length. -/
private theorem mem_boundedCoefficientVectors_of_forall_natAbs_le
    (B : Nat) :
    ∀ coeffs : List Int,
      (∀ c ∈ coeffs, c.natAbs ≤ B) →
        coeffs ∈ boundedCoefficientVectors B coeffs.length
  | [], _ => by
      simp [boundedCoefficientVectors]
  | c :: coeffs, hcoeffs => by
      have htail :
          coeffs ∈ boundedCoefficientVectors B coeffs.length :=
        mem_boundedCoefficientVectors_of_forall_natAbs_le B coeffs
          (fun z hz => hcoeffs z (List.mem_cons_of_mem c hz))
      have hc : c ∈ boundedIntegerList B :=
        mem_boundedIntegerList_of_natAbs_le (hcoeffs c List.mem_cons_self)
      change c :: coeffs ∈ boundedCoefficientVectors B (coeffs.length + 1)
      unfold boundedCoefficientVectors
      rw [List.mem_flatMap]
      refine ⟨coeffs, htail, ?_⟩
      rw [List.mem_map]
      exact ⟨c, hc, rfl⟩

/-- Bounded positive-leading recorded polynomials of exact degree `d` are
enumerated by `trialDivisionCandidatesOfDegree B d`. -/
private theorem mem_trialDivisionCandidatesOfDegree_of_bounded
    {B d : Nat} {p : ZPoly}
    (hdeg : p.degree?.getD 0 = d)
    (hlc : 0 < DensePoly.leadingCoeff p)
    (hrecord : shouldRecordPolynomialFactor p = true)
    (hbound : ∀ i, (p.coeff i).natAbs ≤ B) :
    p ∈ trialDivisionCandidatesOfDegree B d := by
  unfold trialDivisionCandidatesOfDegree
  rw [List.mem_filterMap]
  have hp_ne : p ≠ 0 := by
    intro hzero
    rw [hzero] at hlc
    rw [DensePoly.leadingCoeff_zero] at hlc
    omega
  have hp_size_pos : 0 < p.size := ZPoly.size_pos_of_ne_zero p hp_ne
  have hdeg_size : p.degree?.getD 0 = p.size - 1 := by
    simp [DensePoly.degree?, Nat.ne_of_gt hp_size_pos]
  have hp_size_eq : p.size = d + 1 := by
    omega
  refine ⟨p.toArray.toList, ?_, ?_⟩
  · have hcoeffs :
        ∀ c ∈ p.toArray.toList, c.natAbs ≤ B := by
      intro c hc
      rw [Array.mem_toList_iff] at hc
      obtain ⟨i, hi, rfl⟩ := Array.getElem_of_mem hc
      have hcoeff : p.toArray[i] = p.coeff i := by
        have hi_size : i < p.size := by
          simpa [DensePoly.toArray_size] using hi
        have := DensePoly.toArray_getD p i
        simpa [Array.getD, hi_size] using this
      simpa [hcoeff]
        using hbound i
    have hmem_vectors :=
      mem_boundedCoefficientVectors_of_forall_natAbs_le B p.toArray.toList
        hcoeffs
    simpa [DensePoly.toArray_size, hp_size_eq] using hmem_vectors
  · have hp : DensePoly.ofCoeffs p.toArray = p := by
      exact DensePoly.ofCoeffs_toArray p
    have hcheck :
        (DensePoly.ofCoeffs p.toArray).degree?.getD 0 = d ∧
          0 < DensePoly.leadingCoeff (DensePoly.ofCoeffs p.toArray) ∧
          shouldRecordPolynomialFactor (DensePoly.ofCoeffs p.toArray) = true := by
      simpa [hp] using And.intro hdeg (And.intro hlc hrecord)
    rw [if_pos hcheck]
    simp [hp]

/-- Bounded positive-leading recorded polynomials with degree in
`1..maxDeg` are enumerated by `trialDivisionCandidatesUpTo B maxDeg`. -/
private theorem mem_trialDivisionCandidatesUpTo_of_bounded
    {B maxDeg : Nat} {p : ZPoly}
    (hdegree_pos : 0 < p.degree?.getD 0)
    (hdegree_le : p.degree?.getD 0 ≤ maxDeg)
    (hlc : 0 < DensePoly.leadingCoeff p)
    (hrecord : shouldRecordPolynomialFactor p = true)
    (hbound : ∀ i, (p.coeff i).natAbs ≤ B) :
    p ∈ trialDivisionCandidatesUpTo B maxDeg := by
  unfold trialDivisionCandidatesUpTo
  rw [List.mem_flatMap]
  refine ⟨p.degree?.getD 0 - 1, ?_, ?_⟩
  · rw [List.mem_range]
    omega
  · apply mem_trialDivisionCandidatesOfDegree_of_bounded
    · omega
    · exact hlc
    · exact hrecord
    · exact hbound

/-- The polyProduct invariant for the candidate-peel auxiliary: emitted
factors and final residual multiply back to the original target. -/
private theorem trialDivisionPeelAux_product
    (target : ZPoly) (candidates : List ZPoly) :
    ∀ factors residual,
      trialDivisionPeelAux target candidates = (factors, residual) →
        residual * Array.polyProduct factors = target := by
  induction candidates generalizing target with
  | nil =>
      intro factors residual hsplit
      simp [trialDivisionPeelAux] at hsplit
      rcases hsplit with ⟨rfl, rfl⟩
      exact DensePoly.mul_one_right_poly (S := Int) target
  | cons c cs ih =>
      intro factors residual hsplit
      unfold trialDivisionPeelAux at hsplit
      cases hquot : exactQuotient? target c with
      | none =>
          simp [hquot] at hsplit
          exact ih target factors residual hsplit
      | some q =>
          simp [hquot] at hsplit
          cases hrest : trialDivisionPeelAux q cs with
          | mk rfact rres =>
              simp [hrest] at hsplit
              rcases hsplit with ⟨hfactors, hresidual⟩
              subst factors
              subst residual
              have hih : rres * Array.polyProduct rfact = q :=
                ih q rfact rres hrest
              have hqcq : q * c = target := exactQuotient?_product hquot
              calc
                rres * Array.polyProduct (#[c] ++ rfact)
                    = rres * (c * Array.polyProduct rfact) := by
                      rw [ZPoly.polyProduct_append, ZPoly.polyProduct_singleton]
                _ = rres * (Array.polyProduct rfact * c) := by
                      rw [DensePoly.mul_comm_poly (S := Int) c
                        (Array.polyProduct rfact)]
                _ = (rres * Array.polyProduct rfact) * c := by
                      rw [DensePoly.mul_assoc_poly (S := Int)]
                _ = q * c := by rw [hih]
                _ = target := hqcq

/-- Each emitted factor of the candidate-peel auxiliary is a member of the
input candidate list. -/
private theorem trialDivisionPeelAux_factor_mem
    (target : ZPoly) (candidates : List ZPoly) :
    ∀ factors residual,
      trialDivisionPeelAux target candidates = (factors, residual) →
        ∀ factor ∈ factors.toList, factor ∈ candidates := by
  induction candidates generalizing target with
  | nil =>
      intro factors residual hsplit factor hmem
      simp [trialDivisionPeelAux] at hsplit
      rcases hsplit with ⟨rfl, rfl⟩
      simp at hmem
  | cons c cs ih =>
      intro factors residual hsplit factor hmem
      unfold trialDivisionPeelAux at hsplit
      cases hquot : exactQuotient? target c with
      | none =>
          simp [hquot] at hsplit
          exact List.mem_cons_of_mem c
            (ih target factors residual hsplit factor hmem)
      | some q =>
          simp [hquot] at hsplit
          cases hrest : trialDivisionPeelAux q cs with
          | mk rfact rres =>
              simp [hrest] at hsplit
              rcases hsplit with ⟨hfactors, hresidual⟩
              subst factors
              subst residual
              rw [Array.toList_append] at hmem
              simp at hmem
              cases hmem with
              | inl hself =>
                  rw [hself]
                  exact List.mem_cons_self
              | inr hrest_mem =>
                  exact List.mem_cons_of_mem c
                    (ih q rfact rres hrest factor (by simpa using hrest_mem))

/-- A square-free integer polynomial over `Rat[x]` is not divisible by the
square of any positive-degree integer polynomial.  This is the generic
no-repeated-divisor bridge needed by the trial-division slow path: if
`q * q ∣ core`, then `toRatPoly q` divides both `toRatPoly core` and its
derivative, forcing the gcd in `SquareFreeRat core` to have size at least two. -/
private theorem square_not_dvd_of_squareFreeRat
    {core q : ZPoly} (hcore_ne : core ≠ 0)
    (hsq : Hex.ZPoly.SquareFreeRat core)
    (hq_degree : 0 < q.degree?.getD 0) :
    ¬ (q * q) ∣ core := by
  intro hdvd
  rcases hdvd with ⟨g, hg⟩
  let qRat := ZPoly.toRatPoly q
  let gRat := ZPoly.toRatPoly g
  let coreRat := ZPoly.toRatPoly core
  have hcoreRat_eq : coreRat = qRat * (qRat * gRat) := by
    show ZPoly.toRatPoly core = _
    rw [hg, ZPoly.toRatPoly_mul, ZPoly.toRatPoly_mul, DensePoly.mul_assoc_poly]
  have hqRat_dvd_qg : qRat ∣ qRat * gRat := ⟨gRat, rfl⟩
  have hqRat_dvd_core : qRat ∣ coreRat := by
    rw [hcoreRat_eq]
    exact ⟨qRat * gRat, rfl⟩
  have hqRat_dvd_derivative : qRat ∣ DensePoly.derivative coreRat := by
    rw [hcoreRat_eq, DensePoly.derivative_mul qRat (qRat * gRat)]
    apply DensePoly.dvd_add_poly
    · exact DensePoly.dvd_mul_left_poly (DensePoly.derivative qRat) hqRat_dvd_qg
    · exact ⟨DensePoly.derivative (qRat * gRat), rfl⟩
  have hqRat_dvd_gcd :
      qRat ∣ DensePoly.gcd coreRat (DensePoly.derivative coreRat) :=
    DensePoly.dvd_gcd qRat _ _ hqRat_dvd_core hqRat_dvd_derivative
  have hq_size_ge_two : 2 ≤ q.size := by
    unfold DensePoly.degree? at hq_degree
    by_cases hsize : q.size = 0
    · simp [hsize] at hq_degree
    · simp [hsize] at hq_degree
      omega
  have hqRat_size_ne : qRat.size ≠ 0 := by
    rw [ZPoly.size_toRatPoly]
    omega
  have hcoreRat_ne : coreRat ≠ 0 :=
    ZPoly.toRatPoly_ne_zero_of_ne_zero core hcore_ne
  have hgcd_dvd_core :=
    DensePoly.gcd_dvd_left coreRat (DensePoly.derivative coreRat)
  have hgcd_ne :
      DensePoly.gcd coreRat (DensePoly.derivative coreRat) ≠ 0 := by
    intro h
    apply hcoreRat_ne
    rcases hgcd_dvd_core with ⟨k, hk⟩
    rw [h, DensePoly.zero_mul] at hk
    exact hk
  have hgcd_size_ne :
      (DensePoly.gcd coreRat (DensePoly.derivative coreRat)).size ≠ 0 := by
    intro hsize
    apply hgcd_ne
    apply DensePoly.ext_coeff
    intro n
    rw [DensePoly.coeff_eq_zero_of_size_le _ (by omega)]
    exact (DensePoly.coeff_zero n).symm
  have hsize_le :=
    ZPoly.rat_size_le_of_dvd_nonzero hqRat_size_ne hgcd_size_ne hqRat_dvd_gcd
  have hsq' :
      (DensePoly.gcd coreRat (DensePoly.derivative coreRat)).size ≤ 1 := hsq
  rw [ZPoly.size_toRatPoly] at hsize_le
  omega

/-- Any member of a factor list divides the ordered `Array.polyProduct` of that
list. -/
private theorem dvd_polyProduct_toArray_of_mem {q : ZPoly} :
    ∀ factors : List ZPoly,
      q ∈ factors → q ∣ Array.polyProduct factors.toArray
  | [], hmem => by
      exact absurd hmem List.not_mem_nil
  | head :: tail, hmem => by
      rw [ZPoly.polyProduct_cons_toArray]
      rcases List.mem_cons.mp hmem with hhead | htail
      · subst q
        exact ⟨Array.polyProduct tail.toArray, rfl⟩
      · rcases dvd_polyProduct_toArray_of_mem tail htail with ⟨k, hk⟩
        refine ⟨head * k, ?_⟩
        rw [hk, ← DensePoly.mul_assoc_poly (S := Int) head q k,
          DensePoly.mul_comm_poly (S := Int) head q, DensePoly.mul_assoc_poly (S := Int) q head k]

/-- A candidate that was tried by `trialDivisionPeelAux` but not emitted does
not exactly divide the final residual.  This is the executable "no missed
candidate" statement available without squarefreeness: emitted candidates may
still divide the residual when the input target contains repeated factors,
because each candidate is tried only once. -/
private theorem trialDivisionPeelAux_no_missed_unemitted
    (target : ZPoly) (candidates : List ZPoly)
    (hcand :
      ∀ c ∈ candidates,
        0 < c.degree?.getD 0 ∧ 0 < DensePoly.leadingCoeff c) :
    ∀ factors residual,
      trialDivisionPeelAux target candidates = (factors, residual) →
        ∀ c ∈ candidates, c ∉ factors.toList →
          exactQuotient? residual c = none := by
  induction candidates generalizing target with
  | nil =>
      intro factors residual hsplit cand hc
      simp at hc
  | cons head tail ih =>
      intro factors residual hsplit cand hc hnot_mem
      have htail_cand :
          ∀ c ∈ tail,
            0 < c.degree?.getD 0 ∧ 0 < DensePoly.leadingCoeff c := by
        intro c hc
        exact hcand c (List.mem_cons_of_mem head hc)
      unfold trialDivisionPeelAux at hsplit
      cases hhead : exactQuotient? target head with
      | none =>
          simp [hhead] at hsplit
          have hc_dec : cand = head ∨ cand ∈ tail := by
            simpa using hc
          rcases hc_dec with hc_eq | hc_tail
          · cases hresquot : exactQuotient? residual head with
            | none =>
                rw [hc_eq]
                exact hresquot
            | some q =>
                exfalso
                have hprod :
                    residual * Array.polyProduct factors = target :=
                  trialDivisionPeelAux_product target tail factors residual hsplit
                have hres_mul : q * head = residual :=
                  exactQuotient?_product hresquot
                have hmul :
                    (q * Array.polyProduct factors) * head = target := by
                  calc
                    (q * Array.polyProduct factors) * head
                        = q * (Array.polyProduct factors * head) := by
                            rw [DensePoly.mul_assoc_poly (S := Int)]
                    _ = q * (head * Array.polyProduct factors) := by
                            rw [DensePoly.mul_comm_poly (S := Int)
                              (Array.polyProduct factors) head]
                    _ = (q * head) * Array.polyProduct factors := by
                            rw [← DensePoly.mul_assoc_poly (S := Int)]
                    _ = residual * Array.polyProduct factors := by
                            rw [hres_mul]
                    _ = target := hprod
                have hprops := hcand head List.mem_cons_self
                have hsome :
                    exactQuotient? target head =
                      some (q * Array.polyProduct factors) :=
                  exactQuotient?_eq_some_of_pos_lc_pos_degree_mul_eq
                    hprops.2 hprops.1 hmul
                rw [hhead] at hsome
                contradiction
          · exact ih target htail_cand factors residual hsplit cand hc_tail hnot_mem
      | some quotient =>
          simp [hhead] at hsplit
          cases hrest : trialDivisionPeelAux quotient tail with
          | mk restFactors restResidual =>
              simp [hrest] at hsplit
              rcases hsplit with ⟨hfactors, hresidual⟩
              subst factors
              subst residual
              have hc_dec : cand = head ∨ cand ∈ tail := by
                simpa using hc
              rcases hc_dec with hc_eq | hc_tail
              · rw [hc_eq] at hnot_mem
                exfalso
                apply hnot_mem
                rw [Array.toList_append]
                simp
              · have hnot_tail : cand ∉ restFactors.toList := by
                  intro hmem_tail
                  apply hnot_mem
                  rw [Array.toList_append]
                  simp [hmem_tail]
                exact ih quotient htail_cand restFactors restResidual hrest
                  cand hc_tail hnot_tail

/-- Under squarefreeness of the peel target, a positive-degree emitted candidate
cannot also divide the final residual.  Combining a residual divisor with the
product invariant would make `candidate * candidate` divide the original target,
contradicting `SquareFreeRat`. -/
private theorem trialDivisionPeelAux_no_emitted_residual_divisor_of_squareFreeRat
    (target : ZPoly) (candidates : List ZPoly)
    (htarget_ne : target ≠ 0) (hsq : Hex.ZPoly.SquareFreeRat target)
    (hcand_degree : ∀ c ∈ candidates, 0 < c.degree?.getD 0) :
    ∀ factors residual,
      trialDivisionPeelAux target candidates = (factors, residual) →
        ∀ c ∈ candidates, c ∈ factors.toList → ¬ c ∣ residual := by
  intro factors residual hsplit c hcand hemitted hdiv_residual
  rcases hdiv_residual with ⟨r, hresidual⟩
  have hprod : residual * Array.polyProduct factors = target :=
    trialDivisionPeelAux_product target candidates factors residual hsplit
  have hcdvd_prod : c ∣ Array.polyProduct factors :=
    dvd_polyProduct_toArray_of_mem factors.toList hemitted
  rcases hcdvd_prod with ⟨k, hprod_c⟩
  have hsquare_dvd : c * c ∣ target := by
    refine ⟨r * k, ?_⟩
    rw [← hprod, hresidual, hprod_c]
    calc
      (c * r) * (c * k) = c * (r * (c * k)) := by
          rw [DensePoly.mul_assoc_poly (S := Int)]
      _ = c * ((c * k) * r) := by
          rw [DensePoly.mul_comm_poly (S := Int) r (c * k)]
      _ = c * (c * (k * r)) := by
          rw [DensePoly.mul_assoc_poly (S := Int) c k r]
      _ = (c * c) * (k * r) := by
          rw [← DensePoly.mul_assoc_poly (S := Int) c c (k * r)]
      _ = (c * c) * (r * k) := by
          rw [DensePoly.mul_comm_poly (S := Int) k r]
  exact square_not_dvd_of_squareFreeRat htarget_ne hsq (hcand_degree c hcand) hsquare_dvd

/-- If `candidate` does not divide `target`, the executable exact-quotient check
must return `none`. -/
private theorem exactQuotient?_eq_none_of_not_dvd_core
    {target candidate : ZPoly} (hnot_dvd : ¬ candidate ∣ target) :
    exactQuotient? target candidate = none := by
  cases hcase : exactQuotient? target candidate with
  | none => rfl
  | some quotient =>
      exfalso
      apply hnot_dvd
      have hmul : quotient * candidate = target := exactQuotient?_product hcase
      exact ⟨quotient, by rw [DensePoly.mul_comm_poly (S := Int), hmul]⟩

/-- For a square-free peel target, no tried candidate exactly divides the final
residual.  Unemitted candidates are handled by the executable no-missed
invariant; emitted candidates are ruled out by squarefreeness because another
copy in the residual would make a square divisor of the original target. -/
private theorem trialDivisionPeelAux_no_residual_candidate_of_squareFreeRat
    (target : ZPoly) (candidates : List ZPoly)
    (htarget_ne : target ≠ 0) (hsq : Hex.ZPoly.SquareFreeRat target)
    (hcand :
      ∀ c ∈ candidates,
        0 < c.degree?.getD 0 ∧ 0 < DensePoly.leadingCoeff c) :
    ∀ factors residual,
      trialDivisionPeelAux target candidates = (factors, residual) →
        ∀ c ∈ candidates, exactQuotient? residual c = none := by
  intro factors residual hsplit c hc
  by_cases hemitted : c ∈ factors.toList
  · have hnot_dvd :
        ¬ c ∣ residual :=
      trialDivisionPeelAux_no_emitted_residual_divisor_of_squareFreeRat
        target candidates htarget_ne hsq
        (fun c hc => (hcand c hc).1) factors residual hsplit c hc hemitted
    exact exactQuotient?_eq_none_of_not_dvd_core hnot_dvd
  · exact trialDivisionPeelAux_no_missed_unemitted
      target candidates hcand factors residual hsplit c hc hemitted

/-- When the peel target has positive leading coefficient and every candidate
in the input list has positive leading coefficient, the residual emitted by
`trialDivisionPeelAux` retains a positive leading coefficient. -/
private theorem trialDivisionPeelAux_residual_leadingCoeff_pos
    (target : ZPoly) (candidates : List ZPoly)
    (htarget_pos : 0 < DensePoly.leadingCoeff target)
    (hcand_pos : ∀ c ∈ candidates, 0 < DensePoly.leadingCoeff c) :
    ∀ factors residual,
      trialDivisionPeelAux target candidates = (factors, residual) →
        0 < DensePoly.leadingCoeff residual := by
  induction candidates generalizing target with
  | nil =>
      intro factors residual hsplit
      simp [trialDivisionPeelAux] at hsplit
      rcases hsplit with ⟨rfl, rfl⟩
      exact htarget_pos
  | cons c cs ih =>
      intro factors residual hsplit
      have hc_pos : 0 < DensePoly.leadingCoeff c :=
        hcand_pos c List.mem_cons_self
      have hcs_pos : ∀ c' ∈ cs, 0 < DensePoly.leadingCoeff c' :=
        fun c' h => hcand_pos c' (List.mem_cons_of_mem c h)
      unfold trialDivisionPeelAux at hsplit
      cases hquot : exactQuotient? target c with
      | none =>
          simp [hquot] at hsplit
          exact ih target htarget_pos hcs_pos factors residual hsplit
      | some q =>
          simp [hquot] at hsplit
          cases hrest : trialDivisionPeelAux q cs with
          | mk rfact rres =>
              simp [hrest] at hsplit
              rcases hsplit with ⟨hfactors, hresidual⟩
              subst factors
              subst residual
              have hqcq : q * c = target := exactQuotient?_product hquot
              have htarget_ne : target ≠ 0 := by
                intro hz
                rw [hz] at htarget_pos
                rw [DensePoly.leadingCoeff_zero] at htarget_pos
                omega
              have hc_ne : c ≠ 0 := by
                intro hz
                rw [hz] at hc_pos
                rw [DensePoly.leadingCoeff_zero] at hc_pos
                omega
              have hq_ne : q ≠ 0 := by
                intro hz
                apply htarget_ne
                rw [← hqcq, hz]
                exact DensePoly.zero_mul _
              have hlc_mul :
                  DensePoly.leadingCoeff q * DensePoly.leadingCoeff c =
                    DensePoly.leadingCoeff target := by
                rw [← hqcq]
                exact (ZPoly.leadingCoeff_mul_of_nonzero q c hq_ne hc_ne).symm
              have hq_pos : 0 < DensePoly.leadingCoeff q := by
                rcases Int.lt_or_le 0 (DensePoly.leadingCoeff q) with hp | hle
                · exact hp
                · exfalso
                  have hc_nn : 0 ≤ DensePoly.leadingCoeff c :=
                    Int.le_of_lt hc_pos
                  have hna : 0 ≤ -DensePoly.leadingCoeff q := by omega
                  have hprod_neg_nn :
                      0 ≤ -DensePoly.leadingCoeff q *
                        DensePoly.leadingCoeff c :=
                    Int.mul_nonneg hna hc_nn
                  have hneg_eq :
                      -DensePoly.leadingCoeff q * DensePoly.leadingCoeff c =
                        -(DensePoly.leadingCoeff q * DensePoly.leadingCoeff c) :=
                    Int.neg_mul _ _
                  rw [hneg_eq, hlc_mul] at hprod_neg_nn
                  omega
              exact ih q hq_pos hcs_pos rfact rres hrest

/-- Each emitted factor of the candidate-peel auxiliary satisfies the
property `P` whenever every input candidate does. -/
private theorem trialDivisionPeelAux_factor_property
    {P : ZPoly → Prop} (target : ZPoly) (candidates : List ZPoly)
    (hcand : ∀ c ∈ candidates, P c) :
    ∀ factors residual,
      trialDivisionPeelAux target candidates = (factors, residual) →
        ∀ factor ∈ factors.toList, P factor := by
  intro factors residual hsplit factor hmem
  exact hcand factor
    (trialDivisionPeelAux_factor_mem target candidates factors residual hsplit
      factor hmem)

/-- PolyProduct identity for the standalone integer trial-division core. -/
theorem exhaustiveIntegerTrialCoreFactorsWithBound_polyProduct
    (core : ZPoly) (B : Nat) :
    Array.polyProduct (exhaustiveIntegerTrialCoreFactorsWithBound core B) =
      core := by
  let split := splitIntegerRootFactorsAux core (integerRootCandidates core)
    (integerRootCandidates core).length
  let peel := trialDivisionPeelAux split.2
    (trialDivisionCandidatesUpTo B (split.2.degree?.getD 0 / 2))
  have hsplit_prod : split.2 * Array.polyProduct split.1 = core :=
    splitIntegerRootFactorsAux_product core (integerRootCandidates core)
      (integerRootCandidates core).length split.1 split.2 rfl
  have hpeel_prod : peel.2 * Array.polyProduct peel.1 = split.2 :=
    trialDivisionPeelAux_product split.2
      (trialDivisionCandidatesUpTo B (split.2.degree?.getD 0 / 2))
      peel.1 peel.2 rfl
  change Array.polyProduct
      (if peel.2 = 1 then split.1 ++ peel.1
        else (split.1 ++ peel.1).push peel.2) = core
  by_cases hres_one : peel.2 = 1
  · rw [if_pos hres_one]
    rw [hres_one, ZPoly.one_mul_zpoly] at hpeel_prod
    rw [ZPoly.polyProduct_append, hpeel_prod,
        DensePoly.mul_comm_poly (S := Int)]
    exact hsplit_prod
  · rw [if_neg hres_one]
    rw [polyProduct_push, ZPoly.polyProduct_append,
        DensePoly.mul_assoc_poly (S := Int),
        DensePoly.mul_comm_poly (S := Int) (Array.polyProduct peel.1) peel.2,
        hpeel_prod, DensePoly.mul_comm_poly (S := Int)]
    exact hsplit_prod

/-- Each factor emitted by the standalone integer trial-division core is
fixed by `normalizeFactorSign`, provided `core` has positive leading
coefficient. -/
theorem exhaustiveIntegerTrialCoreFactorsWithBound_normalizeFactorSign
    (core : ZPoly) (B : Nat)
    (hcore_pos : 0 < DensePoly.leadingCoeff core) :
    ∀ factor ∈ (exhaustiveIntegerTrialCoreFactorsWithBound core B).toList,
      normalizeFactorSign factor = factor := by
  let split := splitIntegerRootFactorsAux core (integerRootCandidates core)
    (integerRootCandidates core).length
  let candidates :=
    trialDivisionCandidatesUpTo B (split.2.degree?.getD 0 / 2)
  let peel := trialDivisionPeelAux split.2 candidates
  have hsplit_norm :
      ∀ factor ∈ split.1.toList, normalizeFactorSign factor = factor :=
    splitIntegerRootFactorsAux_normalizeFactorSign core
      (integerRootCandidates core) (integerRootCandidates core).length
      split.1 split.2 rfl
  have hsplit_prod : split.2 * Array.polyProduct split.1 = core :=
    splitIntegerRootFactorsAux_product core (integerRootCandidates core)
      (integerRootCandidates core).length split.1 split.2 rfl
  have hsplit_lc_pos :
      0 < DensePoly.leadingCoeff (Array.polyProduct split.1) :=
    splitIntegerRootFactorsAux_polyProduct_leadingCoeff_pos core
      (integerRootCandidates core) (integerRootCandidates core).length
      split.1 split.2 rfl
  have hcore_ne : core ≠ 0 := by
    intro hz
    rw [hz] at hcore_pos
    rw [DensePoly.leadingCoeff_zero] at hcore_pos
    omega
  have hsplit1_ne : Array.polyProduct split.1 ≠ 0 := by
    intro hz
    rw [hz] at hsplit_lc_pos
    rw [DensePoly.leadingCoeff_zero] at hsplit_lc_pos
    omega
  have hsplit2_ne : split.2 ≠ 0 := by
    intro hz
    apply hcore_ne
    rw [← hsplit_prod, hz]
    exact DensePoly.zero_mul _
  have hsplit2_pos : 0 < DensePoly.leadingCoeff split.2 := by
    have hlc :
        DensePoly.leadingCoeff core =
          DensePoly.leadingCoeff split.2 *
            DensePoly.leadingCoeff (Array.polyProduct split.1) := by
      rw [← hsplit_prod]
      exact ZPoly.leadingCoeff_mul_of_nonzero split.2
        (Array.polyProduct split.1) hsplit2_ne hsplit1_ne
    rcases Int.lt_or_le 0 (DensePoly.leadingCoeff split.2) with hp | hle
    · exact hp
    · exfalso
      have hnn : 0 ≤ DensePoly.leadingCoeff (Array.polyProduct split.1) :=
        Int.le_of_lt hsplit_lc_pos
      have hna : 0 ≤ -DensePoly.leadingCoeff split.2 := by omega
      have hprod_neg_nn :
          0 ≤ -DensePoly.leadingCoeff split.2 *
            DensePoly.leadingCoeff (Array.polyProduct split.1) :=
        Int.mul_nonneg hna hnn
      have hneg_eq :
          -DensePoly.leadingCoeff split.2 *
              DensePoly.leadingCoeff (Array.polyProduct split.1) =
            -(DensePoly.leadingCoeff split.2 *
              DensePoly.leadingCoeff (Array.polyProduct split.1)) :=
        Int.neg_mul _ _
      rw [hneg_eq, ← hlc] at hprod_neg_nn
      omega
  have hcand_norm :
      ∀ c ∈ candidates, normalizeFactorSign c = c := by
    intro c hc
    obtain ⟨_, hlc, _⟩ := mem_trialDivisionCandidatesUpTo hc
    unfold normalizeFactorSign
    have hnot_neg : ¬ DensePoly.leadingCoeff c < 0 := by omega
    rw [if_neg hnot_neg]
  have hcand_pos :
      ∀ c ∈ candidates, 0 < DensePoly.leadingCoeff c :=
    fun c hc => (mem_trialDivisionCandidatesUpTo hc).2.1
  have hpeel_norm :
      ∀ factor ∈ peel.1.toList, normalizeFactorSign factor = factor :=
    trialDivisionPeelAux_factor_property
      (P := fun p => normalizeFactorSign p = p)
      split.2 candidates hcand_norm peel.1 peel.2 rfl
  have hpeel_res_pos : 0 < DensePoly.leadingCoeff peel.2 :=
    trialDivisionPeelAux_residual_leadingCoeff_pos split.2 candidates
      hsplit2_pos hcand_pos peel.1 peel.2 rfl
  change ∀ factor ∈ (if peel.2 = 1 then split.1 ++ peel.1
      else (split.1 ++ peel.1).push peel.2).toList,
    normalizeFactorSign factor = factor
  intro factor hmem
  by_cases hres_one : peel.2 = 1
  · rw [if_pos hres_one] at hmem
    rw [Array.toList_append] at hmem
    rcases List.mem_append.mp hmem with hlin | hpeel
    · exact hsplit_norm factor hlin
    · exact hpeel_norm factor hpeel
  · rw [if_neg hres_one] at hmem
    rw [Array.toList_push, Array.toList_append] at hmem
    rcases List.mem_append.mp hmem with hpref | hres
    · rcases List.mem_append.mp hpref with hlin | hpeel
      · exact hsplit_norm factor hlin
      · exact hpeel_norm factor hpeel
    · have hfactor_eq : factor = peel.2 := by
        rcases List.mem_singleton.mp hres with rfl
        rfl
      rw [hfactor_eq]
      unfold normalizeFactorSign
      have hnot_neg : ¬ DensePoly.leadingCoeff peel.2 < 0 := by omega
      rw [if_neg hnot_neg]

/-- Each factor emitted by the standalone integer trial-division core
satisfies `shouldRecordPolynomialFactor`, provided `core` has positive
leading coefficient. -/
theorem exhaustiveIntegerTrialCoreFactorsWithBound_shouldRecord
    (core : ZPoly) (B : Nat)
    (hcore_pos : 0 < DensePoly.leadingCoeff core) :
    ∀ factor ∈ (exhaustiveIntegerTrialCoreFactorsWithBound core B).toList,
      shouldRecordPolynomialFactor factor = true := by
  let split := splitIntegerRootFactorsAux core (integerRootCandidates core)
    (integerRootCandidates core).length
  let candidates :=
    trialDivisionCandidatesUpTo B (split.2.degree?.getD 0 / 2)
  let peel := trialDivisionPeelAux split.2 candidates
  have hsplit_record :
      ∀ factor ∈ split.1.toList, shouldRecordPolynomialFactor factor = true :=
    splitIntegerRootFactorsAux_shouldRecord core (integerRootCandidates core)
      (integerRootCandidates core).length split.1 split.2 rfl
  have hsplit_prod : split.2 * Array.polyProduct split.1 = core :=
    splitIntegerRootFactorsAux_product core (integerRootCandidates core)
      (integerRootCandidates core).length split.1 split.2 rfl
  have hsplit_lc_pos :
      0 < DensePoly.leadingCoeff (Array.polyProduct split.1) :=
    splitIntegerRootFactorsAux_polyProduct_leadingCoeff_pos core
      (integerRootCandidates core) (integerRootCandidates core).length
      split.1 split.2 rfl
  have hcore_ne : core ≠ 0 := by
    intro hz
    rw [hz] at hcore_pos
    rw [DensePoly.leadingCoeff_zero] at hcore_pos
    omega
  have hsplit1_ne : Array.polyProduct split.1 ≠ 0 := by
    intro hz
    rw [hz] at hsplit_lc_pos
    rw [DensePoly.leadingCoeff_zero] at hsplit_lc_pos
    omega
  have hsplit2_ne : split.2 ≠ 0 := by
    intro hz
    apply hcore_ne
    rw [← hsplit_prod, hz]
    exact DensePoly.zero_mul _
  have hsplit2_pos : 0 < DensePoly.leadingCoeff split.2 := by
    have hlc :
        DensePoly.leadingCoeff core =
          DensePoly.leadingCoeff split.2 *
            DensePoly.leadingCoeff (Array.polyProduct split.1) := by
      rw [← hsplit_prod]
      exact ZPoly.leadingCoeff_mul_of_nonzero split.2
        (Array.polyProduct split.1) hsplit2_ne hsplit1_ne
    rcases Int.lt_or_le 0 (DensePoly.leadingCoeff split.2) with hp | hle
    · exact hp
    · exfalso
      have hnn : 0 ≤ DensePoly.leadingCoeff (Array.polyProduct split.1) :=
        Int.le_of_lt hsplit_lc_pos
      have hna : 0 ≤ -DensePoly.leadingCoeff split.2 := by omega
      have hprod_neg_nn :
          0 ≤ -DensePoly.leadingCoeff split.2 *
            DensePoly.leadingCoeff (Array.polyProduct split.1) :=
        Int.mul_nonneg hna hnn
      have hneg_eq :
          -DensePoly.leadingCoeff split.2 *
              DensePoly.leadingCoeff (Array.polyProduct split.1) =
            -(DensePoly.leadingCoeff split.2 *
              DensePoly.leadingCoeff (Array.polyProduct split.1)) :=
        Int.neg_mul _ _
      rw [hneg_eq, ← hlc] at hprod_neg_nn
      omega
  have hcand_record :
      ∀ c ∈ candidates, shouldRecordPolynomialFactor c = true :=
    fun c hc => (mem_trialDivisionCandidatesUpTo hc).2.2
  have hcand_pos :
      ∀ c ∈ candidates, 0 < DensePoly.leadingCoeff c :=
    fun c hc => (mem_trialDivisionCandidatesUpTo hc).2.1
  have hpeel_record :
      ∀ factor ∈ peel.1.toList,
        shouldRecordPolynomialFactor factor = true :=
    trialDivisionPeelAux_factor_property
      (P := fun p => shouldRecordPolynomialFactor p = true)
      split.2 candidates hcand_record peel.1 peel.2 rfl
  have hpeel_res_pos : 0 < DensePoly.leadingCoeff peel.2 :=
    trialDivisionPeelAux_residual_leadingCoeff_pos split.2 candidates
      hsplit2_pos hcand_pos peel.1 peel.2 rfl
  change ∀ factor ∈ (if peel.2 = 1 then split.1 ++ peel.1
      else (split.1 ++ peel.1).push peel.2).toList,
    shouldRecordPolynomialFactor factor = true
  intro factor hmem
  by_cases hres_one : peel.2 = 1
  · rw [if_pos hres_one] at hmem
    rw [Array.toList_append] at hmem
    rcases List.mem_append.mp hmem with hlin | hpeel
    · exact hsplit_record factor hlin
    · exact hpeel_record factor hpeel
  · rw [if_neg hres_one] at hmem
    rw [Array.toList_push, Array.toList_append] at hmem
    rcases List.mem_append.mp hmem with hpref | hres
    · rcases List.mem_append.mp hpref with hlin | hpeel
      · exact hsplit_record factor hlin
      · exact hpeel_record factor hpeel
    · have hfactor_eq : factor = peel.2 := by
        rcases List.mem_singleton.mp hres with rfl
        rfl
      rw [hfactor_eq]
      have hpeel_ne_zero : peel.2 ≠ 0 := by
        intro hz
        rw [hz] at hpeel_res_pos
        rw [DensePoly.leadingCoeff_zero] at hpeel_res_pos
        omega
      have hpeel_ne_neg_one : peel.2 ≠ DensePoly.C (-1 : Int) := by
        intro hneg
        have hlc_neg : DensePoly.leadingCoeff peel.2 = -1 := by
          rw [hneg]
          change DensePoly.leadingCoeff (DensePoly.C (-1 : Int)) = -1
          simp [DensePoly.leadingCoeff,
            DensePoly.coeffs_C_of_ne_zero (by decide : (-1 : Int) ≠ 0)]
        rw [hlc_neg] at hpeel_res_pos
        omega
      unfold shouldRecordPolynomialFactor
      simp [hpeel_ne_zero, hres_one, hpeel_ne_neg_one]

/-- Transitivity of `∣` on `ZPoly`.  Composes the witness multiplications
explicitly because the file does not import a general `dvd_trans`. -/
private theorem ZPoly_dvd_trans {a b c : ZPoly} (hab : a ∣ b) (hbc : b ∣ c) :
    a ∣ c := by
  rcases hab with ⟨q, hq⟩
  rcases hbc with ⟨r, hr⟩
  refine ⟨q * r, ?_⟩
  rw [hr, hq, DensePoly.mul_assoc_poly (S := Int)]

/-- Each factor emitted by the candidate peel divides the peel target.  Direct
consequence of the product invariant `residual * polyProduct factors = target`
together with `dvd_polyProduct_toArray_of_mem`. -/
private theorem trialDivisionPeelAux_factor_dvd_target
    (target : ZPoly) (candidates : List ZPoly)
    (factors : Array ZPoly) (residual : ZPoly)
    (hsplit : trialDivisionPeelAux target candidates = (factors, residual)) :
    ∀ b ∈ factors.toList, b ∣ target := by
  intro b hb
  have hprod :=
    trialDivisionPeelAux_product target candidates factors residual hsplit
  have hb_pp : b ∣ Array.polyProduct factors :=
    dvd_polyProduct_toArray_of_mem factors.toList hb
  rcases hb_pp with ⟨k, hk⟩
  refine ⟨residual * k, ?_⟩
  calc target
      = residual * Array.polyProduct factors := hprod.symm
    _ = residual * (b * k) := by rw [hk]
    _ = (residual * b) * k := by rw [← DensePoly.mul_assoc_poly (S := Int)]
    _ = (b * residual) * k := by
          rw [DensePoly.mul_comm_poly (S := Int) residual b]
    _ = b * (residual * k) := by rw [DensePoly.mul_assoc_poly (S := Int)]

/-- The peel residual divides the peel target.  Direct consequence of the
product invariant `residual * polyProduct factors = target`. -/
private theorem trialDivisionPeelAux_residual_dvd_target
    (target : ZPoly) (candidates : List ZPoly)
    (factors : Array ZPoly) (residual : ZPoly)
    (hsplit : trialDivisionPeelAux target candidates = (factors, residual)) :
    residual ∣ target := by
  have hprod :=
    trialDivisionPeelAux_product target candidates factors residual hsplit
  exact ⟨Array.polyProduct factors, hprod.symm⟩

/-- A nonzero divisor of size one of a primitive polynomial is a unit.  The
divisor reduces to `C c` with `c.natAbs ∣ content core = 1`, hence `c = ±1`. -/
private theorem isUnit_of_dvd_primitive_size_one
    {core g : ZPoly}
    (hcore_prim : ZPoly.Primitive core)
    (hdvd : g ∣ core) (hsize : g.size = 1) :
    ZPoly.IsUnit g := by
  have hg_eq : g = DensePoly.C (g.coeff 0) :=
    ZPoly.eq_C_of_size_eq_one g hsize
  have hg_ne_zero : g ≠ 0 := by
    intro hzero; rw [hzero] at hsize
    change (0 : Nat) = 1 at hsize; omega
  have hgc_ne : g.coeff 0 ≠ 0 := by
    intro hzero; apply hg_ne_zero; rw [hg_eq, hzero]; rfl
  rcases hdvd with ⟨h, hh⟩
  have hcore_eq : core = DensePoly.C (g.coeff 0) * h :=
    hh.trans (congrArg (· * h) hg_eq)
  have hcoeff_core : ∀ n, ((g.coeff 0).natAbs : Int) ∣ core.coeff n := by
    intro n
    have hcoeff : core.coeff n = g.coeff 0 * h.coeff n := by
      rw [hcore_eq, ZPoly.C_mul_eq_scale,
        DensePoly.coeff_scale (R := Int) (g.coeff 0) h n (Int.mul_zero _)]
    rw [hcoeff]
    exact Int.natAbs_dvd.mpr ⟨h.coeff n, rfl⟩
  have hcontent_dvd : ((g.coeff 0).natAbs : Int) ∣ ZPoly.content core :=
    ZPoly.dvd_content_of_nat_dvd_coeff core _ hcoeff_core
  rw [show ZPoly.content core = 1 from hcore_prim] at hcontent_dvd
  have hnat_dvd : (g.coeff 0).natAbs ∣ (1 : Nat) :=
    Int.ofNat_dvd.mp (by simpa using hcontent_dvd)
  have hnat_le : (g.coeff 0).natAbs ≤ 1 :=
    Nat.le_of_dvd (by omega) hnat_dvd
  have hnat_pos : 1 ≤ (g.coeff 0).natAbs := by
    rcases Nat.eq_zero_or_pos (g.coeff 0).natAbs with hz | hp
    · exact absurd (Int.natAbs_eq_zero.mp hz) hgc_ne
    · exact hp
  have hnat_eq : (g.coeff 0).natAbs = 1 := by omega
  rcases Int.natAbs_eq (g.coeff 0) with heq | heq
  · left; rw [hg_eq, heq, hnat_eq]; rfl
  · right; rw [hg_eq, heq, hnat_eq]; rfl

/-- Coefficient `natAbs` is invariant under `scale (-1 : Int)`. Used to
transport a universal coefficient bound across sign normalization. -/
private theorem natAbs_coeff_scale_neg_one (p : ZPoly) (i : Nat) :
    ((DensePoly.scale (-1 : Int) p).coeff i).natAbs = (p.coeff i).natAbs := by
  rw [DensePoly.coeff_scale (R := Int) (-1 : Int) p i (Int.mul_zero _)]
  rcases Int.natAbs_eq (p.coeff i) with hpos | hneg
  · rw [hpos]; simp [Int.natAbs_neg]
  · rw [hneg]; simp [Int.natAbs_neg]

/-- `scale (-1)` is an involution on `ZPoly`: applying it twice returns the
original polynomial. -/
theorem scale_neg_one_neg_one (p : ZPoly) :
    DensePoly.scale (-1 : Int) (DensePoly.scale (-1 : Int) p) = p := by
  apply DensePoly.ext_coeff
  intro n
  rw [DensePoly.coeff_scale (R := Int) (-1 : Int) _ n (Int.mul_zero _),
      DensePoly.coeff_scale (R := Int) (-1 : Int) p n (Int.mul_zero _)]
  show (-1 : Int) * ((-1 : Int) * p.coeff n) = p.coeff n
  rw [← Int.mul_assoc]
  show ((-1 : Int) * (-1 : Int)) * p.coeff n = p.coeff n
  rw [show ((-1 : Int) * (-1 : Int)) = 1 from by decide, Int.one_mul]

/-- The sign-negation polynomial divides the original: `scale (-1) p` and `p`
are associates via the `±1` unit pair.  Witnesses via the involution
`scale (-1) ∘ scale (-1) = id`. -/
private theorem dvd_scale_neg_one (p : ZPoly) :
    DensePoly.scale (-1 : Int) p ∣ p := by
  refine ⟨DensePoly.C (-1 : Int), ?_⟩
  rw [DensePoly.mul_comm_poly (S := Int), ZPoly.C_mul_eq_scale]
  exact (scale_neg_one_neg_one p).symm

/-- `trialDivisionPeelAux` `cons` reduction when the head candidate fails the
exact-division check.  Equational form of the `none` branch of the
recursion, useful for goal rewriting without unfolding the body's
right-hand occurrences. -/
private theorem trialDivisionPeelAux_cons_none
    (target c : ZPoly) (cs : List ZPoly)
    (hquot : exactQuotient? target c = none) :
    trialDivisionPeelAux target (c :: cs) = trialDivisionPeelAux target cs := by
  show (match exactQuotient? target c with
        | some quotient =>
            let rest := trialDivisionPeelAux quotient cs
            (#[c] ++ rest.1, rest.2)
        | none => trialDivisionPeelAux target cs) = trialDivisionPeelAux target cs
  rw [hquot]

/-- `trialDivisionPeelAux` `cons` reduction when the head candidate exactly
divides the running target.  Equational form of the `some` branch of the
recursion. -/
private theorem trialDivisionPeelAux_cons_some
    (target c q : ZPoly) (cs : List ZPoly)
    (hquot : exactQuotient? target c = some q) :
    trialDivisionPeelAux target (c :: cs) =
      (#[c] ++ (trialDivisionPeelAux q cs).1,
       (trialDivisionPeelAux q cs).2) := by
  show (match exactQuotient? target c with
        | some quotient =>
            let rest := trialDivisionPeelAux quotient cs
            (#[c] ++ rest.1, rest.2)
        | none => trialDivisionPeelAux target cs) =
       (#[c] ++ (trialDivisionPeelAux q cs).1,
        (trialDivisionPeelAux q cs).2)
  rw [hquot]

/-- Degree-ordered prefix-split decomposition of `trialDivisionPeelAux`.
Peeling a concatenated candidate list `pre ++ suf` is the same as first
peeling `pre` (producing `(preFactors, mid)`) and then peeling `suf` from
`mid`: the emitted factors concatenate and the residual matches.
This is the structural identity that the peel.1 case of the candidate-peel
irreducibility argument uses to argue that a strictly smaller-degree
candidate gets tested before any higher-degree emitted factor. -/
private theorem trialDivisionPeelAux_split
    (target : ZPoly) (pre suf : List ZPoly) :
    ∀ preFactors mid,
      trialDivisionPeelAux target pre = (preFactors, mid) →
        trialDivisionPeelAux target (pre ++ suf) =
          (preFactors ++ (trialDivisionPeelAux mid suf).1,
           (trialDivisionPeelAux mid suf).2) := by
  induction pre generalizing target with
  | nil =>
      intro preFactors mid hpre
      simp [trialDivisionPeelAux] at hpre
      rcases hpre with ⟨rfl, rfl⟩
      simp [List.nil_append]
  | cons c cs ih =>
      intro preFactors mid hpre
      cases hquot : exactQuotient? target c with
      | none =>
          rw [trialDivisionPeelAux_cons_none target c cs hquot] at hpre
          have hih := ih target preFactors mid hpre
          rw [List.cons_append,
              trialDivisionPeelAux_cons_none target c (cs ++ suf) hquot]
          exact hih
      | some q =>
          rw [trialDivisionPeelAux_cons_some target c q cs hquot] at hpre
          cases hrest : trialDivisionPeelAux q cs with
          | mk restFact restRes =>
              rw [hrest] at hpre
              simp at hpre
              rcases hpre with ⟨rfl, rfl⟩
              have hih := ih q restFact restRes hrest
              rw [List.cons_append,
                  trialDivisionPeelAux_cons_some target c q (cs ++ suf) hquot,
                  hih]
              generalize trialDivisionPeelAux restRes suf = tsuf
              rcases tsuf with ⟨sfact, sres⟩
              simp [Array.append_assoc]

/-- `DensePoly.scale (-1)` preserves dense size on `ZPoly`. Both directions
of the antisymmetric inequality come from the trim invariant: a strictly
larger size on either side forces a zero coefficient at the top index that
is also forced to be nonzero. -/
private theorem size_scale_neg_one (p : ZPoly) :
    (DensePoly.scale (-1 : Int) p).size = p.size := by
  apply Nat.le_antisymm
  · by_cases hle : (DensePoly.scale (-1 : Int) p).size ≤ p.size
    · exact hle
    · exfalso
      have hlt : p.size < (DensePoly.scale (-1 : Int) p).size :=
        Nat.lt_of_not_ge hle
      let i := (DensePoly.scale (-1 : Int) p).size - 1
      have hpos : 0 < (DensePoly.scale (-1 : Int) p).size := by
        change 0 < (DensePoly.scale (-1 : Int) p).size; omega
      have hp_le : p.size ≤ i := by change p.size ≤ _ - 1; omega
      have hp_zero : p.coeff i = 0 :=
        DensePoly.coeff_eq_zero_of_size_le p hp_le
      have hscale_ne :
          (DensePoly.scale (-1 : Int) p).coeff i ≠ 0 :=
        DensePoly.coeff_last_ne_zero_of_pos_size _ hpos
      rw [DensePoly.coeff_scale _ _ _ (Int.mul_zero (-1 : Int)), hp_zero] at hscale_ne
      exact hscale_ne (Int.mul_zero (-1 : Int))
  · by_cases hle : p.size ≤ (DensePoly.scale (-1 : Int) p).size
    · exact hle
    · exfalso
      have hlt : (DensePoly.scale (-1 : Int) p).size < p.size :=
        Nat.lt_of_not_ge hle
      let i := p.size - 1
      have hp_pos : 0 < p.size := by change 0 < p.size; omega
      have hscale_le : (DensePoly.scale (-1 : Int) p).size ≤ i := by
        change _ ≤ p.size - 1; omega
      have hscale_zero : (DensePoly.scale (-1 : Int) p).coeff i = 0 :=
        DensePoly.coeff_eq_zero_of_size_le _ hscale_le
      have hp_ne : p.coeff i ≠ 0 :=
        DensePoly.coeff_last_ne_zero_of_pos_size p hp_pos
      rw [DensePoly.coeff_scale _ _ _ (Int.mul_zero (-1 : Int))] at hscale_zero
      apply hp_ne
      have : (-1 : Int) * p.coeff i = 0 := hscale_zero
      omega

/-- The peel residual is irreducible when the running target is a primitive,
square-free divisor of the original core with positive leading coefficient
and the trial candidates exhaust every bounded positive-leading positive-
degree divisor.

Argument: a nontrivial decomposition `residual = a * b` would produce a
positive-leading positive-degree divisor `q` of `residual` whose
coefficients respect the universal divisor bound `B` and whose degree is
at most `target.degree?.getD 0 / 2`. Hence `q` belongs to
`trialDivisionCandidatesUpTo B (target.degree?.getD 0 / 2)`. Two cases:
either `q` was emitted (so `q ∣ polyProduct factors` and `q ∣ residual`,
hence `q * q ∣ target ∣ core`, contradicting `SquareFreeRat core`); or `q`
was not emitted (so by `trialDivisionPeelAux_no_missed_unemitted` we have
`exactQuotient? residual q = none`, contradicting `q ∣ residual` together
with positive leading coefficient and degree). -/
private theorem trialDivisionPeel_residual_irreducible
    {core target : ZPoly} {B : Nat}
    {factors : Array ZPoly} {residual : ZPoly}
    (hcore_ne : core ≠ 0)
    (hcore_prim : ZPoly.Primitive core)
    (hcore_sq : Hex.ZPoly.SquareFreeRat core)
    (htarget_dvd : target ∣ core)
    (htarget_pos : 0 < DensePoly.leadingCoeff target)
    (hbound : ∀ g, g ∣ core → ∀ i, (g.coeff i).natAbs ≤ B)
    (hsplit : trialDivisionPeelAux target
        (trialDivisionCandidatesUpTo B (target.degree?.getD 0 / 2)) =
          (factors, residual))
    (hres_ne_one : residual ≠ 1) :
    ZPoly.Irreducible residual := by
  let candidates := trialDivisionCandidatesUpTo B (target.degree?.getD 0 / 2)
  change trialDivisionPeelAux target candidates = (factors, residual) at hsplit
  have htarget_ne : target ≠ 0 := by
    intro h; rw [h] at htarget_pos
    rw [DensePoly.leadingCoeff_zero] at htarget_pos; omega
  have hcand_pos_lc : ∀ c ∈ candidates, 0 < DensePoly.leadingCoeff c :=
    fun c hc => (mem_trialDivisionCandidatesUpTo hc).2.1
  have hcand_pos_deg : ∀ c ∈ candidates, 0 < c.degree?.getD 0 :=
    fun c hc => (mem_trialDivisionCandidatesUpTo hc).1
  have hcand_pos :
      ∀ c ∈ candidates,
        0 < c.degree?.getD 0 ∧ 0 < DensePoly.leadingCoeff c :=
    fun c hc => ⟨hcand_pos_deg c hc, hcand_pos_lc c hc⟩
  have hres_lc_pos : 0 < DensePoly.leadingCoeff residual :=
    trialDivisionPeelAux_residual_leadingCoeff_pos target candidates
      htarget_pos hcand_pos_lc factors residual hsplit
  have hres_ne_zero : residual ≠ 0 := by
    intro hzero; rw [hzero] at hres_lc_pos
    rw [DensePoly.leadingCoeff_zero] at hres_lc_pos; omega
  have hres_dvd_target : residual ∣ target :=
    trialDivisionPeelAux_residual_dvd_target target candidates factors residual hsplit
  have hres_dvd_core : residual ∣ core :=
    ZPoly_dvd_trans hres_dvd_target htarget_dvd
  have hres_ne_neg_one : residual ≠ DensePoly.C (-1 : Int) := by
    intro hneg
    have hlc_neg : DensePoly.leadingCoeff residual = -1 := by
      rw [hneg]
      change DensePoly.leadingCoeff (DensePoly.C (-1 : Int)) = -1
      simp [DensePoly.leadingCoeff,
        DensePoly.coeffs_C_of_ne_zero (by decide : (-1 : Int) ≠ 0)]
    rw [hlc_neg] at hres_lc_pos; omega
  refine { not_zero := hres_ne_zero, not_unit := ?_, no_factors := ?_ }
  · intro hunit
    rcases hunit with h1 | hneg1
    · exact hres_ne_one h1
    · exact hres_ne_neg_one hneg1
  · intro a b hab
    by_cases hua : ZPoly.IsUnit a
    · exact Or.inl hua
    by_cases hub : ZPoly.IsUnit b
    · exact Or.inr hub
    exfalso
    have hna : ¬ ZPoly.IsUnit a := hua
    have hnb : ¬ ZPoly.IsUnit b := hub
    have ha_ne : a ≠ 0 := by
      intro hz; apply hres_ne_zero
      rw [hab, hz, DensePoly.zero_mul]
    have hb_ne : b ≠ 0 := by
      intro hz; apply hres_ne_zero
      rw [hab, hz, DensePoly.mul_comm_poly (S := Int), DensePoly.zero_mul]
    have ha_dvd_res : a ∣ residual := ⟨b, hab⟩
    have hb_dvd_res : b ∣ residual :=
      ⟨a, hab.trans (DensePoly.mul_comm_poly (S := Int) a b)⟩
    have ha_dvd_core : a ∣ core := ZPoly_dvd_trans ha_dvd_res hres_dvd_core
    have hb_dvd_core : b ∣ core := ZPoly_dvd_trans hb_dvd_res hres_dvd_core
    have ha_size_pos : 0 < a.size := ZPoly.size_pos_of_ne_zero a ha_ne
    have hb_size_pos : 0 < b.size := ZPoly.size_pos_of_ne_zero b hb_ne
    have ha_size_ge_two : 2 ≤ a.size := by
      by_cases h : 2 ≤ a.size
      · exact h
      · exfalso
        have hsize : a.size = 1 := by omega
        exact hna (isUnit_of_dvd_primitive_size_one hcore_prim ha_dvd_core hsize)
    have hb_size_ge_two : 2 ≤ b.size := by
      by_cases h : 2 ≤ b.size
      · exact h
      · exfalso
        have hsize : b.size = 1 := by omega
        exact hnb (isUnit_of_dvd_primitive_size_one hcore_prim hb_dvd_core hsize)
    have hab_size : (a * b).size = a.size + b.size - 1 :=
      ZPoly.mul_size_eq_top_succ_of_nonzero a b ha_size_pos hb_size_pos
    rw [← hab] at hab_size
    have hres_size_pos : 0 < residual.size :=
      ZPoly.size_pos_of_ne_zero residual hres_ne_zero
    -- Auxiliary: derive contradiction for either a or b (whichever is smaller)
    suffices hkey :
        ∀ small : ZPoly,
          small ∣ residual → ¬ ZPoly.IsUnit small → small ≠ 0 →
          2 * small.size ≤ residual.size + 1 → False by
      rcases Nat.le_total a.size b.size with hab_le | hba_le
      · exact hkey a ha_dvd_res hna ha_ne (by omega)
      · exact hkey b hb_dvd_res hnb hb_ne (by omega)
    intro small hsm_dvd hsm_nu hsm_ne hsm_size
    have hsm_size_pos : 0 < small.size := ZPoly.size_pos_of_ne_zero small hsm_ne
    have hsm_dvd_core : small ∣ core := ZPoly_dvd_trans hsm_dvd hres_dvd_core
    have hsm_size_ge_two : 2 ≤ small.size := by
      by_cases h : 2 ≤ small.size
      · exact h
      · exfalso
        have hsize : small.size = 1 := by omega
        exact hsm_nu
          (isUnit_of_dvd_primitive_size_one hcore_prim hsm_dvd_core hsize)
    -- Sign-normalize: pick a positive-leading divisor q of small (= small or
    -- scale (-1) small).
    obtain ⟨q, hq_dvd_small, hq_size_eq, hq_lc_pos, hq_natAbs⟩ :
        ∃ q : ZPoly,
          q ∣ small ∧ q.size = small.size ∧
          0 < DensePoly.leadingCoeff q ∧
          ∀ i, (q.coeff i).natAbs = (small.coeff i).natAbs := by
      by_cases hlc_pos : 0 < DensePoly.leadingCoeff small
      · refine ⟨small, ?_, rfl, hlc_pos, fun _ => rfl⟩
        exact ⟨1, (DensePoly.mul_one_right_poly (S := Int) small).symm⟩
      · have hlc_ne : DensePoly.leadingCoeff small ≠ 0 := by
          rw [DensePoly.leadingCoeff_eq_coeff_last small hsm_size_pos]
          exact DensePoly.coeff_last_ne_zero_of_pos_size small hsm_size_pos
        have hlc_neg : DensePoly.leadingCoeff small < 0 := by
          have h1 : ¬ 0 < DensePoly.leadingCoeff small := hlc_pos
          omega
        refine ⟨DensePoly.scale (-1 : Int) small,
                dvd_scale_neg_one small,
                size_scale_neg_one small,
                ?_,
                fun i => natAbs_coeff_scale_neg_one small i⟩
        have hsm_scale_size : 0 < (DensePoly.scale (-1 : Int) small).size := by
          rw [size_scale_neg_one]; exact hsm_size_pos
        rw [DensePoly.leadingCoeff_eq_coeff_last _ hsm_scale_size,
            size_scale_neg_one,
            DensePoly.coeff_scale _ _ _ (Int.mul_zero (-1 : Int)),
            ← DensePoly.leadingCoeff_eq_coeff_last small hsm_size_pos]
        omega
    have hq_size_pos : 0 < q.size := hq_size_eq ▸ hsm_size_pos
    have hq_ne_zero : q ≠ 0 := by
      intro hz; rw [hz] at hq_lc_pos
      rw [DensePoly.leadingCoeff_zero] at hq_lc_pos; omega
    have hq_dvd_res : q ∣ residual := ZPoly_dvd_trans hq_dvd_small hsm_dvd
    have hq_dvd_core : q ∣ core := ZPoly_dvd_trans hq_dvd_res hres_dvd_core
    have hq_bound : ∀ i, (q.coeff i).natAbs ≤ B := by
      intro i
      rw [hq_natAbs i]
      exact hbound small hsm_dvd_core i
    have hq_deg_eq : q.degree?.getD 0 = q.size - 1 := by
      unfold DensePoly.degree?
      simp [Nat.ne_of_gt hq_size_pos]
    have hq_deg_pos : 0 < q.degree?.getD 0 := by
      rw [hq_deg_eq, hq_size_eq]; omega
    have hq_deg_le : q.degree?.getD 0 ≤ target.degree?.getD 0 / 2 := by
      have htarget_size_pos : 0 < target.size :=
        ZPoly.size_pos_of_ne_zero target htarget_ne
      have htarget_deg : target.degree?.getD 0 = target.size - 1 := by
        unfold DensePoly.degree?
        simp [Nat.ne_of_gt htarget_size_pos]
      have hres_le_target : residual.size ≤ target.size :=
        ZPoly.size_le_of_dvd_nonzero hres_ne_zero htarget_ne hres_dvd_target
      rw [hq_deg_eq, hq_size_eq, htarget_deg]
      omega
    have hq_ne_one : q ≠ 1 := by
      intro h1
      have hdeg : q.degree?.getD 0 = 0 := by
        rw [h1]; change (DensePoly.C (1 : Int)).degree?.getD 0 = 0
        exact DensePoly.degree?_C_getD 1
      omega
    have hq_ne_neg_one : q ≠ DensePoly.C (-1 : Int) := by
      intro hneg
      have hdeg : q.degree?.getD 0 = 0 := by
        rw [hneg]; exact DensePoly.degree?_C_getD (-1)
      omega
    have hq_record : shouldRecordPolynomialFactor q = true := by
      unfold shouldRecordPolynomialFactor
      simp [hq_ne_zero, hq_ne_one, hq_ne_neg_one]
    have hq_mem : q ∈ candidates :=
      mem_trialDivisionCandidatesUpTo_of_bounded
        hq_deg_pos hq_deg_le hq_lc_pos hq_record hq_bound
    by_cases hq_emit : q ∈ factors.toList
    · -- emitted: q ∣ polyProduct factors, q ∣ residual ⇒ q*q ∣ target ∣ core
      have hq_dvd_prod : q ∣ Array.polyProduct factors :=
        dvd_polyProduct_toArray_of_mem factors.toList hq_emit
      have hprod : residual * Array.polyProduct factors = target :=
        trialDivisionPeelAux_product target candidates factors residual hsplit
      rcases hq_dvd_res with ⟨w, hres_eq⟩
      rcases hq_dvd_prod with ⟨k, hprod_eq⟩
      have hsquare_dvd_target : q * q ∣ target := by
        refine ⟨w * k, ?_⟩
        rw [← hprod, hres_eq, hprod_eq]
        calc (q * w) * (q * k)
            = q * (w * (q * k)) := by
                rw [DensePoly.mul_assoc_poly (S := Int)]
          _ = q * ((q * k) * w) := by
                rw [DensePoly.mul_comm_poly (S := Int) w (q * k)]
          _ = q * (q * (k * w)) := by
                rw [DensePoly.mul_assoc_poly (S := Int) q k w]
          _ = (q * q) * (k * w) := by
                rw [← DensePoly.mul_assoc_poly (S := Int)]
          _ = (q * q) * (w * k) := by
                rw [DensePoly.mul_comm_poly (S := Int) k w]
      have hsquare_dvd_core : q * q ∣ core :=
        ZPoly_dvd_trans hsquare_dvd_target htarget_dvd
      exact square_not_dvd_of_squareFreeRat hcore_ne hcore_sq
        hq_deg_pos hsquare_dvd_core
    · -- not emitted: no_missed_unemitted gives exactQuotient? residual q = none,
      -- but q ∣ residual (positive lc + degree) ⇒ some, contradiction
      have hno_q : exactQuotient? residual q = none :=
        trialDivisionPeelAux_no_missed_unemitted target candidates hcand_pos
          factors residual hsplit q hq_mem hq_emit
      rcases hq_dvd_res with ⟨w, hres_eq⟩
      have hwq : w * q = residual := by
        rw [hres_eq, DensePoly.mul_comm_poly (S := Int)]
      have hsome : exactQuotient? residual q = some w :=
        exactQuotient?_eq_some_of_pos_lc_pos_degree_mul_eq
          hq_lc_pos hq_deg_pos hwq
      rw [hno_q] at hsome
      nomatch hsome

/-- Degree-ordered prefix split of `trialDivisionCandidatesUpTo`.  Any
threshold `d_split` partitions the candidate list into a prefix
containing only candidates of degree `≤ d_split` and a suffix containing
only candidates of degree `> d_split`.  The prefix is exactly
`trialDivisionCandidatesUpTo B (min d_split maxDeg)` and the suffix is
the flat-map of the remaining `range'` range. -/
private theorem trialDivisionCandidatesUpTo_split_at_degree
    (B maxDeg d_split : Nat) :
    ∃ pre suf : List ZPoly,
      trialDivisionCandidatesUpTo B maxDeg = pre ++ suf ∧
      (∀ c ∈ pre, c.degree?.getD 0 ≤ d_split) ∧
      (∀ c ∈ suf, d_split < c.degree?.getD 0) := by
  by_cases hle : d_split ≤ maxDeg
  · refine ⟨(List.range d_split).flatMap
              (fun d => trialDivisionCandidatesOfDegree B (d + 1)),
            (List.range' d_split (maxDeg - d_split)).flatMap
              (fun d => trialDivisionCandidatesOfDegree B (d + 1)),
            ?_, ?_, ?_⟩
    · unfold trialDivisionCandidatesUpTo
      have heq : List.range maxDeg =
          List.range d_split ++ List.range' d_split (maxDeg - d_split) := by
        have h2 : List.range (d_split + (maxDeg - d_split)) =
            List.range d_split ++ List.range' d_split (maxDeg - d_split) := by
          rw [List.range_add, ← List.range'_eq_map_range]
        have h3 : List.range maxDeg = List.range (d_split + (maxDeg - d_split)) := by
          congr 1; omega
        rw [h3]; exact h2
      rw [heq, List.flatMap_append]
    · intro c hc
      rcases List.mem_flatMap.mp hc with ⟨d, hd_range, hd_in⟩
      rw [List.mem_range] at hd_range
      have ⟨hdeg, _, _⟩ := mem_trialDivisionCandidatesOfDegree hd_in
      omega
    · intro c hc
      rcases List.mem_flatMap.mp hc with ⟨d, hd_range, hd_in⟩
      rw [List.mem_range'_1] at hd_range
      have ⟨hdeg, _, _⟩ := mem_trialDivisionCandidatesOfDegree hd_in
      omega
  · refine ⟨trialDivisionCandidatesUpTo B maxDeg, [],
            (List.append_nil _).symm, ?_, ?_⟩
    · intro c hc
      unfold trialDivisionCandidatesUpTo at hc
      rcases List.mem_flatMap.mp hc with ⟨d, hd_range, hd_in⟩
      rw [List.mem_range] at hd_range
      have ⟨hdeg, _, _⟩ := mem_trialDivisionCandidatesOfDegree hd_in
      omega
    · intro c hc; simp at hc

/-- Each factor emitted by the candidate peel is irreducible when the
running target is a primitive, square-free divisor of the original core
with positive leading coefficient and the trial candidates exhaust every
bounded positive-leading positive-degree divisor.

Argument: a nontrivial decomposition `f_i = a * b` of an emitted factor
yields a strictly smaller-degree positive-leading divisor `q` of `f_i`
with bounded coefficients and degree at most `target.degree?.getD 0 / 2`.
Split the candidate list at `d_split := q.degree?.getD 0`: the prefix
contains every candidate of degree `≤ d_split` (including `q`); the
suffix contains every candidate of degree `> d_split` (including `f_i`).
By `trialDivisionPeelAux_split`, the peel decomposes accordingly. Since
`f_i ∈ peel.1` and the prefix peel only emits prefix candidates (all of
degree `≤ d_split < f_i.degree`), `f_i` belongs to the suffix-peel
factors; hence `f_i ∣ mid`, where `mid` is the running target after the
prefix peel.  Then `q ∣ f_i ∣ mid`, so the prefix peel does not miss
emitting `q` (`trialDivisionPeelAux_no_missed_unemitted` would otherwise
contradict `q ∣ mid`).  With both `q` and `f_i` emitted at distinct
candidate positions, `q * f_i ∣ polyProduct peel.1 ∣ target ∣ core`;
combined with `q ∣ f_i`, this gives `q * q ∣ core`, contradicting
`square_not_dvd_of_squareFreeRat`. -/
private theorem trialDivisionPeel_factor_irreducible
    {core target : ZPoly} {B : Nat}
    {factors : Array ZPoly} {residual : ZPoly} {factor : ZPoly}
    (hcore_ne : core ≠ 0)
    (hcore_prim : ZPoly.Primitive core)
    (hcore_sq : Hex.ZPoly.SquareFreeRat core)
    (htarget_dvd : target ∣ core)
    (htarget_pos : 0 < DensePoly.leadingCoeff target)
    (hbound : ∀ g, g ∣ core → ∀ i, (g.coeff i).natAbs ≤ B)
    (hsplit : trialDivisionPeelAux target
        (trialDivisionCandidatesUpTo B (target.degree?.getD 0 / 2)) =
          (factors, residual))
    (hmem : factor ∈ factors.toList) :
    ZPoly.Irreducible factor := by
  let candidates := trialDivisionCandidatesUpTo B (target.degree?.getD 0 / 2)
  change trialDivisionPeelAux target candidates = (factors, residual) at hsplit
  have htarget_ne : target ≠ 0 := by
    intro h; rw [h] at htarget_pos
    rw [DensePoly.leadingCoeff_zero] at htarget_pos; omega
  have hcand_pos_lc : ∀ c ∈ candidates, 0 < DensePoly.leadingCoeff c :=
    fun c hc => (mem_trialDivisionCandidatesUpTo hc).2.1
  have hcand_pos_deg : ∀ c ∈ candidates, 0 < c.degree?.getD 0 :=
    fun c hc => (mem_trialDivisionCandidatesUpTo hc).1
  have hcand_pos :
      ∀ c ∈ candidates,
        0 < c.degree?.getD 0 ∧ 0 < DensePoly.leadingCoeff c :=
    fun c hc => ⟨hcand_pos_deg c hc, hcand_pos_lc c hc⟩
  have hres_lc_pos : 0 < DensePoly.leadingCoeff residual :=
    trialDivisionPeelAux_residual_leadingCoeff_pos target candidates
      htarget_pos hcand_pos_lc factors residual hsplit
  have hres_ne_zero : residual ≠ 0 := by
    intro hzero; rw [hzero] at hres_lc_pos
    rw [DensePoly.leadingCoeff_zero] at hres_lc_pos; omega
  have hprod : residual * Array.polyProduct factors = target :=
    trialDivisionPeelAux_product target candidates factors residual hsplit
  have hfactor_mem_cand : factor ∈ candidates :=
    trialDivisionPeelAux_factor_mem target candidates factors residual hsplit
      factor hmem
  have hfactor_dvd_target : factor ∣ target :=
    trialDivisionPeelAux_factor_dvd_target target candidates factors residual
      hsplit factor hmem
  have hfactor_dvd_core : factor ∣ core :=
    ZPoly_dvd_trans hfactor_dvd_target htarget_dvd
  have hfactor_pos_deg : 0 < factor.degree?.getD 0 := hcand_pos_deg factor hfactor_mem_cand
  have hfactor_pos_lc : 0 < DensePoly.leadingCoeff factor := hcand_pos_lc factor hfactor_mem_cand
  have hfactor_ne_zero : factor ≠ 0 := by
    intro h; rw [h] at hfactor_pos_lc
    rw [DensePoly.leadingCoeff_zero] at hfactor_pos_lc; omega
  have hfactor_size_pos : 0 < factor.size :=
    ZPoly.size_pos_of_ne_zero factor hfactor_ne_zero
  have hfactor_size_eq : factor.size = factor.degree?.getD 0 + 1 := by
    unfold DensePoly.degree?
    simp [Nat.ne_of_gt hfactor_size_pos]
    omega
  -- Build the Irreducible instance for factor
  refine { not_zero := hfactor_ne_zero, not_unit := ?_, no_factors := ?_ }
  · intro hunit
    rcases hunit with h1 | hneg1
    · have : factor.degree?.getD 0 = 0 := by
        rw [h1]; change (DensePoly.C (1 : Int)).degree?.getD 0 = 0
        exact DensePoly.degree?_C_getD 1
      omega
    · have : factor.degree?.getD 0 = 0 := by
        rw [hneg1]; exact DensePoly.degree?_C_getD (-1)
      omega
  · intro a b hab
    by_cases hua : ZPoly.IsUnit a
    · exact Or.inl hua
    by_cases hub : ZPoly.IsUnit b
    · exact Or.inr hub
    exfalso
    have hna : ¬ ZPoly.IsUnit a := hua
    have hnb : ¬ ZPoly.IsUnit b := hub
    have ha_ne : a ≠ 0 := by
      intro hz; apply hfactor_ne_zero
      rw [hab, hz, DensePoly.zero_mul]
    have hb_ne : b ≠ 0 := by
      intro hz; apply hfactor_ne_zero
      rw [hab, hz, DensePoly.mul_comm_poly (S := Int), DensePoly.zero_mul]
    have ha_dvd_factor : a ∣ factor := ⟨b, hab⟩
    have hb_dvd_factor : b ∣ factor :=
      ⟨a, hab.trans (DensePoly.mul_comm_poly (S := Int) a b)⟩
    have ha_dvd_core : a ∣ core := ZPoly_dvd_trans ha_dvd_factor hfactor_dvd_core
    have hb_dvd_core : b ∣ core := ZPoly_dvd_trans hb_dvd_factor hfactor_dvd_core
    have ha_size_pos : 0 < a.size := ZPoly.size_pos_of_ne_zero a ha_ne
    have hb_size_pos : 0 < b.size := ZPoly.size_pos_of_ne_zero b hb_ne
    have ha_size_ge_two : 2 ≤ a.size := by
      by_cases h : 2 ≤ a.size
      · exact h
      · exfalso
        have hsize : a.size = 1 := by omega
        exact hna (isUnit_of_dvd_primitive_size_one hcore_prim ha_dvd_core hsize)
    have hb_size_ge_two : 2 ≤ b.size := by
      by_cases h : 2 ≤ b.size
      · exact h
      · exfalso
        have hsize : b.size = 1 := by omega
        exact hnb (isUnit_of_dvd_primitive_size_one hcore_prim hb_dvd_core hsize)
    have hab_size : (a * b).size = a.size + b.size - 1 :=
      ZPoly.mul_size_eq_top_succ_of_nonzero a b ha_size_pos hb_size_pos
    rw [← hab] at hab_size
    -- Pick small ∈ {a, b} with 2 * small.size ≤ factor.size + 1
    suffices hkey :
        ∀ small : ZPoly,
          small ∣ factor → ¬ ZPoly.IsUnit small → small ≠ 0 →
          2 * small.size ≤ factor.size + 1 → False by
      rcases Nat.le_total a.size b.size with hab_le | hba_le
      · exact hkey a ha_dvd_factor hna ha_ne (by omega)
      · exact hkey b hb_dvd_factor hnb hb_ne (by omega)
    intro small hsm_dvd hsm_nu hsm_ne hsm_size
    have hsm_size_pos : 0 < small.size := ZPoly.size_pos_of_ne_zero small hsm_ne
    have hsm_dvd_core : small ∣ core := ZPoly_dvd_trans hsm_dvd hfactor_dvd_core
    have hsm_dvd_target : small ∣ target := ZPoly_dvd_trans hsm_dvd hfactor_dvd_target
    have hsm_size_ge_two : 2 ≤ small.size := by
      by_cases h : 2 ≤ small.size
      · exact h
      · exfalso
        have hsize : small.size = 1 := by omega
        exact hsm_nu
          (isUnit_of_dvd_primitive_size_one hcore_prim hsm_dvd_core hsize)
    obtain ⟨q, hq_dvd_small, hq_size_eq, hq_lc_pos, hq_natAbs⟩ :
        ∃ q : ZPoly,
          q ∣ small ∧ q.size = small.size ∧
          0 < DensePoly.leadingCoeff q ∧
          ∀ i, (q.coeff i).natAbs = (small.coeff i).natAbs := by
      by_cases hlc_pos : 0 < DensePoly.leadingCoeff small
      · refine ⟨small, ?_, rfl, hlc_pos, fun _ => rfl⟩
        exact ⟨1, (DensePoly.mul_one_right_poly (S := Int) small).symm⟩
      · have hlc_ne : DensePoly.leadingCoeff small ≠ 0 := by
          rw [DensePoly.leadingCoeff_eq_coeff_last small hsm_size_pos]
          exact DensePoly.coeff_last_ne_zero_of_pos_size small hsm_size_pos
        have hlc_neg : DensePoly.leadingCoeff small < 0 := by
          have h1 : ¬ 0 < DensePoly.leadingCoeff small := hlc_pos
          omega
        refine ⟨DensePoly.scale (-1 : Int) small,
                dvd_scale_neg_one small,
                size_scale_neg_one small,
                ?_,
                fun i => natAbs_coeff_scale_neg_one small i⟩
        have hsm_scale_size : 0 < (DensePoly.scale (-1 : Int) small).size := by
          rw [size_scale_neg_one]; exact hsm_size_pos
        rw [DensePoly.leadingCoeff_eq_coeff_last _ hsm_scale_size,
            size_scale_neg_one,
            DensePoly.coeff_scale _ _ _ (Int.mul_zero (-1 : Int)),
            ← DensePoly.leadingCoeff_eq_coeff_last small hsm_size_pos]
        omega
    have hq_size_pos : 0 < q.size := hq_size_eq ▸ hsm_size_pos
    have hq_ne_zero : q ≠ 0 := by
      intro hz; rw [hz] at hq_lc_pos
      rw [DensePoly.leadingCoeff_zero] at hq_lc_pos; omega
    have hq_dvd_factor : q ∣ factor := ZPoly_dvd_trans hq_dvd_small hsm_dvd
    have hq_dvd_target : q ∣ target := ZPoly_dvd_trans hq_dvd_factor hfactor_dvd_target
    have hq_dvd_core : q ∣ core := ZPoly_dvd_trans hq_dvd_target htarget_dvd
    have hq_bound : ∀ i, (q.coeff i).natAbs ≤ B := by
      intro i; rw [hq_natAbs i]; exact hbound small hsm_dvd_core i
    have hq_deg_eq : q.degree?.getD 0 = q.size - 1 := by
      unfold DensePoly.degree?
      simp [Nat.ne_of_gt hq_size_pos]
    have hq_deg_pos : 0 < q.degree?.getD 0 := by
      rw [hq_deg_eq, hq_size_eq]; omega
    -- degree(q) < degree(factor) since 2 * q.size ≤ factor.size + 1 and q.size ≥ 2
    have hq_deg_lt_factor : q.degree?.getD 0 < factor.degree?.getD 0 := by
      rw [hq_deg_eq, hq_size_eq]
      have hfactor_eq : factor.degree?.getD 0 + 1 = factor.size := hfactor_size_eq.symm
      omega
    have hq_deg_le : q.degree?.getD 0 ≤ target.degree?.getD 0 / 2 := by
      have htarget_size_pos : 0 < target.size :=
        ZPoly.size_pos_of_ne_zero target htarget_ne
      have htarget_deg : target.degree?.getD 0 = target.size - 1 := by
        unfold DensePoly.degree?
        simp [Nat.ne_of_gt htarget_size_pos]
      have hfactor_le_target : factor.size ≤ target.size :=
        ZPoly.size_le_of_dvd_nonzero hfactor_ne_zero htarget_ne hfactor_dvd_target
      rw [hq_deg_eq, hq_size_eq, htarget_deg]
      omega
    have hq_ne_one : q ≠ 1 := by
      intro h1
      have : q.degree?.getD 0 = 0 := by
        rw [h1]; change (DensePoly.C (1 : Int)).degree?.getD 0 = 0
        exact DensePoly.degree?_C_getD 1
      omega
    have hq_ne_neg_one : q ≠ DensePoly.C (-1 : Int) := by
      intro hneg
      have : q.degree?.getD 0 = 0 := by
        rw [hneg]; exact DensePoly.degree?_C_getD (-1)
      omega
    have hq_record : shouldRecordPolynomialFactor q = true := by
      unfold shouldRecordPolynomialFactor
      simp [hq_ne_zero, hq_ne_one, hq_ne_neg_one]
    have hq_mem : q ∈ candidates :=
      mem_trialDivisionCandidatesUpTo_of_bounded
        hq_deg_pos hq_deg_le hq_lc_pos hq_record hq_bound
    -- Split candidates at d_split := q.degree?.getD 0
    obtain ⟨pre, suf, hcand_split, hpre_deg, hsuf_deg⟩ :=
      trialDivisionCandidatesUpTo_split_at_degree B
        (target.degree?.getD 0 / 2) (q.degree?.getD 0)
    -- Apply peel split lemma
    cases hpre : trialDivisionPeelAux target pre with
    | mk preFactors mid =>
        have hpeel_full :
            trialDivisionPeelAux target candidates =
              (preFactors ++ (trialDivisionPeelAux mid suf).1,
               (trialDivisionPeelAux mid suf).2) := by
          rw [show candidates = pre ++ suf from hcand_split]
          exact trialDivisionPeelAux_split target pre suf preFactors mid hpre
        rw [hpeel_full] at hsplit
        cases hsuf_peel : trialDivisionPeelAux mid suf with
        | mk sufFactors finalRes =>
            rw [hsuf_peel] at hsplit
            obtain ⟨hfact_eq, hres_eq⟩ := Prod.mk.inj hsplit
            -- peel.1 = preFactors ++ sufFactors
            -- f_i ∈ peel.1.toList → f_i ∈ preFactors.toList ∨ f_i ∈ sufFactors.toList
            have hmem' : factor ∈ (preFactors ++ sufFactors).toList := by
              rw [hfact_eq]; exact hmem
            rw [Array.toList_append, List.mem_append] at hmem'
            -- f_i ∉ preFactors: degree(f_i) > d_split but pre has degree ≤ d_split
            have hfactor_not_in_pre : factor ∉ preFactors.toList := by
              intro hmem_pre
              have hpre_cand :
                  factor ∈ pre :=
                trialDivisionPeelAux_factor_mem target pre preFactors mid hpre
                  factor hmem_pre
              have := hpre_deg factor hpre_cand
              omega
            have hfactor_in_suf : factor ∈ sufFactors.toList := by
              rcases hmem' with hpre_mem | hsuf_mem
              · exact absurd hpre_mem hfactor_not_in_pre
              · exact hsuf_mem
            -- Now f_i ∣ polyProduct sufFactors → f_i ∣ mid
            have hfactor_dvd_prod_suf : factor ∣ Array.polyProduct sufFactors :=
              dvd_polyProduct_toArray_of_mem sufFactors.toList hfactor_in_suf
            have hsuf_prod : finalRes * Array.polyProduct sufFactors = mid :=
              trialDivisionPeelAux_product mid suf sufFactors finalRes hsuf_peel
            have hfactor_dvd_mid : factor ∣ mid := by
              rcases hfactor_dvd_prod_suf with ⟨k, hk⟩
              refine ⟨finalRes * k, ?_⟩
              rw [← hsuf_prod, hk, ← DensePoly.mul_assoc_poly (S := Int),
                DensePoly.mul_comm_poly (S := Int) finalRes factor,
                DensePoly.mul_assoc_poly (S := Int)]
            have hq_dvd_mid : q ∣ mid := ZPoly_dvd_trans hq_dvd_factor hfactor_dvd_mid
            -- q ∈ pre (degree q = d_split, pre has degree ≤ d_split — but pre may exclude q
            -- since List.append may split at any boundary; however, the construction
            -- via _split_at_degree puts q in pre since q.degree = d_split.)
            have hq_in_pre : q ∈ pre := by
              -- q ∈ candidates = pre ++ suf. q.degree = d_split.
              -- Suf has degree > d_split. So q ∉ suf. Hence q ∈ pre.
              have hq_in_split : q ∈ pre ++ suf := by
                rw [← hcand_split]; exact hq_mem
              rcases List.mem_append.mp hq_in_split with h | h
              · exact h
              · have := hsuf_deg q h; omega
            -- q ∈ pre. Apply no_missed_unemitted on the pre-peel: q is not emitted
            -- only if q ∤ mid. But q ∣ mid. So q IS emitted.
            have hpre_cand_pos :
                ∀ c ∈ pre, 0 < c.degree?.getD 0 ∧ 0 < DensePoly.leadingCoeff c := by
              intro c hc
              have hc_cand : c ∈ candidates := by
                show c ∈ trialDivisionCandidatesUpTo B (target.degree?.getD 0 / 2)
                rw [hcand_split]; exact List.mem_append.mpr (Or.inl hc)
              exact hcand_pos c hc_cand
            have hq_in_preFactors : q ∈ preFactors.toList := by
              by_cases hq_emit : q ∈ preFactors.toList
              · exact hq_emit
              · exfalso
                have hno_q : exactQuotient? mid q = none :=
                  trialDivisionPeelAux_no_missed_unemitted target pre hpre_cand_pos
                    preFactors mid hpre q hq_in_pre hq_emit
                rcases hq_dvd_mid with ⟨w, hmid_eq⟩
                have hwq : w * q = mid := by
                  rw [hmid_eq, DensePoly.mul_comm_poly (S := Int)]
                have hsome : exactQuotient? mid q = some w :=
                  exactQuotient?_eq_some_of_pos_lc_pos_degree_mul_eq
                    hq_lc_pos hq_deg_pos hwq
                rw [hno_q] at hsome
                nomatch hsome
            -- Both q ∈ preFactors and factor ∈ sufFactors. q * factor ∣ polyProduct peel.1.
            have hq_dvd_prod_pre : q ∣ Array.polyProduct preFactors :=
              dvd_polyProduct_toArray_of_mem preFactors.toList hq_in_preFactors
            -- Combining: q * factor ∣ polyProduct preFactors * polyProduct sufFactors
            rcases hq_dvd_prod_pre with ⟨kq, hq_prod_eq⟩
            rcases hfactor_dvd_prod_suf with ⟨kf, hf_prod_eq⟩
            have hsquare_target_chain : q * factor ∣ target := by
              refine ⟨finalRes * (kq * kf), ?_⟩
              have hpeel_prod_eq :
                  Array.polyProduct (preFactors ++ sufFactors) =
                    Array.polyProduct preFactors * Array.polyProduct sufFactors :=
                ZPoly.polyProduct_append preFactors sufFactors
              have hprod' : residual * Array.polyProduct factors = target := hprod
              rw [← hfact_eq, hpeel_prod_eq, hq_prod_eq, hf_prod_eq,
                  ← hres_eq] at hprod'
              rw [← hprod']
              calc finalRes * ((q * kq) * (factor * kf))
                  = finalRes * (q * (kq * (factor * kf))) := by
                      rw [DensePoly.mul_assoc_poly (S := Int) q kq (factor * kf)]
                _ = finalRes * (q * ((factor * kf) * kq)) := by
                      rw [DensePoly.mul_comm_poly (S := Int) kq (factor * kf)]
                _ = finalRes * (q * (factor * (kf * kq))) := by
                      rw [DensePoly.mul_assoc_poly (S := Int) factor kf kq]
                _ = finalRes * (q * (factor * (kq * kf))) := by
                      rw [DensePoly.mul_comm_poly (S := Int) kf kq]
                _ = finalRes * ((q * factor) * (kq * kf)) := by
                      rw [← DensePoly.mul_assoc_poly (S := Int) q factor (kq * kf)]
                _ = (finalRes * (q * factor)) * (kq * kf) := by
                      rw [← DensePoly.mul_assoc_poly (S := Int)]
                _ = ((q * factor) * finalRes) * (kq * kf) := by
                      rw [DensePoly.mul_comm_poly (S := Int) finalRes (q * factor)]
                _ = (q * factor) * (finalRes * (kq * kf)) := by
                      rw [DensePoly.mul_assoc_poly (S := Int)]
            have hsquare_dvd_core : q * factor ∣ core :=
              ZPoly_dvd_trans hsquare_target_chain htarget_dvd
            -- q ∣ factor → q * q ∣ q * factor
            rcases hq_dvd_factor with ⟨wf, hwf⟩
            have hqq_dvd_qfactor : q * q ∣ q * factor := by
              refine ⟨wf, ?_⟩
              rw [hwf, DensePoly.mul_assoc_poly (S := Int)]
            have hqq_dvd_core : q * q ∣ core :=
              ZPoly_dvd_trans hqq_dvd_qfactor hsquare_dvd_core
            exact square_not_dvd_of_squareFreeRat hcore_ne hcore_sq
              hq_deg_pos hqq_dvd_core

/-- For `ε ∈ {1, -1}`, `p` divides its `ε`-scaling.  The identity scaling is
trivial; the sign flip composes `dvd_scale_neg_one` with the involution
`scale_neg_one_neg_one`. -/
private theorem dvd_scale_unit (p : ZPoly) {ε : Int} (hε : ε = 1 ∨ ε = -1) :
    p ∣ DensePoly.scale ε p := by
  rcases hε with rfl | rfl
  · rw [← ZPoly.C_mul_eq_scale (1 : Int) p]
    exact ⟨DensePoly.C 1, DensePoly.mul_comm_poly (S := Int) (DensePoly.C 1) p⟩
  · have h := dvd_scale_neg_one (DensePoly.scale (-1 : Int) p)
    rwa [scale_neg_one_neg_one p] at h

/-- The normalized square-free core divides the original polynomial.

Chains `squareFreeCore ∣ squareFreeCore * repeatedPart` through the signed
reassembly `scale ε (squareFreeCore * repeatedPart) = primitivePart core` (the
`X`-free core is primitive, so its primitive part is itself), then
`core ∣ primitivePart f` (the `X`-power extraction product) and
`primitivePart f ∣ f` (`content_mul_primitivePart`).  Lifts a coefficient bound
on divisors of `f` to a bound on divisors of the square-free core. -/
theorem squareFreeCore_dvd_self (f : ZPoly) (hf : f ≠ 0) :
    (normalizeForFactor f).squareFreeCore ∣ f := by
  have hc_prim :
      ZPoly.Primitive (ZPoly.extractXPower (ZPoly.primitivePart f)).core :=
    extractXPower_core_primitive_of_ne_zero f hf
  have hc_ne : (ZPoly.extractXPower (ZPoly.primitivePart f)).core ≠ 0 :=
    ZPoly.ne_zero_of_primitive _ hc_prim
  -- squareFreeCore ∣ (extractXPower (primitivePart f)).core.
  have hsfc_dvd_c :
      (normalizeForFactor f).squareFreeCore ∣
        (ZPoly.extractXPower (ZPoly.primitivePart f)).core := by
    obtain ⟨ε, hε, hscale⟩ :=
      ZPoly.primitiveSquareFreeDecomposition_reassembly_signed
        (ZPoly.extractXPower (ZPoly.primitivePart f)).core hc_ne
    rw [ZPoly.primitivePart_eq_self_of_primitive _ hc_prim] at hscale
    have hprod_dvd_scale :=
      dvd_scale_unit
        ((ZPoly.primitiveSquareFreeDecomposition
            (ZPoly.extractXPower (ZPoly.primitivePart f)).core).squareFreeCore *
          (ZPoly.primitiveSquareFreeDecomposition
            (ZPoly.extractXPower (ZPoly.primitivePart f)).core).repeatedPart) hε
    rw [hscale] at hprod_dvd_scale
    have hsfc_dvd_prod :
        (ZPoly.primitiveSquareFreeDecomposition
            (ZPoly.extractXPower (ZPoly.primitivePart f)).core).squareFreeCore ∣
          ((ZPoly.primitiveSquareFreeDecomposition
              (ZPoly.extractXPower (ZPoly.primitivePart f)).core).squareFreeCore *
            (ZPoly.primitiveSquareFreeDecomposition
              (ZPoly.extractXPower (ZPoly.primitivePart f)).core).repeatedPart) :=
      ⟨_, rfl⟩
    have hchain := ZPoly_dvd_trans hsfc_dvd_prod hprod_dvd_scale
    simpa [normalizeForFactor] using hchain
  -- core ∣ primitivePart f.
  have hc_dvd_pf :
      (ZPoly.extractXPower (ZPoly.primitivePart f)).core ∣ ZPoly.primitivePart f := by
    have hprod :
        Array.polyProduct
            (xPowerFactorArray (ZPoly.extractXPower (ZPoly.primitivePart f)).power ++
              #[(ZPoly.extractXPower (ZPoly.primitivePart f)).core]) =
          ZPoly.primitivePart f :=
      extractXPower_product (ZPoly.primitivePart f)
    rw [ZPoly.polyProduct_append, ZPoly.polyProduct_singleton] at hprod
    exact ⟨Array.polyProduct
        (xPowerFactorArray (ZPoly.extractXPower (ZPoly.primitivePart f)).power),
      hprod.symm.trans (DensePoly.mul_comm_poly (S := Int) _ _)⟩
  -- primitivePart f ∣ f.
  have hpf_dvd_f : ZPoly.primitivePart f ∣ f := by
    refine ⟨DensePoly.C (ZPoly.content f), ?_⟩
    rw [DensePoly.mul_comm_poly (S := Int), ZPoly.C_mul_eq_scale]
    exact (ZPoly.content_mul_primitivePart f).symm
  exact ZPoly_dvd_trans hsfc_dvd_c (ZPoly_dvd_trans hc_dvd_pf hpf_dvd_f)

/-- Every factor emitted by the standalone integer trial-division core has
positive degree, when `core` is primitive with positive leading coefficient.

The three factor families are handled separately: integer-root split factors
are `linearFactorForRoot` images (degree one); peeled candidates carry the
positive-degree invariant of `trialDivisionCandidatesUpTo`; and the final
residual, when retained, cannot be a constant, because a size-one divisor of a
primitive core is a unit, which a `≠ 1` residual with positive leading
coefficient is not. -/
theorem exhaustiveIntegerTrialCoreFactorsWithBound_degree_pos
    (core : ZPoly) (B : Nat)
    (hcore_prim : ZPoly.Primitive core)
    (hcore_pos : 0 < DensePoly.leadingCoeff core) :
    ∀ factor ∈ (exhaustiveIntegerTrialCoreFactorsWithBound core B).toList,
      0 < factor.degree?.getD 0 := by
  intro factor hmem
  let roots := integerRootCandidates core
  let split := splitIntegerRootFactorsAux core roots roots.length
  let candidates := trialDivisionCandidatesUpTo B (split.2.degree?.getD 0 / 2)
  let peel := trialDivisionPeelAux split.2 candidates
  have hcore_ne : core ≠ 0 := by
    intro hz; rw [hz] at hcore_pos
    rw [DensePoly.leadingCoeff_zero] at hcore_pos; omega
  have hsplit_prod : split.2 * Array.polyProduct split.1 = core :=
    splitIntegerRootFactorsAux_product core roots roots.length split.1 split.2 rfl
  have hsplit2_dvd_core : split.2 ∣ core :=
    ⟨Array.polyProduct split.1, hsplit_prod.symm⟩
  have hsplit_lc_pos :
      0 < DensePoly.leadingCoeff (Array.polyProduct split.1) :=
    splitIntegerRootFactorsAux_polyProduct_leadingCoeff_pos core roots
      roots.length split.1 split.2 rfl
  have hsplit1_ne : Array.polyProduct split.1 ≠ 0 := by
    intro hz; rw [hz] at hsplit_lc_pos
    rw [DensePoly.leadingCoeff_zero] at hsplit_lc_pos; omega
  have hsplit2_ne : split.2 ≠ 0 := by
    intro hz; apply hcore_ne
    rw [← hsplit_prod, hz]; exact DensePoly.zero_mul _
  have hsplit2_pos : 0 < DensePoly.leadingCoeff split.2 := by
    have hlc :
        DensePoly.leadingCoeff core =
          DensePoly.leadingCoeff split.2 *
            DensePoly.leadingCoeff (Array.polyProduct split.1) := by
      rw [← hsplit_prod]
      exact ZPoly.leadingCoeff_mul_of_nonzero split.2 (Array.polyProduct split.1)
        hsplit2_ne hsplit1_ne
    by_cases hp : 0 < DensePoly.leadingCoeff split.2
    · exact hp
    · exfalso
      have hle : DensePoly.leadingCoeff split.2 ≤ 0 := by omega
      have hnn : 0 ≤ DensePoly.leadingCoeff (Array.polyProduct split.1) :=
        Int.le_of_lt hsplit_lc_pos
      have hna : 0 ≤ -DensePoly.leadingCoeff split.2 := by omega
      have hprod_neg :
          0 ≤ -DensePoly.leadingCoeff split.2 *
            DensePoly.leadingCoeff (Array.polyProduct split.1) :=
        Int.mul_nonneg hna hnn
      have hneg_eq :
          -DensePoly.leadingCoeff split.2 *
              DensePoly.leadingCoeff (Array.polyProduct split.1) =
            -(DensePoly.leadingCoeff split.2 *
                DensePoly.leadingCoeff (Array.polyProduct split.1)) :=
        Int.neg_mul _ _
      rw [hneg_eq, ← hlc] at hprod_neg
      omega
  -- Positive degree for the integer-root split factors.
  have hsplit_deg : ∀ b ∈ split.1.toList, 0 < b.degree?.getD 0 := by
    intro b hb
    obtain ⟨rs, _hsub, hshape⟩ :=
      splitIntegerRootFactorsAux_factors_form
        (target := core) (roots := roots) (fuel := roots.length)
        (factors := split.1) (residual := split.2) rfl
    rw [hshape] at hb
    obtain ⟨r, _hr, hb_eq⟩ := List.mem_map.mp hb
    rw [← hb_eq]
    exact linearFactorForRoot_degree_pos r
  -- Positive degree for the peeled candidates.
  have hpeel_deg : ∀ b ∈ peel.1.toList, 0 < b.degree?.getD 0 := by
    intro b hb
    have hb_cand : b ∈ candidates :=
      trialDivisionPeelAux_factor_mem split.2 candidates peel.1 peel.2 rfl b hb
    exact (mem_trialDivisionCandidatesUpTo hb_cand).1
  have hpeel_res_pos : 0 < DensePoly.leadingCoeff peel.2 :=
    trialDivisionPeelAux_residual_leadingCoeff_pos split.2 candidates
      hsplit2_pos (fun c hc => (mem_trialDivisionCandidatesUpTo hc).2.1)
      peel.1 peel.2 rfl
  change factor ∈
      (if peel.2 = 1 then split.1 ++ peel.1
        else (split.1 ++ peel.1).push peel.2).toList at hmem
  by_cases hres_one : peel.2 = 1
  · rw [if_pos hres_one, Array.toList_append, List.mem_append] at hmem
    rcases hmem with h1 | h2
    · exact hsplit_deg factor h1
    · exact hpeel_deg factor h2
  · rw [if_neg hres_one, Array.toList_push, Array.toList_append] at hmem
    rcases List.mem_append.mp hmem with hpref | hres
    · rcases List.mem_append.mp hpref with h1 | h2
      · exact hsplit_deg factor h1
      · exact hpeel_deg factor h2
    · have hfac_eq : factor = peel.2 := List.mem_singleton.mp hres
      rw [hfac_eq]
      have hres_ne : peel.2 ≠ 0 := by
        intro hz; rw [hz] at hpeel_res_pos
        rw [DensePoly.leadingCoeff_zero] at hpeel_res_pos; omega
      have hres_size_pos : 0 < peel.2.size :=
        ZPoly.size_pos_of_ne_zero peel.2 hres_ne
      have hres_dvd_split2 : peel.2 ∣ split.2 :=
        trialDivisionPeelAux_residual_dvd_target split.2 candidates peel.1 peel.2 rfl
      have hres_dvd_core : peel.2 ∣ core :=
        ZPoly_dvd_trans hres_dvd_split2 hsplit2_dvd_core
      have hsize_ge_two : 2 ≤ peel.2.size := by
        by_cases h : 2 ≤ peel.2.size
        · exact h
        · exfalso
          have hsize1 : peel.2.size = 1 := by omega
          rcases isUnit_of_dvd_primitive_size_one hcore_prim hres_dvd_core hsize1
            with h1 | hneg1
          · exact hres_one h1
          · rw [hneg1] at hpeel_res_pos
            simp at hpeel_res_pos
      have hdeg_eq : peel.2.degree?.getD 0 = peel.2.size - 1 := by
        unfold DensePoly.degree?
        simp [Nat.ne_of_gt hres_size_pos]
      omega

end Hex
