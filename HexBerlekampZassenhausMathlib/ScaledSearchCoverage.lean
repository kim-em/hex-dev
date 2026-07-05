/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexBerlekampZassenhaus
public import HexBerlekampMathlib.Basic
public import HexBerlekampZassenhausMathlib.UFDPartition
public import HexHenselMathlib.Correctness
public import HexPolyZMathlib.Basic
public import HexPolyZMathlib.Mignotte
public import Mathlib.RingTheory.Coprime.Lemmas
public import Mathlib.RingTheory.Polynomial.UniqueFactorization
public import Mathlib.RingTheory.PrincipalIdealDomain

public import HexBerlekampZassenhausMathlib.PrimitivityDegreeCover
import all HexBerlekampZassenhausMathlib.PublicSurface
import all HexBerlekampZassenhausMathlib.ModPFactor
import all HexBerlekampZassenhausMathlib.LiftedFactor
import all HexBerlekampZassenhausMathlib.M1Recovery
import all HexBerlekampZassenhausMathlib.RecombinationSplit
import all HexBerlekampZassenhausMathlib.RecombinationCandidate
import all HexBerlekampZassenhausMathlib.HenselFactorProps
import all HexBerlekampZassenhausMathlib.SubsetCoprimality
import all HexBerlekampZassenhausMathlib.ForwardHenselTransport
import all HexBerlekampZassenhausMathlib.RecombinationMonic
import all HexBerlekampZassenhausMathlib.PrimitivityDegreeCover

public section
set_option backward.proofsInPublic true
set_option backward.privateInPublic true

/-!
This module collects the scaled-tier search coverage and `RecoveredScaledSearch`.
-/

namespace HexBerlekampZassenhausMathlib

noncomputable section

open Polynomial

namespace liftedTrueSupports

/-- Every true support is nonempty at a sufficiently precise primitive core
lift. -/
theorem nonempty_of_partition
    {core : Hex.ZPoly} {d : Hex.LiftData}
    (hpartition : LiftedFactorSubsetPartition core d Finset.univ core)
    (hcore_ne : core ≠ 0)
    (hcore_primitive : Hex.ZPoly.Primitive core)
    (hcore_lc_pos : 0 < Hex.DensePoly.leadingCoeff core)
    (hprecision : 2 * Hex.ZPoly.defaultFactorCoeffBound core < d.p ^ d.k) :
    ∀ S ∈ liftedTrueSupports core d, S.Nonempty := by
  intro U hU
  rcases hU with ⟨f, S, hirr, hdvd, hrep, rfl⟩
  by_contra hnot
  rw [Set.not_nonempty_iff_eq_empty] at hnot
  have hS_empty : S = ∅ := by
    apply Finset.ext
    intro i
    have hiff := Set.ext_iff.mp hnot i
    simpa using hiff
  subst hS_empty
  exact not_represents_empty_of_irreducible_dvd_core_of_primitive_pos_lc_core
    hcore_ne hcore_primitive hcore_lc_pos hprecision hdvd hpartition hdvd hirr hrep

/-- The lifted true-support family is in bijection with the normalized
irreducible factors of `core`: its cardinality equals
`(normalizedFactors (toPolynomial core)).card`.

The forward map sends each support to the normalized irreducible polynomial it
represents. Existence of a representing subset for every irreducible divisor
comes from the partition's `HenselSubsetCorrespondenceRest` base
(`exists_subset`); injectivity comes from `unique_up_to_associated`; squarefree
`target = core` makes `normalizedFactors` `Nodup`, so its `toFinset.card`
equals its `card`. -/
theorem ncard_eq_normalizedFactors_card
    {core : Hex.ZPoly} {d : Hex.LiftData}
    (hpartition : LiftedFactorSubsetPartition core d Finset.univ core)
    (hcore_ne : core ≠ 0) :
    (liftedTrueSupports core d).ncard =
      (UniqueFactorizationMonoid.normalizedFactors
        (HexPolyZMathlib.toPolynomial core)).card := by
  classical
  set X := HexPolyZMathlib.toPolynomial core with hX
  have hX_ne : X ≠ 0 := by
    rw [hX]
    intro h
    exact hcore_ne (HexPolyZMathlib.equiv.injective (by simpa using h))
  -- The forward map: a support's representing normalized irreducible factor.
  set φ : Set (LiftedFactorIndex d) → Polynomial ℤ :=
    fun U => normalize (HexPolyZMathlib.toPolynomial
      (liftedRecoveryCandidate core d (Set.toFinite U).toFinset)) with hφdef
  -- Evaluate `φ` on a coerced representing subset.
  have hφ : ∀ {f : Hex.ZPoly} {S : LiftedFactorSubset d},
      Irreducible (HexPolyZMathlib.toPolynomial f) → f ∣ core →
      RepresentsIntegerFactorAtLift core d f S →
      φ (↑S : Set (LiftedFactorIndex d)) =
        normalize (HexPolyZMathlib.toPolynomial f) := by
    intro f S hirr hdvd hrep
    have htf : (Set.toFinite (↑S : Set (LiftedFactorIndex d))).toFinset = S := by
      apply Finset.coe_injective
      rw [Set.Finite.coe_toFinset]
    have hrec : liftedRecoveryCandidate core d S = f :=
      hpartition.liftedRecoveryCandidate_eq hirr hdvd (Finset.subset_univ S) hrep
    simp only [hφdef]
    rw [htf, hrec]
  -- The forward map is a bijection onto the normalized irreducible factors.
  have hbij : Set.BijOn φ (liftedTrueSupports core d)
      (↑((UniqueFactorizationMonoid.normalizedFactors X).toFinset) :
        Set (Polynomial ℤ)) := by
    refine ⟨?_, ?_, ?_⟩
    · -- maps to: each support represents a normalized irreducible factor of `X`.
      intro U hU
      rcases hU with ⟨f, S, hirr, hdvd, hrep, rfl⟩
      rw [hφ hirr hdvd hrep]
      obtain ⟨q, hq_mem, hq_assoc⟩ :=
        UniqueFactorizationMonoid.exists_mem_normalizedFactors_of_dvd hX_ne hirr
          (by rw [hX]; exact HexPolyMathlib.toPolynomial_dvd hdvd)
      have hnorm_q : normalize q = q :=
        UniqueFactorizationMonoid.normalize_normalized_factor q hq_mem
      have heq : normalize (HexPolyZMathlib.toPolynomial f) = q := by
        rw [normalize_eq_normalize_iff_associated.mpr hq_assoc, hnorm_q]
      rw [heq]
      exact Finset.mem_coe.mpr (Multiset.mem_toFinset.mpr hq_mem)
    · -- injective on supports: equal normalized factors force associated
      -- divisors, hence the same representing subset.
      intro U hU V hV hUV
      rcases hU with ⟨f, S, hirr_f, hdvd_f, hrep_f, rfl⟩
      rcases hV with ⟨g, T, hirr_g, hdvd_g, hrep_g, rfl⟩
      rw [hφ hirr_f hdvd_f hrep_f, hφ hirr_g hdvd_g hrep_g] at hUV
      have hassoc : Associated (HexPolyZMathlib.toPolynomial f)
          (HexPolyZMathlib.toPolynomial g) :=
        normalize_eq_normalize_iff_associated.mp hUV
      have hST : S = T :=
        hpartition.unique_up_to_associated hirr_f hdvd_f (Finset.subset_univ S)
          hrep_f hirr_g hdvd_g (Finset.subset_univ T) hrep_g hassoc
      rw [hST]
    · -- surjective onto factors: every normalized irreducible factor of `X`
      -- pulls back to a `ZPoly` divisor with a representing subset.
      intro p hp
      have hp_mem : p ∈ UniqueFactorizationMonoid.normalizedFactors X :=
        Multiset.mem_toFinset.mp (Finset.mem_coe.mp hp)
      have hp_irr : Irreducible p :=
        UniqueFactorizationMonoid.irreducible_of_normalized_factor p hp_mem
      have hp_dvd : p ∣ X :=
        UniqueFactorizationMonoid.dvd_of_mem_normalizedFactors hp_mem
      have hp_norm : normalize p = p :=
        UniqueFactorizationMonoid.normalize_normalized_factor p hp_mem
      have hf_toPoly :
          HexPolyZMathlib.toPolynomial (HexPolyZMathlib.ofPolynomial p) = p :=
        HexPolyZMathlib.toPolynomial_ofPolynomial p
      have hf_irr :
          Irreducible (HexPolyZMathlib.toPolynomial
            (HexPolyZMathlib.ofPolynomial p)) := by
        rw [hf_toPoly]; exact hp_irr
      have hf_dvd : HexPolyZMathlib.ofPolynomial p ∣ core := by
        rw [hX] at hp_dvd
        rcases hp_dvd with ⟨r, hr⟩
        refine ⟨HexPolyZMathlib.ofPolynomial r, ?_⟩
        apply HexPolyZMathlib.equiv.injective
        show HexPolyZMathlib.toPolynomial core =
          HexPolyZMathlib.toPolynomial
            (HexPolyZMathlib.ofPolynomial p * HexPolyZMathlib.ofPolynomial r)
        rw [HexPolyZMathlib.toPolynomial_mul, hf_toPoly,
          HexPolyZMathlib.toPolynomial_ofPolynomial]
        exact hr
      have hf_norm_sign :
          Hex.normalizeFactorSign (HexPolyZMathlib.ofPolynomial p) =
            HexPolyZMathlib.ofPolynomial p := by
        apply normalizeFactorSign_eq_self_of_leadingCoeff_nonneg
        have hlead_normalized : normalize p.leadingCoeff = p.leadingCoeff := by
          have hlead := congrArg Polynomial.leadingCoeff hp_norm
          rwa [Polynomial.leadingCoeff_normalize] at hlead
        have hlc :
            (HexPolyZMathlib.toPolynomial
                (HexPolyZMathlib.ofPolynomial p)).leadingCoeff =
              Hex.DensePoly.leadingCoeff (HexPolyZMathlib.ofPolynomial p) :=
          HexPolyMathlib.leadingCoeff_toPolynomial _
        rw [← hlc, hf_toPoly]
        exact Int.nonneg_of_normalize_eq_self hlead_normalized
      obtain ⟨S, _hSJ, hrep⟩ :=
        hpartition.toHenselSubsetCorrespondenceRest.exists_subset
          hf_norm_sign hf_irr hf_dvd
      refine ⟨(↑S : Set (LiftedFactorIndex d)),
        ⟨HexPolyZMathlib.ofPolynomial p, S, hf_irr, hf_dvd, hrep, rfl⟩, ?_⟩
      rw [hφ hf_irr hf_dvd hrep, hf_toPoly, hp_norm]
  -- Conclude: bijection cardinality, then `Nodup` from squarefreeness.
  have hnodup : (UniqueFactorizationMonoid.normalizedFactors X).Nodup :=
    (UniqueFactorizationMonoid.squarefree_iff_nodup_normalizedFactors hX_ne).mp
      (by rw [hX]; exact hpartition.target_squarefree)
  rw [hbij.ncard_eq, Set.ncard_coe_finset,
    Multiset.toFinset_card_of_nodup hnodup]

end liftedTrueSupports

/--
Main candidate divisibility theorem for the Mathlib-side correspondence of the
Berlekamp-Zassenhaus recombination search (#4430 capstone).

Given a `LiftedFactorSubsetPartition core d J target` and a subset `T ⊆ J`,
suppose the candidate `recombinationCandidate d T` is recordable and admits
an exact quotient against `target`.  If an irreducible integer factor
`factor` of `target` is represented at the Hensel lift by some `S ⊆ T`,
then `factor` divides the recombination candidate.

Proof outline.  The exact-quotient equation
`quotient * recombinationCandidate d T = target` and the irreducibility of
`toPolynomial factor` (so it is prime in `Polynomial ℤ` by UFD) split the
divisibility into two cases:

* `toPolynomial factor ∣ toPolynomial (recombinationCandidate d T)` —
  transport back via `ofPolynomial` to obtain the desired
  `factor ∣ recombinationCandidate d T`.
* `toPolynomial factor ∣ toPolynomial quotient` — assemble a contradiction:
  when `S` is non-empty, pick any `i ∈ S ⊆ T` and apply
  `mem_T_iff_exists_irreducibleFactor_representingSubset` (#4469) to obtain
  an irreducible divisor `g` of the candidate whose representing subset
  `S_g` also contains `i`; the partition's `pairwise_disjoint` field
  contrapositively forces `Associated (toPolynomial factor) (toPolynomial g)`,
  so `toPolynomial factor ∣ toPolynomial (recombinationCandidate d T)` and
  hence `(toPolynomial factor)^2 ∣ toPolynomial target`, contradicting
  squarefreeness via `Irreducible.not_unit`.  When `S = ∅`, the recovery
  equation forces `factor = 1` (or `factor = 0` in the degenerate
  `d.p^d.k = 1` regime), again contradicting irreducibility — packaged in
  `not_represents_empty_of_irreducible_dvd_core`.
-/
theorem representedFactor_dvd_recombinationCandidate_of_subset
    {core target factor quotient : Hex.ZPoly} {d : Hex.LiftData}
    {J S T : LiftedFactorSubset d}
    (hcore_ne : core ≠ 0)
    (hcore_monic : Hex.DensePoly.Monic core)
    (hd_liftedFactor_monic : ∀ i, Hex.DensePoly.Monic (liftedFactor d i))
    (hd_liftedFactor_natDegree_pos :
      ∀ i, 0 < (HexPolyZMathlib.toPolynomial (liftedFactor d i)).natDegree)
    (hprecision :
      2 * Hex.ZPoly.defaultFactorCoeffBound core < d.p ^ d.k)
    (hpartition : LiftedFactorSubsetPartition core d J target)
    (htarget_dvd_core : target ∣ core)
    (hTJ : T ⊆ J)
    (hSJ : S ⊆ J)
    (hrecord :
      Hex.shouldRecordPolynomialFactor (recombinationCandidate d T) = true)
    (hquot :
      Hex.exactQuotient? target (recombinationCandidate d T) = some quotient)
    (hfactor_irr : Irreducible (HexPolyZMathlib.toPolynomial factor))
    (hfactor_dvd_target : factor ∣ target)
    (hrep : RepresentsIntegerFactorAtLift core d factor S)
    (hST : S ⊆ T) :
    factor ∣ recombinationCandidate d T := by
  -- Quotient equation and `candidate ∣ target` from `exactQuotient?_product`.
  have hmul : quotient * recombinationCandidate d T = target :=
    Hex.exactQuotient?_product hquot
  have hcand_dvd_target : recombinationCandidate d T ∣ target := by
    refine ⟨quotient, ?_⟩
    rw [Hex.DensePoly.mul_comm_poly (S := Int)]
    exact hmul.symm
  have hpoly_mul :
      HexPolyZMathlib.toPolynomial quotient *
          HexPolyZMathlib.toPolynomial (recombinationCandidate d T) =
        HexPolyZMathlib.toPolynomial target := by
    rw [← HexPolyZMathlib.toPolynomial_mul, hmul]
  -- UFD prime step on `toPolynomial factor`.
  have hfactor_prime : Prime (HexPolyZMathlib.toPolynomial factor) :=
    UniqueFactorizationMonoid.irreducible_iff_prime.mp hfactor_irr
  have hpoly_factor_dvd_target :
      HexPolyZMathlib.toPolynomial factor ∣
        HexPolyZMathlib.toPolynomial target :=
    HexPolyMathlib.toPolynomial_dvd hfactor_dvd_target
  rw [← hpoly_mul] at hpoly_factor_dvd_target
  rcases hfactor_prime.dvd_or_dvd hpoly_factor_dvd_target with hp_dvd_q | hp_dvd_c
  · -- Case B: `toPolynomial factor ∣ toPolynomial quotient` — derive contradiction.
    exfalso
    have hfactor_dvd_core : factor ∣ core :=
      zpoly_dvd_trans hfactor_dvd_target htarget_dvd_core
    -- `2 ≤ d.p^d.k` follows directly from the Mignotte precision: the default
    -- coefficient bound is positive for the nonzero core, so the modulus clears
    -- twice a positive quantity.
    have hd_modulus : 2 ≤ d.p ^ d.k := by
      have hb_pos : 0 < Hex.ZPoly.defaultFactorCoeffBound core :=
        Hex.ZPoly.defaultFactorCoeffBound_pos_of_ne_zero hcore_ne
      omega
    by_cases hS_empty : S = (∅ : LiftedFactorSubset d)
    · -- Subcase B2: `S = ∅` — packaged by the empty-support helper.
      apply not_represents_empty_of_irreducible_dvd_core
        hcore_ne hcore_monic hprecision hfactor_dvd_core hpartition
        hfactor_dvd_target hfactor_irr
      rw [hS_empty] at hrep
      exact hrep
    · -- Subcase B1: `S` non-empty.  Pick `i ∈ S ⊆ T`, apply #4469 to obtain
      -- `g, S_g` with `i ∈ S_g`, then use `pairwise_disjoint` contrapositively
      -- to conclude `Associated (toPolynomial factor) (toPolynomial g)`.
      have hS_ne : S.Nonempty := Finset.nonempty_iff_ne_empty.mpr hS_empty
      obtain ⟨i, hiS⟩ := hS_ne
      have hiT : i ∈ T := hST hiS
      obtain ⟨g, S_g, hg_irr, hg_dvd_cand, hg_rep, hSg_J, hi_Sg⟩ :=
        mem_T_iff_exists_irreducibleFactor_representingSubset
          hcore_ne hcore_monic hd_modulus hd_liftedFactor_monic
          hd_liftedFactor_natDegree_pos hprecision hpartition htarget_dvd_core
          hTJ hrecord hquot hiT
      have hg_dvd_target : g ∣ target :=
        zpoly_dvd_trans hg_dvd_cand hcand_dvd_target
      -- `i ∈ S ∩ S_g`, so `S` and `S_g` are not disjoint.
      have hnot_disjoint : ¬ Disjoint S S_g := by
        intro hdisj
        exact (Finset.disjoint_left.mp hdisj hiS) hi_Sg
      have hassoc :
          Associated (HexPolyZMathlib.toPolynomial factor)
            (HexPolyZMathlib.toPolynomial g) := by
        by_contra hnot_assoc
        exact hnot_disjoint
          (hpartition.pairwise_disjoint
            hfactor_irr hfactor_dvd_target hSJ hrep
            hg_irr hg_dvd_target hSg_J hg_rep hnot_assoc)
      -- `factor ∣ g ∣ candidate` (poly side) and `factor ∣ quotient` (poly side)
      -- give `factor² ∣ target` (poly side), contradicting squarefreeness.
      have hp_factor_dvd_cand :
          HexPolyZMathlib.toPolynomial factor ∣
            HexPolyZMathlib.toPolynomial (recombinationCandidate d T) :=
        hassoc.dvd.trans (HexPolyMathlib.toPolynomial_dvd hg_dvd_cand)
      have hsqdvd :
          HexPolyZMathlib.toPolynomial factor *
              HexPolyZMathlib.toPolynomial factor ∣
            HexPolyZMathlib.toPolynomial target := by
        rw [← hpoly_mul]
        exact mul_dvd_mul hp_dvd_q hp_factor_dvd_cand
      exact hfactor_irr.not_isUnit
        (hpartition.target_squarefree _ hsqdvd)
  · -- Case A: `toPolynomial factor ∣ toPolynomial (recombinationCandidate d T)`.
    -- Transport back to `Hex.ZPoly` via `ofPolynomial`.
    rcases hp_dvd_c with ⟨r, hr⟩
    refine ⟨HexPolyZMathlib.ofPolynomial r, ?_⟩
    apply HexPolyZMathlib.equiv.injective
    simp only [HexPolyZMathlib.equiv_apply, HexPolyZMathlib.toPolynomial_mul,
      HexPolyZMathlib.toPolynomial_ofPolynomial]
    exact hr

/-- Abstract-bound variant of `liftedFactorSubsetPartition_prefix_none`:
takes `B' : Nat`, `hvalid : ∀ g : Hex.ZPoly, g ∣ core → ∀ i, (g.coeff i).natAbs ≤ B'`,
and `hprecision : 2 * B' < d.p ^ d.k` in place of the core-shape
`defaultFactorCoeffBound core` precision constraint.  Routes the cover-at-min
step through
`coverAtMin_representingSubset_subset_of_recombinationCandidate_dvd_of_bound`
after building the per-normalised-factor bound `hvalid'_T` from the universal
`g ∣ core` bound via the divisibility chain
`g ∣ recombinationCandidate d T ∣ target ∣ core`. -/
theorem liftedFactorSubsetPartition_prefix_none_of_bound
    {core target factor : Hex.ZPoly} {d : Hex.LiftData}
    {J S : LiftedFactorSubset d} {localFactors : List Hex.ZPoly}
    {fuel : Nat}
    {pre suffix : List (List Hex.ZPoly × List Hex.ZPoly)}
    (B' : Nat)
    (hvalid : ∀ g : Hex.ZPoly, g ∣ core → ∀ i, (g.coeff i).natAbs ≤ B')
    (hcore_ne : core ≠ 0)
    (hcore_monic : Hex.DensePoly.Monic core)
    (hd_modulus : 2 ≤ d.p ^ d.k)
    (hd_liftedFactor_monic :
      ∀ i, Hex.DensePoly.Monic (liftedFactor d i))
    (hd_liftedFactor_natDegree_pos :
      ∀ i, 0 < (HexPolyZMathlib.toPolynomial (liftedFactor d i)).natDegree)
    (hprecision : 2 * B' < d.p ^ d.k)
    (htarget_dvd_core : target ∣ core)
    (hpartition : LiftedFactorSubsetPartition core d J target)
    (hmatches : LiftedFactorListMatches d J localFactors)
    (hlocal_nodup : localFactors.Nodup)
    (hfactor_irr : Irreducible (HexPolyZMathlib.toPolynomial factor))
    (hfactor_dvd_target : factor ∣ target)
    (hSrep : RepresentsIntegerFactorAtLift core d factor S)
    (hSJ : S ⊆ J) (hne : J.Nonempty) (hmin : J.min' hne ∈ S)
    (hsplits :
      Hex.subsetSplitsWithFirst localFactors =
        pre ++
          (liftedSubsetSelectedList d S,
           liftedSubsetSelectedList d (J \ S)) :: suffix) :
    ∀ split ∈ pre,
      (let candidate' :=
        Hex.normalizeFactorSign <|
          Hex.ZPoly.primitivePart <|
            Hex.centeredLiftPoly (Array.polyProduct split.1.toArray)
              (d.p ^ d.k)
      if Hex.shouldRecordPolynomialFactor candidate' then
        match Hex.exactQuotient? target candidate' with
        | none => none
        | some quotient' =>
            match Hex.recombinationSearchModAux quotient' (d.p ^ d.k)
                split.2 fuel with
            | none => none
            | some r => some (candidate' :: r)
      else none) = none := by
  intro split hsplit
  obtain ⟨T, hTJ, hmin_in_T, hsplit_eq, i, _hi_J, hi_S, hi_notT⟩ :=
    liftedSubsetSplit_prefix_exists_mem_sdiff_of_matches
      hlocal_nodup hmatches hSJ hne hmin hsplits hsplit
  subst hsplit_eq
  show (if Hex.shouldRecordPolynomialFactor (recombinationCandidate d T) then
      match Hex.exactQuotient? target (recombinationCandidate d T) with
      | none => none
      | some quotient' =>
          match Hex.recombinationSearchModAux quotient' (d.p ^ d.k)
              (liftedSubsetSelectedList d (J \ T)) fuel with
          | none => none
          | some r => some (recombinationCandidate d T :: r)
      else none) = none
  by_cases hrec :
      Hex.shouldRecordPolynomialFactor (recombinationCandidate d T) = true
  · rw [if_pos hrec]
    cases hquot :
        Hex.exactQuotient? target (recombinationCandidate d T) with
    | none => rfl
    | some quotient' =>
      exfalso
      -- Build the per-normalised-factor bound `hvalid'_T` from the universal
      -- `g ∣ core` bound by chaining
      -- `g ∣ recombinationCandidate d T ∣ target ∣ core`.
      have hcand_dvd_target :
          recombinationCandidate d T ∣ target := by
        have hmul :
            quotient' * recombinationCandidate d T = target :=
          Hex.exactQuotient?_product hquot
        refine ⟨quotient', ?_⟩
        rw [Hex.DensePoly.mul_comm_poly (S := Int)]
        exact hmul.symm
      have hcand_dvd_core :
          recombinationCandidate d T ∣ core :=
        zpoly_dvd_trans hcand_dvd_target htarget_dvd_core
      have hvalid'_T : ∀ g : Hex.ZPoly,
          HexPolyZMathlib.toPolynomial g ∈
            UniqueFactorizationMonoid.normalizedFactors
              (HexPolyZMathlib.toPolynomial
                (recombinationCandidate d T)) →
          ∀ i, (g.coeff i).natAbs ≤ B' := by
        intro g hg_mem
        have hg_poly_dvd : HexPolyZMathlib.toPolynomial g ∣
            HexPolyZMathlib.toPolynomial
              (recombinationCandidate d T) :=
          UniqueFactorizationMonoid.dvd_of_mem_normalizedFactors hg_mem
        have hg_dvd_cand : g ∣ recombinationCandidate d T := by
          rcases hg_poly_dvd with ⟨r, hr⟩
          refine ⟨HexPolyZMathlib.ofPolynomial r, ?_⟩
          apply HexPolyZMathlib.equiv.injective
          simp only [HexPolyZMathlib.equiv_apply, HexPolyZMathlib.toPolynomial_mul,
            HexPolyZMathlib.toPolynomial_ofPolynomial]
          exact hr
        have hg_dvd_core : g ∣ core :=
          zpoly_dvd_trans hg_dvd_cand hcand_dvd_core
        exact hvalid g hg_dvd_core
      obtain ⟨f_cov, S_cov, hf_cov_irr, hf_cov_dvd_target, hS_cov_J,
              hmin_in_S_cov, hS_cov_rep, hS_cov_T⟩ :=
        coverAtMin_representingSubset_subset_of_recombinationCandidate_dvd_of_bound
          B' hvalid'_T
          hcore_ne hcore_monic hd_modulus hd_liftedFactor_monic
          hd_liftedFactor_natDegree_pos hprecision hpartition
          htarget_dvd_core hTJ hne hmin_in_T hrec hquot
      have hnot_disjoint : ¬ Disjoint S S_cov := fun hdisj =>
        Finset.disjoint_left.mp hdisj hmin hmin_in_S_cov
      have hassoc :
          Associated (HexPolyZMathlib.toPolynomial factor)
            (HexPolyZMathlib.toPolynomial f_cov) := by
        by_contra hnot_assoc
        exact hnot_disjoint
          (hpartition.pairwise_disjoint
            hfactor_irr hfactor_dvd_target hSJ hSrep
            hf_cov_irr hf_cov_dvd_target hS_cov_J hS_cov_rep hnot_assoc)
      have hSeq : S = S_cov :=
        hpartition.unique_up_to_associated
          hfactor_irr hfactor_dvd_target hSJ hSrep
          hf_cov_irr hf_cov_dvd_target hS_cov_J hS_cov_rep hassoc
      have hi_S_cov : i ∈ S_cov := hSeq ▸ hi_S
      exact hi_notT (hS_cov_T hi_S_cov)
  · rw [if_neg hrec]

/--
Prefix-none discharge under a `LiftedFactorSubsetPartition` (#4367 capstone).

Caller for the recursive coverage proof of
`Hex.recombinationSearchModAux` (#4301).  Every executable split in `pre`
— i.e. enumerated **before** the canonical boundary split
`(liftedSubsetSelectedList d S, liftedSubsetSelectedList d (J \ S))` —
returns `none` when threaded through one step of the recombination search,
provided `S` is the representing subset of an irreducible integer factor at
`J`'s minimum index.

Proof outline.
1. Apply `liftedSubsetSplit_prefix_exists_mem_sdiff_of_matches` (the
   #4508 wrapper) to recover the proof-side subset `T ⊆ J` with
   `J.min' ∈ T` whose canonical split equals `split`, and to obtain a
   witness index `i ∈ J ∩ S \ T`.
2. Identify the inline `candidate'` with `recombinationCandidate d T`
   by definitional unfolding.
3. Split on `Hex.shouldRecordPolynomialFactor (recombinationCandidate d T)`:
   - `false`: the if-branch yields `none` directly.
   - `true`: suppose `Hex.exactQuotient? target (recombinationCandidate d T)
     = some quotient'`. Then
     `coverAtMin_representingSubset_subset_of_recombinationCandidate_dvd`
     (#4395 / PR #4498) produces a representing subset `S_cov ⊆ T` with
     `J.min' ∈ S_cov` representing some irreducible `f_cov`.  Together with
     the hypothesised representing factor for `S`, the partition's
     `pairwise_disjoint` field (via the shared `J.min'`) forces
     `Associated factor f_cov`, then `unique_up_to_associated` collapses
     `S = S_cov ⊆ T`.  But `i ∈ S \ T` from the wrapper, contradicting
     `S ⊆ T`.

The `hlocal_nodup` precondition is required by the wrapper for the
mask-level bit-diff argument (without `Nodup`, the executable
`subsetSplits` enumeration can produce collisions on shared masked lists).
The caller in #4301 threads `Nodup` from a Hensel-coprimality fact
against the partition; a self-contained `liftedFactor d`-injectivity
helper at the partition level is left as a separable sub-task.

This is the `defaultFactorCoeffBound core`-instantiated thin wrapper for
`liftedFactorSubsetPartition_prefix_none_of_bound`: the universal coefficient
bound for `g ∣ core` is discharged by `defaultFactorCoeffBound_valid` itself.
-/
theorem liftedFactorSubsetPartition_prefix_none
    {core target factor : Hex.ZPoly} {d : Hex.LiftData}
    {J S : LiftedFactorSubset d} {localFactors : List Hex.ZPoly}
    {fuel : Nat}
    {pre suffix : List (List Hex.ZPoly × List Hex.ZPoly)}
    (hcore_ne : core ≠ 0)
    (hcore_monic : Hex.DensePoly.Monic core)
    (hd_modulus : 2 ≤ d.p ^ d.k)
    (hd_liftedFactor_monic :
      ∀ i, Hex.DensePoly.Monic (liftedFactor d i))
    (hd_liftedFactor_natDegree_pos :
      ∀ i, 0 < (HexPolyZMathlib.toPolynomial (liftedFactor d i)).natDegree)
    (hprecision :
      2 * Hex.ZPoly.defaultFactorCoeffBound core < d.p ^ d.k)
    (htarget_dvd_core : target ∣ core)
    (hpartition : LiftedFactorSubsetPartition core d J target)
    (hmatches : LiftedFactorListMatches d J localFactors)
    (hlocal_nodup : localFactors.Nodup)
    (hfactor_irr : Irreducible (HexPolyZMathlib.toPolynomial factor))
    (hfactor_dvd_target : factor ∣ target)
    (hSrep : RepresentsIntegerFactorAtLift core d factor S)
    (hSJ : S ⊆ J) (hne : J.Nonempty) (hmin : J.min' hne ∈ S)
    (hsplits :
      Hex.subsetSplitsWithFirst localFactors =
        pre ++
          (liftedSubsetSelectedList d S,
           liftedSubsetSelectedList d (J \ S)) :: suffix) :
    ∀ split ∈ pre,
      (let candidate' :=
        Hex.normalizeFactorSign <|
          Hex.ZPoly.primitivePart <|
            Hex.centeredLiftPoly (Array.polyProduct split.1.toArray)
              (d.p ^ d.k)
      if Hex.shouldRecordPolynomialFactor candidate' then
        match Hex.exactQuotient? target candidate' with
        | none => none
        | some quotient' =>
            match Hex.recombinationSearchModAux quotient' (d.p ^ d.k)
                split.2 fuel with
            | none => none
            | some r => some (candidate' :: r)
      else none) = none :=
  liftedFactorSubsetPartition_prefix_none_of_bound
    (Hex.ZPoly.defaultFactorCoeffBound core)
    (defaultFactorCoeffBound_valid core hcore_ne)
    hcore_ne hcore_monic hd_modulus hd_liftedFactor_monic
    hd_liftedFactor_natDegree_pos hprecision htarget_dvd_core hpartition
    hmatches hlocal_nodup hfactor_irr hfactor_dvd_target hSrep hSJ hne hmin
    hsplits

/-- Abstract-bound variant of
`liftedFactorSubsetPartition_prefix_none_of_primitive_pos_lc_core`:
takes `B' : Nat`, the leading-coefficient bound `hcore_lc_le`, the universal
core-divisor coefficient bound `hvalid`, and `hprecision : 2 * B' < d.p ^ d.k`
in place of the core-shape `defaultFactorCoeffBound core` precision constraint.

`T` is bound locally inside the proof body, so the `hvalid` hypothesis cannot
mention `T` at the binder level; the universal `g ∣ core` form is used instead.
Inside the inner `some` branch, the per-normalised-factor bound on the
candidate's normalised factors is built by chaining
`g ∣ recombinationCandidate d T ∣ target ∣ core` and applying `hvalid`.

The proof body otherwise mirrors the original (now-wrapper) verbatim: the
wrapper-decomposition via `liftedSubsetSplit_prefix_exists_mem_sdiff_of_matches`,
the case-split on `shouldRecordPolynomialFactor` / `exactQuotient?`, and the
`pairwise_disjoint` / `unique_up_to_associated` contradiction. Only the
cover-at-min call is rerouted through
`coverAtMin_representingSubset_subset_of_recombinationCandidate_dvd_of_primitive_pos_lc_core_of_bound`.
-/
theorem liftedFactorSubsetPartition_prefix_none_of_primitive_pos_lc_core_of_bound
    {core target factor : Hex.ZPoly} {d : Hex.LiftData}
    {J S : LiftedFactorSubset d} {localFactors : List Hex.ZPoly}
    {fuel : Nat}
    {pre suffix : List (List Hex.ZPoly × List Hex.ZPoly)}
    (B' : Nat)
    (hcore_lc_le : (Hex.DensePoly.leadingCoeff core).natAbs ≤ B')
    (hvalid : ∀ g : Hex.ZPoly, g ∣ core → ∀ i, (g.coeff i).natAbs ≤ B')
    (hcore_ne : core ≠ 0)
    (hcore_primitive : Hex.ZPoly.Primitive core)
    (hcore_lc_pos : 0 < Hex.DensePoly.leadingCoeff core)
    (hcore_monic : Hex.DensePoly.Monic core)
    (hd_modulus : 2 ≤ d.p ^ d.k)
    (hd_liftedFactor_monic :
      ∀ i, Hex.DensePoly.Monic (liftedFactor d i))
    (hd_liftedFactor_natDegree_pos :
      ∀ i, 0 < (HexPolyZMathlib.toPolynomial (liftedFactor d i)).natDegree)
    (hprecision : 2 * B' < d.p ^ d.k)
    (htarget_dvd_core : target ∣ core)
    (hpartition : LiftedFactorSubsetPartition core d J target)
    (hmatches : LiftedFactorListMatches d J localFactors)
    (hlocal_nodup : localFactors.Nodup)
    (hfactor_irr : Irreducible (HexPolyZMathlib.toPolynomial factor))
    (hfactor_dvd_target : factor ∣ target)
    (hSrep : RepresentsIntegerFactorAtLift core d factor S)
    (hSJ : S ⊆ J) (hne : J.Nonempty) (hmin : J.min' hne ∈ S)
    (hsplits :
      Hex.subsetSplitsWithFirst localFactors =
        pre ++
          (liftedSubsetSelectedList d S,
           liftedSubsetSelectedList d (J \ S)) :: suffix) :
    ∀ split ∈ pre,
      (let candidate' :=
        Hex.normalizeFactorSign <|
          Hex.ZPoly.primitivePart <|
            Hex.centeredLiftPoly (Array.polyProduct split.1.toArray)
              (d.p ^ d.k)
      if Hex.shouldRecordPolynomialFactor candidate' then
        match Hex.exactQuotient? target candidate' with
        | none => none
        | some quotient' =>
            match Hex.recombinationSearchModAux quotient' (d.p ^ d.k)
                split.2 fuel with
            | none => none
            | some r => some (candidate' :: r)
      else none) = none := by
  intro split hsplit
  obtain ⟨T, hTJ, hmin_in_T, hsplit_eq, i, hi_J, hi_S, hi_notT⟩ :=
    liftedSubsetSplit_prefix_exists_mem_sdiff_of_matches
      hlocal_nodup hmatches hSJ hne hmin hsplits hsplit
  subst hsplit_eq
  show (if Hex.shouldRecordPolynomialFactor (recombinationCandidate d T) then
      match Hex.exactQuotient? target (recombinationCandidate d T) with
      | none => none
      | some quotient' =>
          match Hex.recombinationSearchModAux quotient' (d.p ^ d.k)
              (liftedSubsetSelectedList d (J \ T)) fuel with
          | none => none
          | some r => some (recombinationCandidate d T :: r)
      else none) = none
  by_cases hrec :
      Hex.shouldRecordPolynomialFactor (recombinationCandidate d T) = true
  · rw [if_pos hrec]
    cases hquot :
        Hex.exactQuotient? target (recombinationCandidate d T) with
    | none => rfl
    | some quotient' =>
      exfalso
      -- Build the per-normalised-factor bound `hvalid'_T` from the universal
      -- `g ∣ core` bound by chaining
      -- `g ∣ recombinationCandidate d T ∣ target ∣ core`.
      have hcand_dvd_target :
          recombinationCandidate d T ∣ target := by
        have hmul :
            quotient' * recombinationCandidate d T = target :=
          Hex.exactQuotient?_product hquot
        refine ⟨quotient', ?_⟩
        rw [Hex.DensePoly.mul_comm_poly (S := Int)]
        exact hmul.symm
      have hcand_dvd_core :
          recombinationCandidate d T ∣ core :=
        zpoly_dvd_trans hcand_dvd_target htarget_dvd_core
      have hvalid'_T : ∀ g : Hex.ZPoly,
          HexPolyZMathlib.toPolynomial g ∈
            UniqueFactorizationMonoid.normalizedFactors
              (HexPolyZMathlib.toPolynomial
                (recombinationCandidate d T)) →
          ∀ i, (g.coeff i).natAbs ≤ B' := by
        intro g hg_mem
        have hg_poly_dvd : HexPolyZMathlib.toPolynomial g ∣
            HexPolyZMathlib.toPolynomial
              (recombinationCandidate d T) :=
          UniqueFactorizationMonoid.dvd_of_mem_normalizedFactors hg_mem
        have hg_dvd_cand : g ∣ recombinationCandidate d T := by
          rcases hg_poly_dvd with ⟨r, hr⟩
          refine ⟨HexPolyZMathlib.ofPolynomial r, ?_⟩
          apply HexPolyZMathlib.equiv.injective
          simp only [HexPolyZMathlib.equiv_apply, HexPolyZMathlib.toPolynomial_mul,
            HexPolyZMathlib.toPolynomial_ofPolynomial]
          exact hr
        have hg_dvd_core : g ∣ core :=
          zpoly_dvd_trans hg_dvd_cand hcand_dvd_core
        exact hvalid g hg_dvd_core
      obtain ⟨f_cov, S_cov, hf_cov_irr, hf_cov_dvd_target, hS_cov_J,
              hmin_in_S_cov, hS_cov_rep, hS_cov_T⟩ :=
        coverAtMin_representingSubset_subset_of_recombinationCandidate_dvd_of_primitive_pos_lc_core_of_bound
          B' hvalid'_T hcore_ne hcore_primitive hcore_lc_pos hcore_monic hcore_lc_le
          hd_modulus hd_liftedFactor_monic hd_liftedFactor_natDegree_pos
          hprecision hpartition htarget_dvd_core hTJ hne hmin_in_T hrec hquot
      have hnot_disjoint : ¬ Disjoint S S_cov := fun hdisj =>
        Finset.disjoint_left.mp hdisj hmin hmin_in_S_cov
      have hassoc :
          Associated (HexPolyZMathlib.toPolynomial factor)
            (HexPolyZMathlib.toPolynomial f_cov) := by
        by_contra hnot_assoc
        exact hnot_disjoint
          (hpartition.pairwise_disjoint
            hfactor_irr hfactor_dvd_target hSJ hSrep
            hf_cov_irr hf_cov_dvd_target hS_cov_J hS_cov_rep hnot_assoc)
      have hSeq : S = S_cov :=
        hpartition.unique_up_to_associated
          hfactor_irr hfactor_dvd_target hSJ hSrep
          hf_cov_irr hf_cov_dvd_target hS_cov_J hS_cov_rep hassoc
      have hi_S_cov : i ∈ S_cov := hSeq ▸ hi_S
      exact hi_notT (hS_cov_T hi_S_cov)
  · rw [if_neg hrec]

/-- Primitive + positive-leading-core variant of
`liftedFactorSubsetPartition_prefix_none` (#4646).

Identical to the monic version except the cover-at-min step routes through
`coverAtMin_representingSubset_subset_of_recombinationCandidate_dvd_of_primitive_pos_lc_core`.
The structural cover/pairwise-disjoint/unique fields of the partition do not
depend on `Monic core`, so the rest of the proof carries over verbatim.

This is the `defaultFactorCoeffBound core`-instantiated thin wrapper for
`liftedFactorSubsetPartition_prefix_none_of_primitive_pos_lc_core_of_bound`:
the leading-coefficient bound is discharged via
`defaultFactorCoeffBound_leadingCoeff_natAbs_le`, and the universal
coefficient bound for `g ∣ core` is `defaultFactorCoeffBound_valid` itself. -/
theorem liftedFactorSubsetPartition_prefix_none_of_primitive_pos_lc_core
    {core target factor : Hex.ZPoly} {d : Hex.LiftData}
    {J S : LiftedFactorSubset d} {localFactors : List Hex.ZPoly}
    {fuel : Nat}
    {pre suffix : List (List Hex.ZPoly × List Hex.ZPoly)}
    (hcore_ne : core ≠ 0)
    (hcore_primitive : Hex.ZPoly.Primitive core)
    (hcore_lc_pos : 0 < Hex.DensePoly.leadingCoeff core)
    (hcore_monic : Hex.DensePoly.Monic core)
    (hd_modulus : 2 ≤ d.p ^ d.k)
    (hd_liftedFactor_monic :
      ∀ i, Hex.DensePoly.Monic (liftedFactor d i))
    (hd_liftedFactor_natDegree_pos :
      ∀ i, 0 < (HexPolyZMathlib.toPolynomial (liftedFactor d i)).natDegree)
    (hprecision :
      2 * Hex.ZPoly.defaultFactorCoeffBound core < d.p ^ d.k)
    (htarget_dvd_core : target ∣ core)
    (hpartition : LiftedFactorSubsetPartition core d J target)
    (hmatches : LiftedFactorListMatches d J localFactors)
    (hlocal_nodup : localFactors.Nodup)
    (hfactor_irr : Irreducible (HexPolyZMathlib.toPolynomial factor))
    (hfactor_dvd_target : factor ∣ target)
    (hSrep : RepresentsIntegerFactorAtLift core d factor S)
    (hSJ : S ⊆ J) (hne : J.Nonempty) (hmin : J.min' hne ∈ S)
    (hsplits :
      Hex.subsetSplitsWithFirst localFactors =
        pre ++
          (liftedSubsetSelectedList d S,
           liftedSubsetSelectedList d (J \ S)) :: suffix) :
    ∀ split ∈ pre,
      (let candidate' :=
        Hex.normalizeFactorSign <|
          Hex.ZPoly.primitivePart <|
            Hex.centeredLiftPoly (Array.polyProduct split.1.toArray)
              (d.p ^ d.k)
      if Hex.shouldRecordPolynomialFactor candidate' then
        match Hex.exactQuotient? target candidate' with
        | none => none
        | some quotient' =>
            match Hex.recombinationSearchModAux quotient' (d.p ^ d.k)
                split.2 fuel with
            | none => none
            | some r => some (candidate' :: r)
      else none) = none := by
  have hcore_lc_le := defaultFactorCoeffBound_leadingCoeff_natAbs_le hcore_ne
  exact liftedFactorSubsetPartition_prefix_none_of_primitive_pos_lc_core_of_bound
    (Hex.ZPoly.defaultFactorCoeffBound core)
    hcore_lc_le
    (defaultFactorCoeffBound_valid core hcore_ne)
    hcore_ne hcore_primitive hcore_lc_pos hcore_monic hd_modulus hd_liftedFactor_monic
    hd_liftedFactor_natDegree_pos hprecision htarget_dvd_core hpartition
    hmatches hlocal_nodup hfactor_irr hfactor_dvd_target hSrep hSJ hne hmin
    hsplits

/-- The recovered candidate is a fixed point of `Hex.normalizeFactorSign`: its
construction applies `Hex.normalizeFactorSign` as the outermost operation. -/
private theorem normalizeFactorSign_liftedRecoveryCandidate_eq
    {core : Hex.ZPoly} {d : Hex.LiftData} (T : LiftedFactorSubset d) :
    Hex.normalizeFactorSign (liftedRecoveryCandidate core d T) =
      liftedRecoveryCandidate core d T := by
  have hnonneg :
      0 ≤ Hex.DensePoly.leadingCoeff (liftedRecoveryCandidate core d T) := by
    show 0 ≤ Hex.DensePoly.leadingCoeff (Hex.normalizeFactorSign _)
    exact leadingCoeff_normalizeFactorSign_nonneg _
  unfold Hex.normalizeFactorSign
  have hnot :
      ¬ Hex.DensePoly.leadingCoeff (liftedRecoveryCandidate core d T) < 0 := by
    omega
  rw [if_neg hnot]

/-- The recovered candidate's transport is squarefree whenever it exactly
divides the squarefree `target`. -/
private theorem toPolynomial_liftedRecoveryCandidate_squarefree
    {core target quotient : Hex.ZPoly} {d : Hex.LiftData}
    {J T : LiftedFactorSubset d}
    (hpartition : LiftedFactorSubsetPartition core d J target)
    (hquot :
      Hex.exactQuotient? target (liftedRecoveryCandidate core d T) =
        some quotient) :
    Squarefree (HexPolyZMathlib.toPolynomial
      (liftedRecoveryCandidate core d T)) := by
  have hmul : quotient * liftedRecoveryCandidate core d T = target :=
    Hex.exactQuotient?_product hquot
  have hcand_dvd_target : liftedRecoveryCandidate core d T ∣ target := by
    refine ⟨quotient, ?_⟩
    rw [Hex.DensePoly.mul_comm_poly (S := Int)]
    exact hmul.symm
  exact Squarefree.squarefree_of_dvd
    (HexPolyMathlib.toPolynomial_dvd hcand_dvd_target) hpartition.target_squarefree

/-- Recovered-candidate analogue of
`exists_representingSubset_of_mem_normalizedFactors_scaledRecombinationCandidate_of_primitive_pos_lc_core_of_bound`. -/
private theorem exists_representingSubset_of_mem_normalizedFactors_liftedRecoveryCandidate_of_bound
    {core target quotient : Hex.ZPoly} {d : Hex.LiftData}
    {J T : LiftedFactorSubset d}
    (B' : Nat)
    (hvalid : ∀ g : Hex.ZPoly,
      HexPolyZMathlib.toPolynomial g ∈
        UniqueFactorizationMonoid.normalizedFactors
          (HexPolyZMathlib.toPolynomial
            (liftedRecoveryCandidate core d T)) →
      ∀ i, (g.coeff i).natAbs ≤ B')
    (hcore_lc_le : (Hex.DensePoly.leadingCoeff core).natAbs ≤ B')
    (hcore_ne : core ≠ 0)
    (_hcore_primitive : Hex.ZPoly.Primitive core)
    (hcore_lc_pos : 0 < Hex.DensePoly.leadingCoeff core)
    (hd_liftedFactor_monic : ∀ i, Hex.DensePoly.Monic (liftedFactor d i))
    (hprecision : 2 * B' < d.p ^ d.k)
    (hpartition : LiftedFactorSubsetPartition core d J target)
    (htarget_dvd_core : target ∣ core)
    (hTJ : T ⊆ J)
    (hrecord :
      Hex.shouldRecordPolynomialFactor
          (liftedRecoveryCandidate core d T) = true)
    (hquot :
      Hex.exactQuotient? target (liftedRecoveryCandidate core d T) =
        some quotient)
    {gPoly : Polynomial ℤ}
    (hg_mem : gPoly ∈ UniqueFactorizationMonoid.normalizedFactors
      (HexPolyZMathlib.toPolynomial (liftedRecoveryCandidate core d T))) :
    ∃ (g : Hex.ZPoly) (S_g : LiftedFactorSubset d),
      HexPolyZMathlib.toPolynomial g = gPoly ∧
      Irreducible (HexPolyZMathlib.toPolynomial g) ∧
      g ∣ target ∧
      g ∣ liftedRecoveryCandidate core d T ∧
      RepresentsIntegerFactorAtLift core d g S_g ∧
      S_g ⊆ J ∧
      S_g ⊆ T ∧
      Hex.ZPoly.content g = 1 ∧
      Hex.normalizeFactorSign g = g := by
  obtain ⟨hcand_poly_ne_zero, _hcand_poly_nonunit⟩ :=
    toPolynomial_ne_zero_and_not_isUnit_of_shouldRecord hrecord
  have hg_norm :=
    (UniqueFactorizationMonoid.mem_normalizedFactors_iff'
      (p := gPoly)
      (x := HexPolyZMathlib.toPolynomial (liftedRecoveryCandidate core d T))
      hcand_poly_ne_zero).mp hg_mem
  rcases hg_norm with ⟨hg_irr, hg_normalized, hg_dvd_cand_poly⟩
  let g : Hex.ZPoly := HexPolyZMathlib.ofPolynomial gPoly
  have hg_toPolynomial : HexPolyZMathlib.toPolynomial g = gPoly :=
    HexPolyZMathlib.toPolynomial_ofPolynomial gPoly
  have hg_irr_toPoly : Irreducible (HexPolyZMathlib.toPolynomial g) := by
    rw [hg_toPolynomial]
    exact hg_irr
  have hg_dvd_cand : g ∣ liftedRecoveryCandidate core d T := by
    rcases hg_dvd_cand_poly with ⟨r, hr⟩
    refine ⟨HexPolyZMathlib.ofPolynomial r, ?_⟩
    apply HexPolyZMathlib.equiv.injective
    simp only [HexPolyZMathlib.equiv_apply, HexPolyZMathlib.toPolynomial_mul,
      HexPolyZMathlib.toPolynomial_ofPolynomial]
    rw [hg_toPolynomial]
    exact hr
  have hcand_dvd_target : liftedRecoveryCandidate core d T ∣ target := by
    have hmul : quotient * liftedRecoveryCandidate core d T = target :=
      Hex.exactQuotient?_product hquot
    refine ⟨quotient, ?_⟩
    rw [Hex.DensePoly.mul_comm_poly (S := Int)]
    exact hmul.symm
  have hg_dvd_target : g ∣ target := zpoly_dvd_trans hg_dvd_cand hcand_dvd_target
  have hcand_primitive : Hex.ZPoly.Primitive
      (liftedRecoveryCandidate core d T) :=
    zpoly_primitive_liftedRecoveryCandidate_of_bound
      B' hcore_lc_pos hcore_lc_le hd_liftedFactor_monic hprecision T
  have hcand_poly_primitive :
      (HexPolyZMathlib.toPolynomial
        (liftedRecoveryCandidate core d T)).IsPrimitive :=
    toPolynomial_isPrimitive_of_zpoly_primitive_basic hcand_primitive
  have hg_poly_primitive : gPoly.IsPrimitive :=
    isPrimitive_of_dvd hcand_poly_primitive hg_dvd_cand_poly
  have hg_content : Hex.ZPoly.content g = 1 := by
    have : (HexPolyZMathlib.toPolynomial g).IsPrimitive := by
      rw [hg_toPolynomial]; exact hg_poly_primitive
    exact zpoly_primitive_of_toPolynomial_isPrimitive_basic this
  have hg_lead_nonneg : 0 ≤ gPoly.leadingCoeff := by
    have hlead_normalized :
        normalize gPoly.leadingCoeff = gPoly.leadingCoeff := by
      have hlead := congrArg Polynomial.leadingCoeff hg_normalized
      rwa [Polynomial.leadingCoeff_normalize] at hlead
    exact Int.nonneg_of_normalize_eq_self hlead_normalized
  have hg_norm_sign : Hex.normalizeFactorSign g = g := by
    have hg_hex_lc_nonneg : 0 ≤ Hex.DensePoly.leadingCoeff g := by
      have hlc :
          (HexPolyZMathlib.toPolynomial g).leadingCoeff =
            Hex.DensePoly.leadingCoeff g :=
        HexPolyMathlib.leadingCoeff_toPolynomial g
      rw [← hlc, hg_toPolynomial]
      exact hg_lead_nonneg
    unfold Hex.normalizeFactorSign
    have hnot : ¬ Hex.DensePoly.leadingCoeff g < 0 := by omega
    rw [if_neg hnot]
  obtain ⟨S_g, hSJ, hSrep⟩ :=
    hpartition.exists_subset hg_norm_sign hg_irr_toPoly hg_dvd_target
  have hST : S_g ⊆ T :=
    representingSubset_subset_of_dvd_liftedRecoveryCandidate_of_primitive_pos_lc_core_of_bound
      B' (hvalid g (by rw [hg_toPolynomial]; exact hg_mem))
      hcore_ne _hcore_primitive hcore_lc_pos hprecision htarget_dvd_core
      hpartition hTJ hg_irr_toPoly hg_dvd_target hg_content hg_norm_sign
      hg_dvd_cand hSJ hSrep
  exact ⟨g, S_g, hg_toPolynomial, hg_irr_toPoly, hg_dvd_target, hg_dvd_cand,
    hSrep, hSJ, hST, hg_content, hg_norm_sign⟩

/-- Recovered-candidate analogue of
`exists_mem_representedSubset_of_degree_cover_of_scaledRecombinationCandidate_of_primitive_pos_lc_core_of_bound`. -/
private theorem exists_mem_representedSubset_of_degree_cover_of_liftedRecoveryCandidate_of_bound
    {core target : Hex.ZPoly} {d : Hex.LiftData}
    {J T : LiftedFactorSubset d}
    (B' : Nat)
    (hcore_ne : core ≠ 0)
    (hcore_primitive : Hex.ZPoly.Primitive core)
    (hcore_lc_pos : 0 < Hex.DensePoly.leadingCoeff core)
    (hcore_lc_le : (Hex.DensePoly.leadingCoeff core).natAbs ≤ B')
    (hd_liftedFactor_monic :
      ∀ i, Hex.DensePoly.Monic (liftedFactor d i))
    (hd_liftedFactor_natDegree_pos :
      ∀ i, 0 < (HexPolyZMathlib.toPolynomial (liftedFactor d i)).natDegree)
    (hprecision : 2 * B' < d.p ^ d.k)
    (hpartition : LiftedFactorSubsetPartition core d J target)
    (_htarget_dvd_core : target ∣ core)
    (_hTJ : T ⊆ J)
    (gs : Finset Hex.ZPoly)
    (S_of : Hex.ZPoly → LiftedFactorSubset d)
    (h_each : ∀ g ∈ gs,
      Irreducible (HexPolyZMathlib.toPolynomial g) ∧
      g ∣ target ∧
      g ∣ liftedRecoveryCandidate core d T ∧
      RepresentsIntegerFactorAtLift core d g (S_of g) ∧
      S_of g ⊆ J ∧
      S_of g ⊆ T ∧
      Hex.ZPoly.content g = 1 ∧
      Hex.normalizeFactorSign g = g)
    (hvalid : ∀ g ∈ gs, ∀ i, (g.coeff i).natAbs ≤ B')
    (h_pairwise_not_associated :
      ∀ ⦃g h : Hex.ZPoly⦄, g ∈ gs → h ∈ gs → g ≠ h →
        ¬ Associated (HexPolyZMathlib.toPolynomial g)
          (HexPolyZMathlib.toPolynomial h))
    (h_degree_total :
      (HexPolyZMathlib.toPolynomial
          (liftedRecoveryCandidate core d T)).natDegree =
        ∑ g ∈ gs, (HexPolyZMathlib.toPolynomial g).natDegree) :
    ∀ {i : LiftedFactorIndex d}, i ∈ T → ∃ g ∈ gs, i ∈ S_of g := by
  set f : LiftedFactorIndex d → Nat :=
    fun j => (HexPolyZMathlib.toPolynomial (liftedFactor d j)).natDegree
  have h_cand_eq :
      (HexPolyZMathlib.toPolynomial
          (liftedRecoveryCandidate core d T)).natDegree =
        ∑ j ∈ T, f j :=
    natDegree_toPolynomial_liftedRecoveryCandidate_eq_sum_of_bound
      B' hcore_lc_pos hcore_lc_le hd_liftedFactor_monic hprecision T
  have h_g_eq : ∀ g ∈ gs,
      (HexPolyZMathlib.toPolynomial g).natDegree = ∑ j ∈ S_of g, f j := by
    intro g hg
    obtain ⟨hg_irr, hg_dvd, _, hg_rep, hg_SJ, _, _, _⟩ := h_each g hg
    exact natDegree_toPolynomial_eq_sum_of_represents_of_primitive_pos_lc_core_of_bound
      B' (hvalid g hg) hcore_lc_le hcore_ne hcore_primitive hcore_lc_pos
      hd_liftedFactor_monic hpartition hg_irr hg_dvd hg_SJ hg_rep hprecision
  have h_pwdisj : Set.PairwiseDisjoint (↑gs : Set Hex.ZPoly) S_of := by
    intro g hg h hh hgh
    obtain ⟨hg_irr, hg_dvd, _, hg_rep, hg_SJ, _, _, _⟩ := h_each g hg
    obtain ⟨hh_irr, hh_dvd, _, hh_rep, hh_SJ, _, _, _⟩ := h_each h hh
    exact hpartition.pairwise_disjoint hg_irr hg_dvd hg_SJ hg_rep
      hh_irr hh_dvd hh_SJ hh_rep
      (h_pairwise_not_associated hg hh hgh)
  have h_sub : gs.biUnion S_of ⊆ T := by
    intro j hj
    obtain ⟨g, hg, hjg⟩ := Finset.mem_biUnion.mp hj
    exact (h_each g hg).2.2.2.2.2.1 hjg
  have h_sum_eq :
      ∑ j ∈ T, f j = ∑ j ∈ gs.biUnion S_of, f j := by
    have h_step : ∑ j ∈ gs.biUnion S_of, f j = ∑ g ∈ gs, ∑ j ∈ S_of g, f j :=
      Finset.sum_biUnion h_pwdisj
    rw [h_step, ← h_cand_eq, h_degree_total]
    exact Finset.sum_congr rfl h_g_eq
  have h_zero : ∑ j ∈ T \ gs.biUnion S_of, f j = 0 := by
    have h_split :
        (∑ j ∈ T \ gs.biUnion S_of, f j) +
            (∑ j ∈ gs.biUnion S_of, f j) =
          ∑ j ∈ T, f j :=
      Finset.sum_sdiff h_sub
    omega
  have h_empty : T \ gs.biUnion S_of = ∅ := by
    by_contra hne
    obtain ⟨j, hj⟩ := Finset.nonempty_iff_ne_empty.mpr hne
    have h_le : f j ≤ ∑ k ∈ T \ gs.biUnion S_of, f k :=
      Finset.single_le_sum (f := f) (fun _ _ => Nat.zero_le _) hj
    have h_pos : 0 < f j := hd_liftedFactor_natDegree_pos j
    omega
  intro i hi
  have hi_in_bU : i ∈ gs.biUnion S_of := by
    by_contra h_not
    have h_in_sdiff : i ∈ T \ gs.biUnion S_of :=
      Finset.mem_sdiff.mpr ⟨hi, h_not⟩
    rw [h_empty] at h_in_sdiff
    exact Finset.notMem_empty _ h_in_sdiff
  exact Finset.mem_biUnion.mp hi_in_bU

/-- Recovered-candidate analogue of
`mem_T_iff_exists_irreducibleFactor_representingSubset_of_scaledRecombinationCandidate_of_primitive_pos_lc_core_of_bound`. -/
private theorem mem_T_iff_exists_irreducibleFactor_representingSubset_of_liftedRecoveryCandidate_of_bound
    {core target quotient : Hex.ZPoly} {d : Hex.LiftData}
    {J T : LiftedFactorSubset d}
    (B' : Nat)
    (hcore_lc_le : (Hex.DensePoly.leadingCoeff core).natAbs ≤ B')
    (hvalid : ∀ g : Hex.ZPoly,
      HexPolyZMathlib.toPolynomial g ∈
        UniqueFactorizationMonoid.normalizedFactors
          (HexPolyZMathlib.toPolynomial
            (liftedRecoveryCandidate core d T)) →
      ∀ i, (g.coeff i).natAbs ≤ B')
    (hcore_ne : core ≠ 0)
    (hcore_primitive : Hex.ZPoly.Primitive core)
    (hcore_lc_pos : 0 < Hex.DensePoly.leadingCoeff core)
    (hd_liftedFactor_monic :
      ∀ i, Hex.DensePoly.Monic (liftedFactor d i))
    (hd_liftedFactor_natDegree_pos :
      ∀ i, 0 < (HexPolyZMathlib.toPolynomial (liftedFactor d i)).natDegree)
    (hprecision : 2 * B' < d.p ^ d.k)
    (hpartition : LiftedFactorSubsetPartition core d J target)
    (htarget_dvd_core : target ∣ core)
    (hTJ : T ⊆ J)
    (hrecord :
      Hex.shouldRecordPolynomialFactor
          (liftedRecoveryCandidate core d T) = true)
    (hquot :
      Hex.exactQuotient? target (liftedRecoveryCandidate core d T) =
        some quotient)
    {i : LiftedFactorIndex d} (hi : i ∈ T) :
    ∃ (g : Hex.ZPoly) (S_g : LiftedFactorSubset d),
      Irreducible (HexPolyZMathlib.toPolynomial g) ∧
      g ∣ liftedRecoveryCandidate core d T ∧
      RepresentsIntegerFactorAtLift core d g S_g ∧
      S_g ⊆ J ∧ i ∈ S_g := by
  have hcand_poly_ne_zero :
      HexPolyZMathlib.toPolynomial (liftedRecoveryCandidate core d T) ≠ 0 :=
    (toPolynomial_ne_zero_and_not_isUnit_of_shouldRecord hrecord).1
  have hcand_ne : liftedRecoveryCandidate core d T ≠ 0 := by
    intro h
    apply hcand_poly_ne_zero
    rw [h]
    exact HexPolyMathlib.toPolynomial_zero
  have hcand_squarefree :
      Squarefree
        (HexPolyZMathlib.toPolynomial (liftedRecoveryCandidate core d T)) :=
    toPolynomial_liftedRecoveryCandidate_squarefree hpartition hquot
  set normFactors :=
    UniqueFactorizationMonoid.normalizedFactors
      (HexPolyZMathlib.toPolynomial (liftedRecoveryCandidate core d T))
    with hnf_def
  have hnf_nodup : normFactors.Nodup :=
    (UniqueFactorizationMonoid.squarefree_iff_nodup_normalizedFactors
      hcand_poly_ne_zero).mp hcand_squarefree
  have hcand_normFix :
      Hex.normalizeFactorSign (liftedRecoveryCandidate core d T) =
        liftedRecoveryCandidate core d T :=
    normalizeFactorSign_liftedRecoveryCandidate_eq T
  have hcand_normalize_eq :
      normalize
          (HexPolyZMathlib.toPolynomial
            (liftedRecoveryCandidate core d T)) =
        HexPolyZMathlib.toPolynomial (liftedRecoveryCandidate core d T) :=
    normalize_toPolynomial_of_normalizeFactorSign_id hcand_ne hcand_normFix
  have hnf_prod_eq :
      normFactors.prod =
        HexPolyZMathlib.toPolynomial (liftedRecoveryCandidate core d T) := by
    rw [UniqueFactorizationMonoid.prod_normalizedFactors_eq hcand_poly_ne_zero,
      hcand_normalize_eq]
  have bridge_for : ∀ g : Hex.ZPoly,
      HexPolyZMathlib.toPolynomial g ∈ normFactors →
      ∃ S_g : LiftedFactorSubset d,
        Irreducible (HexPolyZMathlib.toPolynomial g) ∧
        g ∣ target ∧
        g ∣ liftedRecoveryCandidate core d T ∧
        RepresentsIntegerFactorAtLift core d g S_g ∧
        S_g ⊆ J ∧
        S_g ⊆ T ∧
        Hex.ZPoly.content g = 1 ∧
        Hex.normalizeFactorSign g = g := by
    intro g hgPoly
    obtain ⟨g', S_g, h_eq, h_irr, h_dvd_t, h_dvd_c, h_rep, h_SJ, h_ST,
        h_cont, h_norm⟩ :=
      exists_representingSubset_of_mem_normalizedFactors_liftedRecoveryCandidate_of_bound
        B' hvalid hcore_lc_le hcore_ne hcore_primitive hcore_lc_pos
        hd_liftedFactor_monic hprecision hpartition htarget_dvd_core hTJ
        hrecord hquot hgPoly
    have hg_eq : g' = g := by
      have := congrArg HexPolyZMathlib.ofPolynomial h_eq
      simpa [HexPolyZMathlib.ofPolynomial_toPolynomial] using this
    refine ⟨S_g, ?_, ?_, ?_, ?_, h_SJ, h_ST, ?_, ?_⟩
    · rw [← hg_eq]; exact h_irr
    · rw [← hg_eq]; exact h_dvd_t
    · rw [← hg_eq]; exact h_dvd_c
    · rw [← hg_eq]; exact h_rep
    · rw [← hg_eq]; exact h_cont
    · rw [← hg_eq]; exact h_norm
  let S_of : Hex.ZPoly → LiftedFactorSubset d := fun g =>
    if h : HexPolyZMathlib.toPolynomial g ∈ normFactors then
      Classical.choose (bridge_for g h)
    else (∅ : LiftedFactorSubset d)
  let gs : Finset Hex.ZPoly :=
    normFactors.toFinset.image HexPolyZMathlib.ofPolynomial
  have mem_gs : ∀ {g : Hex.ZPoly},
      g ∈ gs ↔ HexPolyZMathlib.toPolynomial g ∈ normFactors := by
    intro g
    refine ⟨?_, ?_⟩
    · intro hg
      rcases Finset.mem_image.mp hg with ⟨gPoly, hgPoly_mem, h_eq⟩
      rw [Multiset.mem_toFinset] at hgPoly_mem
      rw [← h_eq, HexPolyZMathlib.toPolynomial_ofPolynomial]
      exact hgPoly_mem
    · intro hg
      refine Finset.mem_image.mpr ⟨HexPolyZMathlib.toPolynomial g, ?_, ?_⟩
      · exact Multiset.mem_toFinset.mpr hg
      · exact HexPolyZMathlib.ofPolynomial_toPolynomial g
  have h_each : ∀ g ∈ gs,
      Irreducible (HexPolyZMathlib.toPolynomial g) ∧
      g ∣ target ∧
      g ∣ liftedRecoveryCandidate core d T ∧
      RepresentsIntegerFactorAtLift core d g (S_of g) ∧
      S_of g ⊆ J ∧
      S_of g ⊆ T ∧
      Hex.ZPoly.content g = 1 ∧
      Hex.normalizeFactorSign g = g := by
    intro g hg
    have hg_norm := mem_gs.mp hg
    have hS_of_eq :
        S_of g = Classical.choose (bridge_for g hg_norm) := by
      simp [S_of, dif_pos hg_norm]
    have hspec := Classical.choose_spec (bridge_for g hg_norm)
    rw [hS_of_eq]
    exact hspec
  have h_pairwise : ∀ ⦃g h : Hex.ZPoly⦄, g ∈ gs → h ∈ gs → g ≠ h →
      ¬ Associated (HexPolyZMathlib.toPolynomial g)
        (HexPolyZMathlib.toPolynomial h) := by
    intro g h hg_in hh_in hgh hassoc
    have hg_norm := mem_gs.mp hg_in
    have hh_norm := mem_gs.mp hh_in
    have hg_eq :
        normalize (HexPolyZMathlib.toPolynomial g) =
          HexPolyZMathlib.toPolynomial g :=
      UniqueFactorizationMonoid.normalize_normalized_factor _ hg_norm
    have hh_eq :
        normalize (HexPolyZMathlib.toPolynomial h) =
          HexPolyZMathlib.toPolynomial h :=
      UniqueFactorizationMonoid.normalize_normalized_factor _ hh_norm
    have hpoly_eq :
        HexPolyZMathlib.toPolynomial g = HexPolyZMathlib.toPolynomial h := by
      rw [← hg_eq, ← hh_eq]
      exact normalize_eq_normalize hassoc.dvd hassoc.symm.dvd
    apply hgh
    have := congrArg HexPolyZMathlib.ofPolynomial hpoly_eq
    simpa [HexPolyZMathlib.ofPolynomial_toPolynomial] using this
  have h_degree_total :
      (HexPolyZMathlib.toPolynomial
          (liftedRecoveryCandidate core d T)).natDegree =
        ∑ g ∈ gs, (HexPolyZMathlib.toPolynomial g).natDegree := by
    have h_image_sum :
        ∑ g ∈ gs, (HexPolyZMathlib.toPolynomial g).natDegree =
          ∑ gPoly ∈ normFactors.toFinset, gPoly.natDegree := by
      show ∑ g ∈ normFactors.toFinset.image HexPolyZMathlib.ofPolynomial,
          (HexPolyZMathlib.toPolynomial g).natDegree =
        ∑ gPoly ∈ normFactors.toFinset, gPoly.natDegree
      rw [Finset.sum_image]
      · refine Finset.sum_congr rfl ?_
        intro gPoly _
        simp
      · intro a _ b _ heq
        have := congrArg HexPolyZMathlib.toPolynomial heq
        simpa using this
    have h_toFinset_sum :
        ∑ gPoly ∈ normFactors.toFinset, gPoly.natDegree =
          (normFactors.map Polynomial.natDegree).sum := by
      change (normFactors.toFinset.val.map Polynomial.natDegree).sum =
        (normFactors.map Polynomial.natDegree).sum
      rw [Multiset.toFinset_val, hnf_nodup.dedup]
    rw [h_image_sum, h_toFinset_sum, ← hnf_prod_eq,
      Polynomial.natDegree_multiset_prod _
        (UniqueFactorizationMonoid.zero_notMem_normalizedFactors _)]
  obtain ⟨g, hg_in_gs, hi_in_Sg⟩ :=
    exists_mem_representedSubset_of_degree_cover_of_liftedRecoveryCandidate_of_bound
      B' hcore_ne hcore_primitive hcore_lc_pos hcore_lc_le
      hd_liftedFactor_monic hd_liftedFactor_natDegree_pos hprecision hpartition
      htarget_dvd_core hTJ gs S_of h_each
      (fun g hg => hvalid g (mem_gs.mp hg))
      h_pairwise h_degree_total hi
  have _hg_norm := mem_gs.mp hg_in_gs
  obtain ⟨h_irr, _, h_dvd_c, h_rep, h_SJ, _, _, _⟩ := h_each g hg_in_gs
  exact ⟨g, S_of g, h_irr, h_dvd_c, h_rep, h_SJ, hi_in_Sg⟩

/-- Recovered-candidate cover-at-min: from a recordable recovered candidate with
an exact quotient against `target`, the minimum index of `T` lies in a
represented subset of an irreducible divisor whose subset is contained in `T`. -/
private theorem coverAtMin_representingSubset_subset_of_liftedRecoveryCandidate_dvd_of_bound
    {core target quotient : Hex.ZPoly} {d : Hex.LiftData}
    {J T : LiftedFactorSubset d}
    (B' : Nat)
    (hcore_lc_le : (Hex.DensePoly.leadingCoeff core).natAbs ≤ B')
    (hvalid : ∀ g : Hex.ZPoly,
      HexPolyZMathlib.toPolynomial g ∈
        UniqueFactorizationMonoid.normalizedFactors
          (HexPolyZMathlib.toPolynomial
            (liftedRecoveryCandidate core d T)) →
      ∀ i, (g.coeff i).natAbs ≤ B')
    (hcore_ne : core ≠ 0)
    (hcore_primitive : Hex.ZPoly.Primitive core)
    (hcore_lc_pos : 0 < Hex.DensePoly.leadingCoeff core)
    (hd_liftedFactor_monic :
      ∀ i, Hex.DensePoly.Monic (liftedFactor d i))
    (hd_liftedFactor_natDegree_pos :
      ∀ i, 0 < (HexPolyZMathlib.toPolynomial (liftedFactor d i)).natDegree)
    (hprecision : 2 * B' < d.p ^ d.k)
    (hpartition : LiftedFactorSubsetPartition core d J target)
    (htarget_dvd_core : target ∣ core)
    (hTJ : T ⊆ J)
    (hne : J.Nonempty)
    (hmin_in_T : J.min' hne ∈ T)
    (hrecord :
      Hex.shouldRecordPolynomialFactor
          (liftedRecoveryCandidate core d T) = true)
    (hquot :
      Hex.exactQuotient? target (liftedRecoveryCandidate core d T) =
        some quotient) :
    ∃ (f : Hex.ZPoly) (S : LiftedFactorSubset d),
      Irreducible (HexPolyZMathlib.toPolynomial f) ∧
      f ∣ target ∧
      S ⊆ J ∧ J.min' hne ∈ S ∧
      RepresentsIntegerFactorAtLift core d f S ∧
      S ⊆ T := by
  obtain ⟨f, S, hf_irr, hf_dvd_cand, hf_rep, hSJ, hiS⟩ :=
    mem_T_iff_exists_irreducibleFactor_representingSubset_of_liftedRecoveryCandidate_of_bound
      B' hcore_lc_le hvalid hcore_ne hcore_primitive hcore_lc_pos
      hd_liftedFactor_monic hd_liftedFactor_natDegree_pos hprecision hpartition
      htarget_dvd_core hTJ hrecord hquot hmin_in_T
  have hcand_dvd_target : liftedRecoveryCandidate core d T ∣ target := by
    have hmul : quotient * liftedRecoveryCandidate core d T = target :=
      Hex.exactQuotient?_product hquot
    refine ⟨quotient, ?_⟩
    rw [Hex.DensePoly.mul_comm_poly (S := Int)]
    exact hmul.symm
  have hf_dvd_target : f ∣ target := zpoly_dvd_trans hf_dvd_cand hcand_dvd_target
  have hf_content : Hex.ZPoly.content f = 1 := by
    have hf_poly_primitive : (HexPolyZMathlib.toPolynomial f).IsPrimitive := by
      have hcand_primitive : Hex.ZPoly.Primitive
          (liftedRecoveryCandidate core d T) :=
        zpoly_primitive_liftedRecoveryCandidate_of_bound
          B' hcore_lc_pos hcore_lc_le hd_liftedFactor_monic hprecision T
      have hcand_poly_primitive :
          (HexPolyZMathlib.toPolynomial
            (liftedRecoveryCandidate core d T)).IsPrimitive :=
        toPolynomial_isPrimitive_of_zpoly_primitive_basic hcand_primitive
      exact isPrimitive_of_dvd hcand_poly_primitive
        (HexPolyMathlib.toPolynomial_dvd hf_dvd_cand)
    exact zpoly_primitive_of_toPolynomial_isPrimitive_basic hf_poly_primitive
  have hf_norm_sign : Hex.normalizeFactorSign f = f := by
    obtain ⟨hf_primitive, hf_lc_pos⟩ :=
      representsIntegerFactorAtLift_primitive_of_bound
        B' hcore_lc_le hcore_ne hcore_primitive hcore_lc_pos
        hd_liftedFactor_monic hpartition hf_irr hf_dvd_target htarget_dvd_core
        hSJ hf_rep hprecision
    unfold Hex.normalizeFactorSign
    have hnot : ¬ Hex.DensePoly.leadingCoeff f < 0 := by omega
    rw [if_neg hnot]
  -- A coefficient bound on `f` from a normalised factor of the candidate
  -- associated to `f` (the unit witness is `C c` with `|c| = 1`).
  have hvalid_f : ∀ i, (f.coeff i).natAbs ≤ B' := by
    have hf_poly_dvd :
        HexPolyZMathlib.toPolynomial f ∣
          HexPolyZMathlib.toPolynomial (liftedRecoveryCandidate core d T) :=
      HexPolyMathlib.toPolynomial_dvd hf_dvd_cand
    have hcand_poly_ne_zero :
        HexPolyZMathlib.toPolynomial (liftedRecoveryCandidate core d T) ≠ 0 :=
      (toPolynomial_ne_zero_and_not_isUnit_of_shouldRecord hrecord).1
    obtain ⟨gPoly, hg_mem, hg_assoc⟩ :=
      UniqueFactorizationMonoid.exists_mem_normalizedFactors_of_dvd
        hcand_poly_ne_zero hf_irr hf_poly_dvd
    let g : Hex.ZPoly := HexPolyZMathlib.ofPolynomial gPoly
    have hg_toPoly : HexPolyZMathlib.toPolynomial g = gPoly :=
      HexPolyZMathlib.toPolynomial_ofPolynomial gPoly
    have hg_bound : ∀ i, (g.coeff i).natAbs ≤ B' :=
      hvalid g (by rw [hg_toPoly]; exact hg_mem)
    obtain ⟨u, hu⟩ := hg_assoc
    obtain ⟨c, hc_unit, hcu⟩ := Polynomial.isUnit_iff.mp u.isUnit
    have hc_abs_one : c.natAbs = 1 := Int.isUnit_iff_natAbs_eq.mp hc_unit
    intro i
    have hg_coeff : g.coeff i = gPoly.coeff i := by
      have := HexPolyZMathlib.coeff_toPolynomial g i
      rw [hg_toPoly] at this
      exact this.symm
    have hgPoly_coeff_f : gPoly.coeff i = f.coeff i * c := by
      have hmul : (HexPolyZMathlib.toPolynomial f * Polynomial.C c).coeff i =
          (HexPolyZMathlib.toPolynomial f).coeff i * c :=
        Polynomial.coeff_mul_C _ _ _
      rw [← hu, ← hcu, hmul, HexPolyZMathlib.coeff_toPolynomial]
    have hbound := hg_bound i
    rw [hg_coeff, hgPoly_coeff_f, Int.natAbs_mul, hc_abs_one, Nat.mul_one] at hbound
    exact hbound
  have hST : S ⊆ T :=
    representingSubset_subset_of_dvd_liftedRecoveryCandidate_of_primitive_pos_lc_core_of_bound
      B' hvalid_f
      hcore_ne hcore_primitive hcore_lc_pos hprecision htarget_dvd_core
      hpartition hTJ hf_irr hf_dvd_target hf_content hf_norm_sign hf_dvd_cand
      hSJ hf_rep
  exact ⟨f, S, hf_irr, hf_dvd_target, hSJ, hiS, hf_rep, hST⟩

/-- Executable scaled-search prefix-none surface in the recovered/dilate
coordinate.  The inline candidate matches `liftedRecoveryCandidate`, the
candidate shape used by `Hex.scaledRecombinationSearchModAux`. -/
theorem RecoveredScaledSearch.prefixNone_of_bound
    {core target factor : Hex.ZPoly} {d : Hex.LiftData}
    {J S : LiftedFactorSubset d} {localFactors : List Hex.ZPoly}
    {fuel : Nat}
    {pre suffix : List (List Hex.ZPoly × List Hex.ZPoly)}
    (B' : Nat)
    (hcore_lc_le : (Hex.DensePoly.leadingCoeff core).natAbs ≤ B')
    (hvalid : ∀ g : Hex.ZPoly, g ∣ core → ∀ i, (g.coeff i).natAbs ≤ B')
    (hcore_ne : core ≠ 0)
    (hcore_primitive : Hex.ZPoly.Primitive core)
    (hcore_lc_pos : 0 < Hex.DensePoly.leadingCoeff core)
    (hd_liftedFactor_monic :
      ∀ i, Hex.DensePoly.Monic (liftedFactor d i))
    (hd_liftedFactor_natDegree_pos :
      ∀ i, 0 < (HexPolyZMathlib.toPolynomial (liftedFactor d i)).natDegree)
    (hprecision : 2 * B' < d.p ^ d.k)
    (htarget_dvd_core : target ∣ core)
    (hpartition : LiftedFactorSubsetPartition core d J target)
    (hmatches : LiftedFactorListMatches d J localFactors)
    (hlocal_nodup : localFactors.Nodup)
    (hfactor_irr : Irreducible (HexPolyZMathlib.toPolynomial factor))
    (hfactor_dvd_target : factor ∣ target)
    (hSrep : RepresentsIntegerFactorAtLift core d factor S)
    (hSJ : S ⊆ J) (hne : J.Nonempty) (hmin : J.min' hne ∈ S)
    (hsplits :
      Hex.subsetSplitsWithFirst localFactors =
        pre ++
          (liftedSubsetSelectedList d S,
           liftedSubsetSelectedList d (J \ S)) :: suffix) :
    ∀ split ∈ pre,
      (let candidate' :=
        Hex.normalizeFactorSign <|
          Hex.ZPoly.primitivePart <|
            Hex.ZPoly.dilate (Hex.DensePoly.leadingCoeff core)
              (Hex.centeredLiftPoly
                (Array.polyProduct split.1.toArray)
                (d.p ^ d.k))
      if Hex.shouldRecordPolynomialFactor candidate' then
        match Hex.exactQuotient? target candidate' with
        | none => none
        | some quotient' =>
            match Hex.scaledRecombinationSearchModAux
                (Hex.DensePoly.leadingCoeff core)
                quotient' (d.p ^ d.k) split.2 fuel with
            | none => none
            | some r => some (candidate' :: r)
      else none) = none := by
  intro split hsplit
  obtain ⟨T, hTJ, hmin_in_T, hsplit_eq, i, _hi_J, hi_S, hi_notT⟩ :=
    liftedSubsetSplit_prefix_exists_mem_sdiff_of_matches
      hlocal_nodup hmatches hSJ hne hmin hsplits hsplit
  subst hsplit_eq
  -- Identify the inline dilate candidate with `liftedRecoveryCandidate core d T`.
  simp only [polyProduct_liftedSubsetSelectedList_eq_liftedFactorProduct]
  show (if Hex.shouldRecordPolynomialFactor (liftedRecoveryCandidate core d T) then
      match Hex.exactQuotient? target (liftedRecoveryCandidate core d T) with
      | none => none
      | some quotient' =>
          match Hex.scaledRecombinationSearchModAux
              (Hex.DensePoly.leadingCoeff core)
              quotient' (d.p ^ d.k)
              (liftedSubsetSelectedList d (J \ T)) fuel with
          | none => none
          | some r => some (liftedRecoveryCandidate core d T :: r)
      else none) = none
  by_cases hrec :
      Hex.shouldRecordPolynomialFactor (liftedRecoveryCandidate core d T) = true
  · rw [if_pos hrec]
    cases hquot :
        Hex.exactQuotient? target (liftedRecoveryCandidate core d T) with
    | none => rfl
    | some quotient' =>
      exfalso
      have hcand_dvd_target :
          liftedRecoveryCandidate core d T ∣ target := by
        have hmul :
            quotient' * liftedRecoveryCandidate core d T = target :=
          Hex.exactQuotient?_product hquot
        refine ⟨quotient', ?_⟩
        rw [Hex.DensePoly.mul_comm_poly (S := Int)]
        exact hmul.symm
      have hcand_dvd_core :
          liftedRecoveryCandidate core d T ∣ core :=
        zpoly_dvd_trans hcand_dvd_target htarget_dvd_core
      have hvalid'_T : ∀ g : Hex.ZPoly,
          HexPolyZMathlib.toPolynomial g ∈
            UniqueFactorizationMonoid.normalizedFactors
              (HexPolyZMathlib.toPolynomial
                (liftedRecoveryCandidate core d T)) →
          ∀ i, (g.coeff i).natAbs ≤ B' := by
        intro g hg_mem
        have hg_poly_dvd : HexPolyZMathlib.toPolynomial g ∣
            HexPolyZMathlib.toPolynomial
              (liftedRecoveryCandidate core d T) :=
          UniqueFactorizationMonoid.dvd_of_mem_normalizedFactors hg_mem
        have hg_dvd_cand : g ∣ liftedRecoveryCandidate core d T := by
          rcases hg_poly_dvd with ⟨r, hr⟩
          refine ⟨HexPolyZMathlib.ofPolynomial r, ?_⟩
          apply HexPolyZMathlib.equiv.injective
          simp only [HexPolyZMathlib.equiv_apply, HexPolyZMathlib.toPolynomial_mul,
            HexPolyZMathlib.toPolynomial_ofPolynomial]
          exact hr
        have hg_dvd_core : g ∣ core :=
          zpoly_dvd_trans hg_dvd_cand hcand_dvd_core
        exact hvalid g hg_dvd_core
      obtain ⟨f_cov, S_cov, hf_cov_irr, hf_cov_dvd_target, hS_cov_J,
              hmin_in_S_cov, hS_cov_rep, hS_cov_T⟩ :=
        coverAtMin_representingSubset_subset_of_liftedRecoveryCandidate_dvd_of_bound
          B' hcore_lc_le hvalid'_T
          hcore_ne hcore_primitive hcore_lc_pos hd_liftedFactor_monic
          hd_liftedFactor_natDegree_pos hprecision hpartition
          htarget_dvd_core hTJ hne hmin_in_T hrec hquot
      have hnot_disjoint : ¬ Disjoint S S_cov := fun hdisj =>
        Finset.disjoint_left.mp hdisj hmin hmin_in_S_cov
      have hassoc :
          Associated (HexPolyZMathlib.toPolynomial factor)
            (HexPolyZMathlib.toPolynomial f_cov) := by
        by_contra hnot_assoc
        exact hnot_disjoint
          (hpartition.pairwise_disjoint
            hfactor_irr hfactor_dvd_target hSJ hSrep
            hf_cov_irr hf_cov_dvd_target hS_cov_J hS_cov_rep hnot_assoc)
      have hSeq : S = S_cov :=
        hpartition.unique_up_to_associated
          hfactor_irr hfactor_dvd_target hSJ hSrep
          hf_cov_irr hf_cov_dvd_target hS_cov_J hS_cov_rep hassoc
      have hi_S_cov : i ∈ S_cov := hSeq ▸ hi_S
      exact hi_notT (hS_cov_T hi_S_cov)
  · rw [if_neg hrec]


/-- Algorithm-side packaging for the BHKS fast-core success branch in
the form needed by UFD arguments over `Polynomial ℤ`.  Combines the
existing product, divisibility, and `shouldRecord` invariants exposed
in `HexBerlekampZassenhaus` with the `toPolynomial` map.
The remaining count-equality hypothesis is the open obligation of
#4022 — once supplied, this lemma feeds directly into
`HexBerlekampZassenhausMathlib.UFDPartition.irreducible_of_partition_card_eq_normalizedFactors_card`. -/
theorem bhksRecoveryCoreWithBound_some_factor_irreducible_of_count
    {core : Hex.ZPoly} {B : Nat} {primeData : Hex.PrimeChoiceData}
    {k fuel : Nat} {coreFactors : Array Hex.ZPoly}
    (hcore_ne : core ≠ 0)
    (h : Hex.bhksRecoveryCoreWithBound core B primeData k fuel = some coreFactors)
    (hcount :
      (coreFactors.toList.map HexPolyZMathlib.toPolynomial).length =
        (UniqueFactorizationMonoid.normalizedFactors
          (HexPolyZMathlib.toPolynomial core)).card) :
    ∀ factor ∈ coreFactors.toList,
      Irreducible (HexPolyZMathlib.toPolynomial factor) := by
  set f := HexPolyZMathlib.toPolynomial core with hf_def
  have hf_ne : f ≠ 0 := by
    intro hzero
    apply hcore_ne
    apply HexPolyZMathlib.equiv.injective
    simpa using hzero
  set gs : List (Polynomial ℤ) :=
    coreFactors.toList.map HexPolyZMathlib.toPolynomial with hgs_def
  have hprod : Associated gs.prod f := by
    have hp_core : Array.polyProduct coreFactors = core :=
      Hex.bhksRecoveryCoreWithBound_product core B primeData k fuel coreFactors h
    have hp_poly :
        (coreFactors.toList.map HexPolyZMathlib.toPolynomial).prod =
          HexPolyZMathlib.toPolynomial core := by
      rw [← polyProduct_toPolynomial, hp_core]
    rw [hgs_def, hp_poly, hf_def]
  have hdvd_all :
      ∀ factor ∈ coreFactors.toList, factor ∣ core :=
    Hex.bhksRecoveryCoreWithBound_some_dvd core B primeData k fuel coreFactors h
  have hrecord_all :
      ∀ factor ∈ coreFactors.toList,
        Hex.shouldRecordPolynomialFactor factor = true :=
    Hex.bhksRecoveryCoreWithBound_some_shouldRecord h
  have hne_all : ∀ g ∈ gs, g ≠ 0 := by
    intro g hg
    rw [hgs_def, List.mem_map] at hg
    obtain ⟨factor, hfactor_mem, hg_eq⟩ := hg
    rw [← hg_eq]
    exact
      (toPolynomial_ne_zero_and_not_isUnit_of_shouldRecord
        (hrecord_all factor hfactor_mem)).1
  have hnonunit_all : ∀ g ∈ gs, ¬ IsUnit g := by
    intro g hg
    rw [hgs_def, List.mem_map] at hg
    obtain ⟨factor, hfactor_mem, hg_eq⟩ := hg
    rw [← hg_eq]
    exact
      (toPolynomial_ne_zero_and_not_isUnit_of_shouldRecord
        (hrecord_all factor hfactor_mem)).2
  intro factor hfactor_mem
  have hpolyfactor_mem :
      HexPolyZMathlib.toPolynomial factor ∈ gs := by
    rw [hgs_def, List.mem_map]
    exact ⟨factor, hfactor_mem, rfl⟩
  exact
      HexBerlekampZassenhausMathlib.UFDPartition.irreducible_of_partition_card_eq_normalizedFactors_card
      hf_ne gs hne_all hnonunit_all hprod hcount _ hpolyfactor_mem

/-- Upper cardinality bound for a successful BHKS fast-core branch.

The emitted factor list consists of non-zero non-units whose product is
associated to `core`, so the abstract UFD partition bound applies after
transporting the executable factors to `Polynomial ℤ`. -/
theorem bhksRecoveryCoreWithBound_some_factor_count_le
    {core : Hex.ZPoly} {B : Nat} {primeData : Hex.PrimeChoiceData}
    {k fuel : Nat} {coreFactors : Array Hex.ZPoly}
    (hcore_ne : core ≠ 0)
    (h : Hex.bhksRecoveryCoreWithBound core B primeData k fuel = some coreFactors) :
    (coreFactors.toList.map HexPolyZMathlib.toPolynomial).length ≤
      (UniqueFactorizationMonoid.normalizedFactors
        (HexPolyZMathlib.toPolynomial core)).card := by
  set f := HexPolyZMathlib.toPolynomial core with hf_def
  have hf_ne : f ≠ 0 := by
    intro hzero
    apply hcore_ne
    apply HexPolyZMathlib.equiv.injective
    simpa using hzero
  set gs : List (Polynomial ℤ) :=
    coreFactors.toList.map HexPolyZMathlib.toPolynomial with hgs_def
  have hprod : Associated gs.prod f := by
    have hp_core : Array.polyProduct coreFactors = core :=
      Hex.bhksRecoveryCoreWithBound_product core B primeData k fuel coreFactors h
    have hp_poly :
        (coreFactors.toList.map HexPolyZMathlib.toPolynomial).prod =
          HexPolyZMathlib.toPolynomial core := by
      rw [← polyProduct_toPolynomial, hp_core]
    rw [hgs_def, hp_poly, hf_def]
  have hrecord_all :
      ∀ factor ∈ coreFactors.toList,
        Hex.shouldRecordPolynomialFactor factor = true :=
    Hex.bhksRecoveryCoreWithBound_some_shouldRecord h
  have hne_all : ∀ g ∈ gs, g ≠ 0 := by
    intro g hg
    rw [hgs_def, List.mem_map] at hg
    obtain ⟨factor, hfactor_mem, hg_eq⟩ := hg
    rw [← hg_eq]
    exact
      (toPolynomial_ne_zero_and_not_isUnit_of_shouldRecord
        (hrecord_all factor hfactor_mem)).1
  have hnonunit_all : ∀ g ∈ gs, ¬ IsUnit g := by
    intro g hg
    rw [hgs_def, List.mem_map] at hg
    obtain ⟨factor, hfactor_mem, hg_eq⟩ := hg
    rw [← hg_eq]
    exact
      (toPolynomial_ne_zero_and_not_isUnit_of_shouldRecord
        (hrecord_all factor hfactor_mem)).2
  exact
    HexBerlekampZassenhausMathlib.UFDPartition.length_le_normalizedFactors_card
      hf_ne gs hne_all hnonunit_all hprod

/-- Lower cardinality bound for a successful BHKS fast-core branch whose
emitted candidates have already been certified irreducible.

The remaining BHKS/B8 work is to derive the `hirr` hypothesis from the
equivalence-class partition-refinement argument for the concrete success
state.  Once supplied, the abstract UFD partition theorem gives the reverse
count inequality needed to pair with
`bhksRecoveryCoreWithBound_some_factor_count_le`. -/
theorem bhksRecoveryCoreWithBound_some_factor_count_ge_of_irreducible
    {core : Hex.ZPoly} {B : Nat} {primeData : Hex.PrimeChoiceData}
    {k fuel : Nat} {coreFactors : Array Hex.ZPoly}
    (h : Hex.bhksRecoveryCoreWithBound core B primeData k fuel = some coreFactors)
    (hirr :
      ∀ factor ∈ coreFactors.toList,
        Irreducible (HexPolyZMathlib.toPolynomial factor)) :
    (UniqueFactorizationMonoid.normalizedFactors
      (HexPolyZMathlib.toPolynomial core)).card ≤
        (coreFactors.toList.map HexPolyZMathlib.toPolynomial).length := by
  set f := HexPolyZMathlib.toPolynomial core with hf_def
  set gs : List (Polynomial ℤ) :=
    coreFactors.toList.map HexPolyZMathlib.toPolynomial with hgs_def
  have hprod : Associated gs.prod f := by
    have hp_core : Array.polyProduct coreFactors = core :=
      Hex.bhksRecoveryCoreWithBound_product core B primeData k fuel coreFactors h
    have hp_poly :
        (coreFactors.toList.map HexPolyZMathlib.toPolynomial).prod =
          HexPolyZMathlib.toPolynomial core := by
      rw [← polyProduct_toPolynomial, hp_core]
    rw [hgs_def, hp_poly, hf_def]
  have hirr_gs : ∀ g ∈ gs, Irreducible g := by
    intro g hg
    rw [hgs_def, List.mem_map] at hg
    obtain ⟨factor, hfactor_mem, hg_eq⟩ := hg
    rw [← hg_eq]
    exact hirr factor hfactor_mem
  exact
    HexBerlekampZassenhausMathlib.UFDPartition.normalizedFactors_card_le_length_of_irreducible_partition
      gs hirr_gs hprod

/-- Cardinality equality for a successful BHKS fast-core branch once the
BHKS/B8 proof has certified every emitted candidate irreducible. -/
theorem bhksRecoveryCoreWithBound_some_factor_count_eq_of_irreducible
    {core : Hex.ZPoly} {B : Nat} {primeData : Hex.PrimeChoiceData}
    {k fuel : Nat} {coreFactors : Array Hex.ZPoly}
    (hcore_ne : core ≠ 0)
    (h : Hex.bhksRecoveryCoreWithBound core B primeData k fuel = some coreFactors)
    (hirr :
      ∀ factor ∈ coreFactors.toList,
        Irreducible (HexPolyZMathlib.toPolynomial factor)) :
    (coreFactors.toList.map HexPolyZMathlib.toPolynomial).length =
      (UniqueFactorizationMonoid.normalizedFactors
        (HexPolyZMathlib.toPolynomial core)).card := by
  apply le_antisymm
  · exact bhksRecoveryCoreWithBound_some_factor_count_le hcore_ne h
  · exact bhksRecoveryCoreWithBound_some_factor_count_ge_of_irreducible h hirr

/-- Branch-local fast-core success irreducibility, expressed in the Mathlib-free
`Hex.ZPoly.Irreducible` predicate. This is the `Hex.ZPoly` transport of
`bhksRecoveryCoreWithBound_some_factor_irreducible_of_count`, obtained by
composing that scaffold with the existing
`Hex.ZPoly.Irreducible_iff_polynomialIrreducible` equivalence.

The remaining count-equality hypothesis is the residual #4030 obligation; once
supplied, this lemma yields fast-core branch irreducibility directly in the
executable `Hex.ZPoly` form needed by callers that do not import Mathlib's
`Polynomial` model. -/
theorem bhksRecoveryCoreWithBound_some_factor_zpolyIrreducible_of_count
    {core : Hex.ZPoly} {B : Nat} {primeData : Hex.PrimeChoiceData}
    {k fuel : Nat} {coreFactors : Array Hex.ZPoly}
    (hcore_ne : core ≠ 0)
    (h : Hex.bhksRecoveryCoreWithBound core B primeData k fuel = some coreFactors)
    (hcount :
      (coreFactors.toList.map HexPolyZMathlib.toPolynomial).length =
        (UniqueFactorizationMonoid.normalizedFactors
          (HexPolyZMathlib.toPolynomial core)).card) :
    ∀ factor ∈ coreFactors.toList, Hex.ZPoly.Irreducible factor := by
  intro factor hfactor_mem
  exact
    (Hex.ZPoly.Irreducible_iff_polynomialIrreducible factor).mpr
      (bhksRecoveryCoreWithBound_some_factor_irreducible_of_count
        hcore_ne h hcount factor hfactor_mem)

/--
Abstract-bound variant of
`recombinationSearchModAux_some_and_covers_of_liftedFactorSubsetPartition`:
the concrete `2 * defaultFactorCoeffBound core < d.p ^ d.k` Mignotte
precision is replaced by `2 * B' < d.p ^ d.k` against an abstract bound
`B'`, paired with the universal divisor coefficient bound
`∀ g ∣ core, ∀ i, (g.coeff i).natAbs ≤ B'`. The `B'`/`hvalid`/`hprecision`
abstract-bound hypotheses remain load-bearing at the empty-`J` step
(`not_represents_empty_of_irreducible_dvd_core_of_bound`, specialised by
`hvalid g hg_dvd_core`) and the prefix-none discharge
(`liftedFactorSubsetPartition_prefix_none_of_bound`, receiving the
universal `hvalid` and `B'` unchanged). At the cover-at-min recovery the
partition equality `LiftedFactorSubsetPartition.recombinationCandidate_eq`
pins `f_cov` to `recombinationCandidate d S_cov`; `recombinationCandidate_monic`
supplies monicness and `natDegree_toPolynomial_recombinationCandidate_eq_sum`
the natDegree positivity, so those three points consume the sound partition
evidence rather than the old scaled-product recovery lemmas. In the recursive
IH call, the outer abstract-bound hypotheses are captured by closure.
-/
private theorem recombinationSearchModAux_some_and_covers_of_liftedFactorSubsetPartition_of_bound
    {core : Hex.ZPoly} {d : Hex.LiftData}
    (B' : Nat)
    (hvalid : ∀ g : Hex.ZPoly, g ∣ core → ∀ i, (g.coeff i).natAbs ≤ B')
    (hcore_ne : core ≠ 0)
    (hcore_monic : Hex.DensePoly.Monic core)
    (hd_modulus : 2 ≤ d.p ^ d.k)
    (hd_liftedFactor_monic :
      ∀ i, Hex.DensePoly.Monic (liftedFactor d i))
    (hd_liftedFactor_natDegree_pos :
      ∀ i, 0 < (HexPolyZMathlib.toPolynomial (liftedFactor d i)).natDegree)
    (hd_liftedFactor_inj : Function.Injective (liftedFactor d))
    (hprecision : 2 * B' < d.p ^ d.k) :
    ∀ {target : Hex.ZPoly} {J : LiftedFactorSubset d}
      {localFactors : List Hex.ZPoly} {fuel : Nat},
      Hex.DensePoly.Monic target →
      target ∣ core →
      LiftedFactorSubsetPartition core d J target →
      LiftedFactorListMatches d J localFactors →
      J.card < fuel →
      ∃ result,
        Hex.recombinationSearchModAux target (d.p ^ d.k) localFactors fuel =
          some result ∧
        ∀ factor : Hex.ZPoly,
          Irreducible (HexPolyZMathlib.toPolynomial factor) →
          factor ∣ target →
          ∃ emitted ∈ result,
            Associated (HexPolyZMathlib.toPolynomial emitted)
              (HexPolyZMathlib.toPolynomial factor) := by
  intro target J localFactors fuel htarget_monic htarget_dvd_core hpartition
    hmatches hfuel
  induction fuel generalizing target J localFactors with
  | zero => omega
  | succ fuel' ih =>
    by_cases htarget_eq_one : target = 1
    · -- `target = 1` branch: the executable returns `some []` directly, and the
      -- universal claim is vacuous because no irreducible divides `1`.
      subst htarget_eq_one
      refine ⟨[], ?_, ?_⟩
      · show Hex.recombinationSearchModAux 1 (d.p ^ d.k) localFactors (fuel' + 1) =
          some []
        unfold Hex.recombinationSearchModAux
        simp
      · intro factor hirr hdvd
        exfalso
        have hfactor_dvd_one_poly :
            HexPolyZMathlib.toPolynomial factor ∣ (1 : Polynomial ℤ) := by
          rw [show (1 : Polynomial ℤ) = HexPolyZMathlib.toPolynomial 1 from
            toPolynomial_one_zpoly.symm]
          exact HexPolyMathlib.toPolynomial_dvd hdvd
        exact hirr.not_isUnit (isUnit_of_dvd_one hfactor_dvd_one_poly)
    · -- `target ≠ 1` branch: derive `J` nonempty, then descend through the
      -- `cover_at_min`-emitted irreducible factor `f_cov`.
      have htarget_poly_monic :
          (HexPolyZMathlib.toPolynomial target).Monic := by
        show (HexPolyZMathlib.toPolynomial target).leadingCoeff = 1
        rw [HexPolyMathlib.leadingCoeff_toPolynomial]
        exact htarget_monic
      -- Step 1: `J` is nonempty (else the partition produces a representing
      -- subset `S ⊆ ∅` for an irreducible divisor of `target`, contradicting
      -- `not_represents_empty_of_irreducible_dvd_core_of_bound`).
      have hJ_ne : J.Nonempty := by
        by_contra hJ_empty
        rw [Finset.not_nonempty_iff_eq_empty] at hJ_empty
        have htarget_poly_ne_one :
            HexPolyZMathlib.toPolynomial target ≠ 1 := by
          intro h
          apply htarget_eq_one
          apply HexPolyZMathlib.equiv.injective
          show HexPolyZMathlib.toPolynomial target =
            HexPolyZMathlib.toPolynomial 1
          rw [toPolynomial_one_zpoly]
          exact h
        have htarget_poly_nonunit :
            ¬ IsUnit (HexPolyZMathlib.toPolynomial target) := by
          intro hunit
          exact htarget_poly_ne_one
            (htarget_poly_monic.eq_one_of_isUnit hunit)
        have htarget_poly_ne :
            HexPolyZMathlib.toPolynomial target ≠ 0 :=
          htarget_poly_monic.ne_zero
        obtain ⟨g, hg_irr_toPoly, hg_dvd_target, hg_norm_sign⟩ :=
          exists_signNormalized_irreducible_factor htarget_poly_nonunit
            htarget_poly_ne
        obtain ⟨S, hSJ, hSrep⟩ :=
          hpartition.exists_subset hg_norm_sign hg_irr_toPoly hg_dvd_target
        have hS_empty : S = ∅ := by
          rw [hJ_empty] at hSJ
          exact Finset.subset_empty.mp hSJ
        have hg_dvd_core : g ∣ core :=
          zpoly_dvd_trans hg_dvd_target htarget_dvd_core
        apply not_represents_empty_of_irreducible_dvd_core_of_bound
          B' (hvalid g hg_dvd_core) hcore_ne hcore_monic hd_modulus
          hpartition hg_dvd_target hg_irr_toPoly hprecision
        rw [← hS_empty]; exact hSrep
      -- Step 2: cover-at-min produces an irreducible divisor `f_cov` of `target`
      -- whose representing subset `S_cov` contains `J.min'`.
      obtain ⟨f_cov, S_cov, hf_cov_irr, hf_cov_dvd_target, hS_cov_J,
              hmin_in_S_cov, hS_cov_rep⟩ :=
        hpartition.cover_at_min hJ_ne
      -- The partition pins `f_cov` to its executable recombination candidate,
      -- which is monic on a monic core (`recombinationCandidate_monic`).
      have hrec_eq : recombinationCandidate d S_cov = f_cov :=
        hpartition.recombinationCandidate_eq hcore_monic hf_cov_irr
          hf_cov_dvd_target hS_cov_J hS_cov_rep
      have hf_cov_monic : Hex.DensePoly.Monic f_cov :=
        hrec_eq ▸ recombinationCandidate_monic hd_modulus hd_liftedFactor_monic S_cov
      -- Step 3: `f_cov` has positive natDegree (sum over `S_cov` nonempty).
      have hf_cov_natDeg_pos :
          0 < (HexPolyZMathlib.toPolynomial f_cov).natDegree := by
        rw [← hrec_eq,
          natDegree_toPolynomial_recombinationCandidate_eq_sum
            hd_modulus hd_liftedFactor_monic S_cov]
        apply Finset.sum_pos (fun i _ => hd_liftedFactor_natDegree_pos i)
        exact ⟨J.min' hJ_ne, hmin_in_S_cov⟩
      have hf_cov_degree_pos : 0 < f_cov.degree?.getD 0 := by
        rw [← HexPolyMathlib.natDegree_toPolynomial]
        exact hf_cov_natDeg_pos
      -- Step 4: exact-quotient equation `quotient * f_cov = target`.
      obtain ⟨quotient, hquot, hmul⟩ :=
        exactQuotient?_recombinationCandidate_eq_some_of_eq_factor
          hrec_eq hf_cov_monic hf_cov_degree_pos hf_cov_dvd_target
      have hquot_eq : quotient * f_cov = target := hrec_eq ▸ hmul
      have hquot_poly_eq :
          HexPolyZMathlib.toPolynomial quotient *
              HexPolyZMathlib.toPolynomial f_cov =
            HexPolyZMathlib.toPolynomial target := by
        rw [← HexPolyZMathlib.toPolynomial_mul, hquot_eq]
      -- Step 5: `quotient` is monic and divides `core`.
      have hquot_dvd_target : quotient ∣ target :=
        ⟨f_cov, hquot_eq.symm⟩
      have hquot_dvd_core : quotient ∣ core :=
        zpoly_dvd_trans hquot_dvd_target htarget_dvd_core
      have hf_cov_poly_monic :
          (HexPolyZMathlib.toPolynomial f_cov).Monic := by
        show (HexPolyZMathlib.toPolynomial f_cov).leadingCoeff = 1
        rw [HexPolyMathlib.leadingCoeff_toPolynomial]
        exact hf_cov_monic
      have hquot_monic : Hex.DensePoly.Monic quotient := by
        have hquot_poly_monic :
            (HexPolyZMathlib.toPolynomial quotient).Monic :=
          hf_cov_poly_monic.of_mul_monic_right (hquot_poly_eq ▸ htarget_poly_monic)
        show Hex.DensePoly.leadingCoeff quotient = (1 : Int)
        rw [← HexPolyMathlib.leadingCoeff_toPolynomial]
        exact hquot_poly_monic
      -- Step 6: partition transport and matches transport for the recursive call.
      have hpartition_new :
          LiftedFactorSubsetPartition core d (J \ S_cov) quotient :=
        liftedFactorSubsetPartition_transport hpartition hquot_eq hS_cov_rep
          hS_cov_J hf_cov_irr hf_cov_dvd_target
      have hmatches_new :
          LiftedFactorListMatches d (J \ S_cov)
            (liftedSubsetSelectedList d (J \ S_cov)) :=
        LiftedFactorListMatches.sdiff_of_subset
      -- Step 7: fuel decrement is valid because `(J \ S_cov).card < J.card`
      -- (since `J.min' ∈ S_cov ⊆ J`, so `J \ S_cov` is a strict subset of `J`).
      have hcard_new : (J \ S_cov).card < fuel' := by
        have hmin_not_in_sdiff : J.min' hJ_ne ∉ J \ S_cov := by
          intro h
          exact (Finset.mem_sdiff.mp h).2 hmin_in_S_cov
        have hsub_strict : J \ S_cov ⊂ J := by
          refine ⟨Finset.sdiff_subset, fun hsub => hmin_not_in_sdiff ?_⟩
          exact hsub (J.min'_mem hJ_ne)
        have : (J \ S_cov).card < J.card := Finset.card_lt_card hsub_strict
        omega
      -- Step 8: apply the IH to obtain the recursive search success and the
      -- universal coverage for divisors of `quotient`.
      obtain ⟨restFactors, hrest, hrest_covers⟩ :=
        ih hquot_monic hquot_dvd_core hpartition_new hmatches_new hcard_new
      -- Step 9: decompose the canonical split membership into prefix and suffix.
      have hsplit_mem :
          (liftedSubsetSelectedList d S_cov,
              liftedSubsetSelectedList d (J \ S_cov)) ∈
            Hex.subsetSplitsWithFirst localFactors :=
        liftedSubsetSplit_mem_subsetSplitsWithFirst_of_matches
          hmatches hS_cov_J hJ_ne hmin_in_S_cov
      obtain ⟨pre, suffix, hsplits⟩ := List.append_of_mem hsplit_mem
      -- Step 10: prefix-none discharge.
      have hlocal_nodup : localFactors.Nodup :=
        hmatches.nodup_of_injOn hd_liftedFactor_inj.injOn
      have hprefix :=
        liftedFactorSubsetPartition_prefix_none_of_bound
          B' hvalid hcore_ne hcore_monic hd_modulus
          hd_liftedFactor_monic hd_liftedFactor_natDegree_pos hprecision
          htarget_dvd_core hpartition hmatches hlocal_nodup hf_cov_irr
          hf_cov_dvd_target hS_cov_rep hS_cov_J hJ_ne hmin_in_S_cov hsplits
          (fuel := fuel')
      -- Step 11: assemble the executable step result via
      -- `recombinationSearchModAux_eq_some_of_step_of_prefix_none`.
      have hrecord :
          Hex.shouldRecordPolynomialFactor (recombinationCandidate d S_cov) =
            true := by
        rw [hrec_eq]
        exact shouldRecordPolynomialFactor_of_irreducible_toPolynomial hf_cov_irr
      have hsearch_step :
          Hex.recombinationSearchModAux target (d.p ^ d.k) localFactors
              (fuel' + 1) =
            some (recombinationCandidate d S_cov :: restFactors) :=
        Hex.recombinationSearchModAux_eq_some_of_step_of_prefix_none
          (target := target)
          (candidate := recombinationCandidate d S_cov)
          (quotient := quotient)
          (modulus := d.p ^ d.k)
          (localFactors := localFactors)
          (selected := liftedSubsetSelectedList d S_cov)
          (rest := liftedSubsetSelectedList d (J \ S_cov))
          (restFactors := restFactors)
          (pre := pre)
          (suffix := suffix)
          (fuel := fuel')
          htarget_eq_one hsplits hprefix rfl hrecord hquot hrest
      refine ⟨recombinationCandidate d S_cov :: restFactors, hsearch_step, ?_⟩
      -- Step 12: universal coverage. Case-split on whether `factor` is
      -- associated to `f_cov`.
      intro factor hfactor_irr hfactor_dvd_target
      by_cases hassoc :
          Associated (HexPolyZMathlib.toPolynomial factor)
            (HexPolyZMathlib.toPolynomial f_cov)
      · -- Case A: `factor ~ f_cov`. Emitted witness is `f_cov` itself.
        refine ⟨recombinationCandidate d S_cov, by simp, ?_⟩
        rw [hrec_eq]
        exact hassoc.symm
      · -- Case B: `factor ≁ f_cov`. Then `factor ∣ quotient` (UFD splitting on
        -- `factor ∣ quotient * f_cov`, with the `factor ∣ f_cov` branch ruled
        -- out by the not-associated hypothesis).
        have hfactor_dvd_quotient : factor ∣ quotient := by
          have hfactor_poly_dvd_target :
              HexPolyZMathlib.toPolynomial factor ∣
                HexPolyZMathlib.toPolynomial target :=
            HexPolyMathlib.toPolynomial_dvd hfactor_dvd_target
          have hfactor_poly_prime :
              Prime (HexPolyZMathlib.toPolynomial factor) :=
            UniqueFactorizationMonoid.irreducible_iff_prime.mp hfactor_irr
          have hfactor_poly_dvd_prod :
              HexPolyZMathlib.toPolynomial factor ∣
                HexPolyZMathlib.toPolynomial quotient *
                  HexPolyZMathlib.toPolynomial f_cov := by
            rw [hquot_poly_eq]; exact hfactor_poly_dvd_target
          rcases hfactor_poly_prime.dvd_or_dvd hfactor_poly_dvd_prod with
            hdvd_quot_poly | hdvd_fcov_poly
          · -- `toPolynomial factor ∣ toPolynomial quotient`. Pull back via
            -- `ofPolynomial`.
            rcases hdvd_quot_poly with ⟨r, hr⟩
            refine ⟨HexPolyZMathlib.ofPolynomial r, ?_⟩
            apply HexPolyZMathlib.equiv.injective
            simp only [HexPolyZMathlib.equiv_apply,
              HexPolyZMathlib.toPolynomial_mul,
              HexPolyZMathlib.toPolynomial_ofPolynomial]
            exact hr
          · -- `toPolynomial factor ∣ toPolynomial f_cov` and both irreducible
            -- gives `Associated`, contradicting `hassoc`.
            exact absurd (hfactor_irr.associated_of_dvd hf_cov_irr hdvd_fcov_poly)
              hassoc
        obtain ⟨emitted, hemitted_mem, hemitted_assoc⟩ :=
          hrest_covers factor hfactor_irr hfactor_dvd_quotient
        exact ⟨emitted, List.mem_cons_of_mem _ hemitted_mem, hemitted_assoc⟩

/--
Universal-quantifier auxiliary for the recursive coverage capstone (#4301):
under a `LiftedFactorSubsetPartition core d J target` rest-state predicate,
`Hex.recombinationSearchModAux` returns `some result` and **every**
irreducible integer divisor of `target` is associated to some emitted
candidate in `result`.

The deliverable theorem
`recombinationSearchModAux_some_factor_associated_of_liftedFactorSubsetPartition`
specialises this universal statement to a fixed `factor` hypothesis.

Proof outline (induction on `fuel`):
* `fuel = 0`: `J.card < 0` is impossible.
* `fuel = fuel' + 1`:
  - If `J = ∅`: the partition's inherited `exists_subset` forces every
    irreducible divisor of `target` to be represented by `∅`, contradicting
    `not_represents_empty_of_irreducible_dvd_core`. Therefore `target` has
    no irreducible divisors; combined with `target` monic and
    `target ∣ core`, this gives `target = 1` and the executable returns
    `some []`. The universal claim is vacuous (no irreducibles divide 1).
  - If `J` is nonempty: `LiftedFactorSubsetPartition.cover_at_min` provides
    an irreducible divisor `f_cov` of `target` whose representing subset
    `S_cov` contains `J.min'`. The recovery theorem
    `recombinationCandidate_eq_factor_of_recovery_of_monic_core` identifies
    `recombinationCandidate d S_cov = f_cov`; the executable split membership
    comes from `liftedSubsetSplit_mem_subsetSplitsWithFirst_of_matches`;
    the prefix-none obligation is discharged by
    `liftedFactorSubsetPartition_prefix_none` (with nodup from
    `LiftedFactorListMatches.nodup_of_injOn`); the partition transports via
    `liftedFactorSubsetPartition_transport` and matches via
    `LiftedFactorListMatches.sdiff_of_subset`. The inductive hypothesis on
    `(quotient, J \ S_cov)` then both supplies the recursive-rest success
    witness and covers every irreducible divisor of `quotient`. For an
    arbitrary irreducible `factor ∣ target`, the partition's
    `pairwise_disjoint` (contrapositive via the shared `S_cov` ownership of
    `J.min'`) and `unique_up_to_associated` fields decide whether
    `factor` is associated to `f_cov` (in which case `f_cov` itself is the
    emitted witness) or `factor ∣ quotient` (in which case the inductive
    hypothesis supplies the witness in the recursive tail).

This is the `defaultFactorCoeffBound core`-instantiated thin wrapper for
`recombinationSearchModAux_some_and_covers_of_liftedFactorSubsetPartition_of_bound`:
the universal coefficient bound for `g ∣ core` is discharged by
`defaultFactorCoeffBound_valid` itself.
-/
private theorem recombinationSearchModAux_some_and_covers_of_liftedFactorSubsetPartition
    {core : Hex.ZPoly} {d : Hex.LiftData}
    (hcore_ne : core ≠ 0)
    (hcore_monic : Hex.DensePoly.Monic core)
    (hd_modulus : 2 ≤ d.p ^ d.k)
    (hd_liftedFactor_monic :
      ∀ i, Hex.DensePoly.Monic (liftedFactor d i))
    (hd_liftedFactor_natDegree_pos :
      ∀ i, 0 < (HexPolyZMathlib.toPolynomial (liftedFactor d i)).natDegree)
    (hd_liftedFactor_inj : Function.Injective (liftedFactor d))
    (hprecision : 2 * Hex.ZPoly.defaultFactorCoeffBound core < d.p ^ d.k) :
    ∀ {target : Hex.ZPoly} {J : LiftedFactorSubset d}
      {localFactors : List Hex.ZPoly} {fuel : Nat},
      Hex.DensePoly.Monic target →
      target ∣ core →
      LiftedFactorSubsetPartition core d J target →
      LiftedFactorListMatches d J localFactors →
      J.card < fuel →
      ∃ result,
        Hex.recombinationSearchModAux target (d.p ^ d.k) localFactors fuel =
          some result ∧
        ∀ factor : Hex.ZPoly,
          Irreducible (HexPolyZMathlib.toPolynomial factor) →
          factor ∣ target →
          ∃ emitted ∈ result,
            Associated (HexPolyZMathlib.toPolynomial emitted)
              (HexPolyZMathlib.toPolynomial factor) := by
  intro target J localFactors fuel htarget_monic htarget_dvd_core hpartition
    hmatches hfuel
  exact recombinationSearchModAux_some_and_covers_of_liftedFactorSubsetPartition_of_bound
    (Hex.ZPoly.defaultFactorCoeffBound core)
    (defaultFactorCoeffBound_valid core hcore_ne)
    hcore_ne hcore_monic hd_modulus hd_liftedFactor_monic
    hd_liftedFactor_natDegree_pos hd_liftedFactor_inj hprecision
    htarget_monic htarget_dvd_core hpartition hmatches hfuel

/--
Abstract-bound variant of
`scaledRecombinationSearchModAux_some_and_covers_of_liftedFactorSubsetPartition`:
the concrete `2 * defaultFactorCoeffBound core < d.p ^ d.k` Mignotte
precision is replaced by `2 * B' < d.p ^ d.k` against an abstract bound
`B'`, paired with the leading-coefficient bound on `core` and the
universal divisor coefficient bound `∀ g ∣ core, ∀ i, (g.coeff i).natAbs
≤ B'`.  This is the reusable coverage theorem for the executable scaled
search in the recovered/dilate coordinate; the recursive step records
`liftedRecoveryCandidate` and discharges its prefix obligation via
`RecoveredScaledSearch.prefixNone_of_bound`.
-/
theorem RecoveredScaledSearch.covers_of_bound
    {core : Hex.ZPoly} {d : Hex.LiftData}
    (B' : Nat)
    (hcore_lc_le : (Hex.DensePoly.leadingCoeff core).natAbs ≤ B')
    (hvalid : ∀ g : Hex.ZPoly, g ∣ core → ∀ i, (g.coeff i).natAbs ≤ B')
    (hcore_ne : core ≠ 0)
    (hcore_primitive : Hex.ZPoly.Primitive core)
    (hcore_lc_pos : 0 < Hex.DensePoly.leadingCoeff core)
    (hd_modulus : 2 ≤ d.p ^ d.k)
    (hd_liftedFactor_monic :
      ∀ i, Hex.DensePoly.Monic (liftedFactor d i))
    (hd_liftedFactor_natDegree_pos :
      ∀ i, 0 < (HexPolyZMathlib.toPolynomial (liftedFactor d i)).natDegree)
    (hd_liftedFactor_inj : Function.Injective (liftedFactor d))
    (hprecision : 2 * B' < d.p ^ d.k) :
    ∀ {target : Hex.ZPoly} {J : LiftedFactorSubset d}
      {localFactors : List Hex.ZPoly} {fuel : Nat},
      Hex.ZPoly.Primitive target →
      0 < Hex.DensePoly.leadingCoeff target →
      target ∣ core →
      LiftedFactorSubsetPartition core d J target →
      LiftedFactorListMatches d J localFactors →
      J.card < fuel →
      ∃ result,
        Hex.scaledRecombinationSearchModAux (Hex.DensePoly.leadingCoeff core)
            target (d.p ^ d.k) localFactors fuel =
          some result ∧
        ∀ factor : Hex.ZPoly,
          Irreducible (HexPolyZMathlib.toPolynomial factor) →
          factor ∣ target →
          ∃ emitted ∈ result,
            Associated (HexPolyZMathlib.toPolynomial emitted)
              (HexPolyZMathlib.toPolynomial factor) := by
  intro target J localFactors fuel htarget_primitive htarget_lc_pos
    htarget_dvd_core hpartition hmatches hfuel
  induction fuel generalizing target J localFactors with
  | zero => omega
  | succ fuel' ih =>
    by_cases htarget_eq_one : target = 1
    · subst htarget_eq_one
      refine ⟨[], ?_, ?_⟩
      · show Hex.scaledRecombinationSearchModAux
            (Hex.DensePoly.leadingCoeff core) 1 (d.p ^ d.k)
            localFactors (fuel' + 1) = some []
        unfold Hex.scaledRecombinationSearchModAux
        simp
      · intro factor hirr hdvd
        exfalso
        have hfactor_dvd_one_poly :
            HexPolyZMathlib.toPolynomial factor ∣ (1 : Polynomial ℤ) := by
          rw [show (1 : Polynomial ℤ) = HexPolyZMathlib.toPolynomial 1 from
            toPolynomial_one_zpoly.symm]
          exact HexPolyMathlib.toPolynomial_dvd hdvd
        exact hirr.not_isUnit (isUnit_of_dvd_one hfactor_dvd_one_poly)
    · have htarget_poly_ne_one :
          HexPolyZMathlib.toPolynomial target ≠ 1 := by
        intro h
        apply htarget_eq_one
        apply HexPolyZMathlib.equiv.injective
        show HexPolyZMathlib.toPolynomial target =
          HexPolyZMathlib.toPolynomial 1
        rw [toPolynomial_one_zpoly]
        exact h
      have htarget_poly_nonunit :
          ¬ IsUnit (HexPolyZMathlib.toPolynomial target) := by
        intro hunit
        exact htarget_eq_one
          (zpoly_eq_one_of_toPolynomial_isUnit_of_pos_lc htarget_lc_pos hunit)
      have htarget_poly_ne :
          HexPolyZMathlib.toPolynomial target ≠ 0 := by
        intro hzero
        apply zpoly_ne_zero_of_pos_lc htarget_lc_pos
        apply HexPolyZMathlib.equiv.injective
        show HexPolyZMathlib.toPolynomial target =
          HexPolyZMathlib.toPolynomial 0
        rw [HexPolyZMathlib.toPolynomial_zero]
        exact hzero
      have hJ_ne : J.Nonempty := by
        by_contra hJ_empty
        rw [Finset.not_nonempty_iff_eq_empty] at hJ_empty
        obtain ⟨g, hg_irr_toPoly, hg_dvd_target, hg_norm_sign⟩ :=
          exists_signNormalized_irreducible_factor htarget_poly_nonunit
            htarget_poly_ne
        obtain ⟨S, hSJ, hSrep⟩ :=
          hpartition.exists_subset hg_norm_sign hg_irr_toPoly hg_dvd_target
        have hS_empty : S = ∅ := by
          rw [hJ_empty] at hSJ
          exact Finset.subset_empty.mp hSJ
        have hg_dvd_core : g ∣ core :=
          zpoly_dvd_trans hg_dvd_target htarget_dvd_core
        apply not_represents_empty_of_irreducible_dvd_core_of_primitive_pos_lc_core_of_bound
          B' (hvalid g hg_dvd_core) hcore_ne hcore_primitive hcore_lc_pos
          hcore_lc_le hd_modulus hpartition hg_dvd_target hg_irr_toPoly hprecision
        rw [← hS_empty]; exact hSrep
      obtain ⟨f_cov, S_cov, hf_cov_irr, hf_cov_dvd_target, hS_cov_J,
              hmin_in_S_cov, hS_cov_rep⟩ :=
        hpartition.cover_at_min hJ_ne
      have hf_cov_dvd_core : f_cov ∣ core :=
        zpoly_dvd_trans hf_cov_dvd_target htarget_dvd_core
      -- The partition pins `f_cov` to its sound recovered candidate.
      have hrec_eq : liftedRecoveryCandidate core d S_cov = f_cov :=
        hpartition.liftedRecoveryCandidate_eq hf_cov_irr hf_cov_dvd_target
          hS_cov_J hS_cov_rep
      obtain ⟨hf_cov_primitive, hf_cov_lc_pos⟩ :=
        representsIntegerFactorAtLift_primitive_of_bound
          B' hcore_lc_le hcore_ne
          hcore_primitive hcore_lc_pos hd_liftedFactor_monic
          hpartition hf_cov_irr hf_cov_dvd_target htarget_dvd_core hS_cov_J
          hS_cov_rep hprecision
      have hf_cov_natDeg_pos :
          0 < (HexPolyZMathlib.toPolynomial f_cov).natDegree := by
        rw [← hrec_eq,
          natDegree_toPolynomial_liftedRecoveryCandidate_eq_sum_of_bound
            B' hcore_lc_pos hcore_lc_le hd_liftedFactor_monic hprecision S_cov]
        apply Finset.sum_pos (fun i _ => hd_liftedFactor_natDegree_pos i)
        exact ⟨J.min' hJ_ne, hmin_in_S_cov⟩
      have hf_cov_degree_pos : 0 < f_cov.degree?.getD 0 := by
        rw [← HexPolyMathlib.natDegree_toPolynomial]
        exact hf_cov_natDeg_pos
      obtain ⟨quotient, hquot, hmul⟩ :=
        exactQuotient?_liftedRecoveryCandidate_eq_some_of_eq_factor_of_primitive_pos_lc
          hrec_eq hf_cov_lc_pos hf_cov_degree_pos hf_cov_dvd_target
      have hquot_eq : quotient * f_cov = target := hrec_eq ▸ hmul
      have hquot_poly_eq :
          HexPolyZMathlib.toPolynomial quotient *
              HexPolyZMathlib.toPolynomial f_cov =
            HexPolyZMathlib.toPolynomial target := by
        rw [← HexPolyZMathlib.toPolynomial_mul, hquot_eq]
      have hquot_dvd_target : quotient ∣ target :=
        ⟨f_cov, hquot_eq.symm⟩
      have hquot_dvd_core : quotient ∣ core :=
        zpoly_dvd_trans hquot_dvd_target htarget_dvd_core
      have hquot_primitive : Hex.ZPoly.Primitive quotient :=
        zpoly_primitive_of_dvd_primitive_basic htarget_primitive hquot_dvd_target
      have hquot_lc_pos : 0 < Hex.DensePoly.leadingCoeff quotient :=
        zpoly_left_pos_lc_of_mul_eq_of_pos_lc hquot_eq hf_cov_lc_pos
          htarget_lc_pos
      have hpartition_new :
          LiftedFactorSubsetPartition core d (J \ S_cov) quotient :=
        liftedFactorSubsetPartition_transport hpartition hquot_eq hS_cov_rep
          hS_cov_J hf_cov_irr hf_cov_dvd_target
      have hmatches_new :
          LiftedFactorListMatches d (J \ S_cov)
            (liftedSubsetSelectedList d (J \ S_cov)) :=
        LiftedFactorListMatches.sdiff_of_subset
      have hcard_new : (J \ S_cov).card < fuel' := by
        have hmin_not_in_sdiff : J.min' hJ_ne ∉ J \ S_cov := by
          intro h
          exact (Finset.mem_sdiff.mp h).2 hmin_in_S_cov
        have hsub_strict : J \ S_cov ⊂ J := by
          refine ⟨Finset.sdiff_subset, fun hsub => hmin_not_in_sdiff ?_⟩
          exact hsub (J.min'_mem hJ_ne)
        have : (J \ S_cov).card < J.card := Finset.card_lt_card hsub_strict
        omega
      obtain ⟨restFactors, hrest, hrest_covers⟩ :=
        ih hquot_primitive hquot_lc_pos hquot_dvd_core hpartition_new
          hmatches_new hcard_new
      have hsplit_mem :
          (liftedSubsetSelectedList d S_cov,
              liftedSubsetSelectedList d (J \ S_cov)) ∈
            Hex.subsetSplitsWithFirst localFactors :=
        liftedSubsetSplit_mem_subsetSplitsWithFirst_of_matches
          hmatches hS_cov_J hJ_ne hmin_in_S_cov
      obtain ⟨pre, suffix, hsplits⟩ := List.append_of_mem hsplit_mem
      have hlocal_nodup : localFactors.Nodup :=
        hmatches.nodup_of_injOn hd_liftedFactor_inj.injOn
      have hprefix :=
        RecoveredScaledSearch.prefixNone_of_bound
          B' hcore_lc_le hvalid hcore_ne hcore_primitive hcore_lc_pos
          hd_liftedFactor_monic hd_liftedFactor_natDegree_pos
          hprecision htarget_dvd_core hpartition hmatches hlocal_nodup
          hf_cov_irr hf_cov_dvd_target hS_cov_rep hS_cov_J hJ_ne
          hmin_in_S_cov hsplits (fuel := fuel')
      have hrecord :
          Hex.shouldRecordPolynomialFactor
              (liftedRecoveryCandidate core d S_cov) =
            true :=
        shouldRecord_liftedRecoveryCandidate_of_eq_factor
          hrec_eq hf_cov_irr
      have hcandidate_def :
          liftedRecoveryCandidate core d S_cov =
            Hex.normalizeFactorSign
              (Hex.ZPoly.primitivePart
                (Hex.ZPoly.dilate (Hex.DensePoly.leadingCoeff core)
                  (Hex.centeredLiftPoly
                    (Array.polyProduct
                      (liftedSubsetSelectedList d S_cov).toArray)
                    (d.p ^ d.k)))) := by
        unfold liftedRecoveryCandidate
        rw [polyProduct_liftedSubsetSelectedList_eq_liftedFactorProduct]
      have hsearch_step :
          Hex.scaledRecombinationSearchModAux (Hex.DensePoly.leadingCoeff core)
              target (d.p ^ d.k) localFactors (fuel' + 1) =
            some (liftedRecoveryCandidate core d S_cov :: restFactors) :=
        Hex.scaledRecombinationSearchModAux_eq_some_of_step_of_prefix_none
          (target := target)
          (candidate := liftedRecoveryCandidate core d S_cov)
          (quotient := quotient)
          (modulus := d.p ^ d.k)
          (localFactors := localFactors)
          (selected := liftedSubsetSelectedList d S_cov)
          (rest := liftedSubsetSelectedList d (J \ S_cov))
          (restFactors := restFactors)
          (pre := pre)
          (suffix := suffix)
          (fuel := fuel')
          htarget_eq_one hsplits hprefix hcandidate_def hrecord hquot hrest
      refine ⟨liftedRecoveryCandidate core d S_cov :: restFactors,
        hsearch_step, ?_⟩
      intro factor hfactor_irr hfactor_dvd_target
      by_cases hassoc :
          Associated (HexPolyZMathlib.toPolynomial factor)
            (HexPolyZMathlib.toPolynomial f_cov)
      · refine ⟨liftedRecoveryCandidate core d S_cov, by simp, ?_⟩
        rw [hrec_eq]
        exact hassoc.symm
      · have hfactor_dvd_quotient : factor ∣ quotient := by
          have hfactor_poly_dvd_target :
              HexPolyZMathlib.toPolynomial factor ∣
                HexPolyZMathlib.toPolynomial target :=
            HexPolyMathlib.toPolynomial_dvd hfactor_dvd_target
          have hfactor_poly_prime :
              Prime (HexPolyZMathlib.toPolynomial factor) :=
            UniqueFactorizationMonoid.irreducible_iff_prime.mp hfactor_irr
          have hfactor_poly_dvd_prod :
              HexPolyZMathlib.toPolynomial factor ∣
                HexPolyZMathlib.toPolynomial quotient *
                  HexPolyZMathlib.toPolynomial f_cov := by
            rw [hquot_poly_eq]; exact hfactor_poly_dvd_target
          rcases hfactor_poly_prime.dvd_or_dvd hfactor_poly_dvd_prod with
            hdvd_quot_poly | hdvd_fcov_poly
          · rcases hdvd_quot_poly with ⟨r, hr⟩
            refine ⟨HexPolyZMathlib.ofPolynomial r, ?_⟩
            apply HexPolyZMathlib.equiv.injective
            simp only [HexPolyZMathlib.equiv_apply,
              HexPolyZMathlib.toPolynomial_mul,
              HexPolyZMathlib.toPolynomial_ofPolynomial]
            exact hr
          · exact absurd (hfactor_irr.associated_of_dvd hf_cov_irr hdvd_fcov_poly)
              hassoc
        obtain ⟨emitted, hemitted_mem, hemitted_assoc⟩ :=
          hrest_covers factor hfactor_irr hfactor_dvd_quotient
        exact ⟨emitted, List.mem_cons_of_mem _ hemitted_mem, hemitted_assoc⟩

/--
Primitive + positive-leading analogue of
`recombinationSearchModAux_some_and_covers_of_liftedFactorSubsetPartition`.

This is the recovered/dilate coverage auxiliary for primitive non-monic cores:
the executable step is `Hex.scaledRecombinationSearchModAux`, candidates are
identified as `liftedRecoveryCandidate`, and the recursive target invariant is
`Hex.ZPoly.Primitive target` plus positive leading coefficient instead of
monicity.

Thin wrapper over
`RecoveredScaledSearch.covers_of_bound`
that instantiates `B' := Hex.ZPoly.defaultFactorCoeffBound core` and
discharges the abstract bound hypotheses via `defaultFactorCoeffBound_valid`
paired with `leadingCoeff_eq_coeff_last`.
-/
theorem RecoveredScaledSearch.covers
    {core : Hex.ZPoly} {d : Hex.LiftData}
    (hcore_ne : core ≠ 0)
    (hcore_primitive : Hex.ZPoly.Primitive core)
    (hcore_lc_pos : 0 < Hex.DensePoly.leadingCoeff core)
    (hd_modulus : 2 ≤ d.p ^ d.k)
    (hd_liftedFactor_monic :
      ∀ i, Hex.DensePoly.Monic (liftedFactor d i))
    (hd_liftedFactor_natDegree_pos :
      ∀ i, 0 < (HexPolyZMathlib.toPolynomial (liftedFactor d i)).natDegree)
    (hd_liftedFactor_inj : Function.Injective (liftedFactor d))
    (hprecision : 2 * Hex.ZPoly.defaultFactorCoeffBound core < d.p ^ d.k) :
    ∀ {target : Hex.ZPoly} {J : LiftedFactorSubset d}
      {localFactors : List Hex.ZPoly} {fuel : Nat},
      Hex.ZPoly.Primitive target →
      0 < Hex.DensePoly.leadingCoeff target →
      target ∣ core →
      LiftedFactorSubsetPartition core d J target →
      LiftedFactorListMatches d J localFactors →
      J.card < fuel →
      ∃ result,
        Hex.scaledRecombinationSearchModAux (Hex.DensePoly.leadingCoeff core)
            target (d.p ^ d.k) localFactors fuel =
          some result ∧
        ∀ factor : Hex.ZPoly,
          Irreducible (HexPolyZMathlib.toPolynomial factor) →
          factor ∣ target →
          ∃ emitted ∈ result,
            Associated (HexPolyZMathlib.toPolynomial emitted)
              (HexPolyZMathlib.toPolynomial factor) := by
  intro target J localFactors fuel htarget_primitive htarget_lc_pos
    htarget_dvd_core hpartition hmatches hfuel
  have hcore_lc_le := defaultFactorCoeffBound_leadingCoeff_natAbs_le hcore_ne
  exact RecoveredScaledSearch.covers_of_bound
    (Hex.ZPoly.defaultFactorCoeffBound core)
    hcore_lc_le
    (defaultFactorCoeffBound_valid core hcore_ne)
    hcore_ne hcore_primitive hcore_lc_pos hd_modulus hd_liftedFactor_monic
    hd_liftedFactor_natDegree_pos hd_liftedFactor_inj hprecision
    htarget_primitive htarget_lc_pos htarget_dvd_core hpartition hmatches hfuel

end

end HexBerlekampZassenhausMathlib
