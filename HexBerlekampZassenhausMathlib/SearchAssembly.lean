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

public import HexBerlekampZassenhausMathlib.SmartSearchCoverage
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
import all HexBerlekampZassenhausMathlib.ScaledSearchCoverage
import all HexBerlekampZassenhausMathlib.SmartSearchCoverage

public section
set_option backward.proofsInPublic true
set_option backward.privateInPublic true

/-!
This module collects the associated-factor lemmas and `choosePrimeData` partition assembly.
-/

namespace HexBerlekampZassenhausMathlib

noncomputable section

open Polynomial

/-- Coverage + squarefreeness ⇒ each emitted factor is irreducible.  When the
recorded `result` multiplies back to a square-free `core` and every irreducible
factor of `core` is an associate of some emitted factor, the emitted list has
exactly `normalizedFactors.card` entries (coverage gives `≥`, the product gives
`≤`), so each entry is irreducible by the UFD partition lemma. -/
theorem smartCore_factor_irreducible_of_covers_of_squarefree
    {core : Hex.ZPoly} {result : List Hex.ZPoly}
    (hcore_ne : core ≠ 0)
    (hsqfree : Squarefree (HexPolyZMathlib.toPolynomial core))
    (hprod : Array.polyProduct result.toArray = core)
    (hrecord : ∀ g ∈ result, Hex.shouldRecordPolynomialFactor g = true)
    (hcover : ∀ factor : Hex.ZPoly,
      Irreducible (HexPolyZMathlib.toPolynomial factor) → factor ∣ core →
      ∃ emitted ∈ result, Associated (HexPolyZMathlib.toPolynomial emitted)
        (HexPolyZMathlib.toPolynomial factor)) :
    ∀ g ∈ result, Irreducible (HexPolyZMathlib.toPolynomial g) := by
  set f := HexPolyZMathlib.toPolynomial core with hf_def
  have hf_ne : f ≠ 0 := by
    intro hzero; apply hcore_ne; apply HexPolyZMathlib.equiv.injective
    simpa [hf_def] using hzero
  set gs : List (Polynomial ℤ) := result.map HexPolyZMathlib.toPolynomial with hgs_def
  have hprod' : Associated gs.prod f := by
    have hp_poly : (result.map HexPolyZMathlib.toPolynomial).prod =
        HexPolyZMathlib.toPolynomial core := by
      rw [← polyProduct_toPolynomial, hprod]
    rw [hgs_def, hp_poly, hf_def]
  have hne_all : ∀ g ∈ gs, g ≠ 0 := by
    intro g hg; rw [hgs_def, List.mem_map] at hg
    obtain ⟨factor, hfactor_mem, hg_eq⟩ := hg; rw [← hg_eq]
    exact (toPolynomial_ne_zero_and_not_isUnit_of_shouldRecord
      (hrecord factor hfactor_mem)).1
  have hnonunit_all : ∀ g ∈ gs, ¬ IsUnit g := by
    intro g hg; rw [hgs_def, List.mem_map] at hg
    obtain ⟨factor, hfactor_mem, hg_eq⟩ := hg; rw [← hg_eq]
    exact (toPolynomial_ne_zero_and_not_isUnit_of_shouldRecord
      (hrecord factor hfactor_mem)).2
  have hcover_gs : ∀ q ∈ UniqueFactorizationMonoid.normalizedFactors f,
      ∃ g ∈ gs, Associated g q := by
    intro q hq
    have hq_irr : Irreducible q :=
      UniqueFactorizationMonoid.irreducible_of_normalized_factor q hq
    have hq_dvd : q ∣ f := UniqueFactorizationMonoid.dvd_of_mem_normalizedFactors hq
    have htoPoly : HexPolyZMathlib.toPolynomial (HexPolyZMathlib.ofPolynomial q) = q :=
      HexPolyZMathlib.toPolynomial_ofPolynomial q
    have hfactor_irr :
        Irreducible (HexPolyZMathlib.toPolynomial (HexPolyZMathlib.ofPolynomial q)) := by
      rw [htoPoly]; exact hq_irr
    have hfactor_dvd : HexPolyZMathlib.ofPolynomial q ∣ core := by
      rcases hq_dvd with ⟨r, hr⟩
      refine ⟨HexPolyZMathlib.ofPolynomial r, ?_⟩
      apply HexPolyZMathlib.equiv.injective
      simp only [HexPolyZMathlib.equiv_apply, HexPolyZMathlib.toPolynomial_mul,
        HexPolyZMathlib.toPolynomial_ofPolynomial]
      exact hr
    obtain ⟨emitted, hemitted_mem, hemitted_assoc⟩ := hcover _ hfactor_irr hfactor_dvd
    refine ⟨HexPolyZMathlib.toPolynomial emitted, ?_, ?_⟩
    · rw [hgs_def, List.mem_map]; exact ⟨emitted, hemitted_mem, rfl⟩
    · rw [htoPoly] at hemitted_assoc; exact hemitted_assoc
  have hcard_le : gs.length ≤ (UniqueFactorizationMonoid.normalizedFactors f).card :=
    UFDPartition.length_le_normalizedFactors_card hf_ne gs hne_all hnonunit_all hprod'
  have hcard_ge : (UniqueFactorizationMonoid.normalizedFactors f).card ≤ gs.length :=
    UFDPartition.normalizedFactors_card_le_length_of_coverage hf_ne hsqfree gs hcover_gs
  have hcount : gs.length = (UniqueFactorizationMonoid.normalizedFactors f).card :=
    le_antisymm hcard_le hcard_ge
  intro g hg_mem
  have hpoly_mem : HexPolyZMathlib.toPolynomial g ∈ gs := by
    rw [hgs_def, List.mem_map]; exact ⟨g, hg_mem, rfl⟩
  exact UFDPartition.irreducible_of_partition_card_eq_normalizedFactors_card hf_ne gs
    hne_all hnonunit_all hprod' hcount _ hpoly_mem

/--
Abstract-bound variant of
`recombinationSearchModAux_some_factor_associated_of_liftedFactorSubsetPartition`:
the concrete `2 * defaultFactorCoeffBound core < d.p ^ d.k` Mignotte
precision is replaced by `2 * B' < d.p ^ d.k` against an abstract bound
`B'`, paired with the leading-coefficient bound on `core` and the
universal divisor coefficient bound `∀ g ∣ core, ∀ i, (g.coeff i).natAbs
≤ B'`. Thin wrapper over
`recombinationSearchModAux_some_and_covers_of_liftedFactorSubsetPartition_of_bound`
that extracts the per-factor coverage at the supplied `factor`.
-/
theorem recombinationSearchModAux_some_factor_associated_of_liftedFactorSubsetPartition_of_bound
    {core target factor : Hex.ZPoly} {d : Hex.LiftData}
    {J : LiftedFactorSubset d} {localFactors : List Hex.ZPoly} {fuel : Nat}
    (B' : Nat)
    (hcore_lc_le : (Hex.DensePoly.leadingCoeff core).natAbs ≤ B')
    (hvalid : ∀ g : Hex.ZPoly, g ∣ core → ∀ i, (g.coeff i).natAbs ≤ B')
    (hcore_ne : core ≠ 0)
    (hcore_monic : Hex.DensePoly.Monic core)
    (hd_modulus : 2 ≤ d.p ^ d.k)
    (hd_liftedFactor_monic :
      ∀ i, Hex.DensePoly.Monic (liftedFactor d i))
    (hd_liftedFactor_natDegree_pos :
      ∀ i, 0 < (HexPolyZMathlib.toPolynomial (liftedFactor d i)).natDegree)
    (hd_liftedFactor_inj : Function.Injective (liftedFactor d))
    (hprecision : 2 * B' < d.p ^ d.k)
    (htarget_monic : Hex.DensePoly.Monic target)
    (htarget_dvd_core : target ∣ core)
    (hpartition : LiftedFactorSubsetPartition core d J target)
    (hmatches : LiftedFactorListMatches d J localFactors)
    (hfactor_irr : Irreducible (HexPolyZMathlib.toPolynomial factor))
    (hfactor_dvd_target : factor ∣ target)
    (hfuel : J.card < fuel) :
    ∃ result,
      Hex.recombinationSearchModAux target (d.p ^ d.k) localFactors fuel =
        some result ∧
      ∃ emitted ∈ result,
        Associated (HexPolyZMathlib.toPolynomial emitted)
          (HexPolyZMathlib.toPolynomial factor) := by
  obtain ⟨result, hresult, hcovers⟩ :=
    recombinationSearchModAux_some_and_covers_of_liftedFactorSubsetPartition_of_bound
      B' hvalid hcore_ne hcore_monic hd_modulus hd_liftedFactor_monic
      hd_liftedFactor_natDegree_pos hd_liftedFactor_inj hprecision
      htarget_monic htarget_dvd_core hpartition hmatches hfuel
  exact ⟨result, hresult, hcovers factor hfactor_irr hfactor_dvd_target⟩

/--
Recursive coverage capstone for `Hex.recombinationSearchModAux` (#4301).

Given a `LiftedFactorSubsetPartition core d J target` rest-state predicate at
a recursive recombination level, and an irreducible integer divisor `factor`
of `target`, the executable recombination search returns `some result` with
`factor` (up to `Associated`) among the emitted candidates.

Thin wrapper over
`recombinationSearchModAux_some_factor_associated_of_liftedFactorSubsetPartition_of_bound`
that instantiates `B' := Hex.ZPoly.defaultFactorCoeffBound core` and
discharges the abstract bound hypotheses via
`defaultFactorCoeffBound_leadingCoeff_natAbs_le` paired with
`defaultFactorCoeffBound_valid`. -/
theorem recombinationSearchModAux_some_factor_associated_of_liftedFactorSubsetPartition
    {core target factor : Hex.ZPoly} {d : Hex.LiftData}
    {J : LiftedFactorSubset d} {localFactors : List Hex.ZPoly} {fuel : Nat}
    (hcore_ne : core ≠ 0)
    (hcore_monic : Hex.DensePoly.Monic core)
    (hd_modulus : 2 ≤ d.p ^ d.k)
    (hd_liftedFactor_monic :
      ∀ i, Hex.DensePoly.Monic (liftedFactor d i))
    (hd_liftedFactor_natDegree_pos :
      ∀ i, 0 < (HexPolyZMathlib.toPolynomial (liftedFactor d i)).natDegree)
    (hd_liftedFactor_inj : Function.Injective (liftedFactor d))
    (hprecision : 2 * Hex.ZPoly.defaultFactorCoeffBound core < d.p ^ d.k)
    (htarget_monic : Hex.DensePoly.Monic target)
    (htarget_dvd_core : target ∣ core)
    (hpartition : LiftedFactorSubsetPartition core d J target)
    (hmatches : LiftedFactorListMatches d J localFactors)
    (hfactor_irr : Irreducible (HexPolyZMathlib.toPolynomial factor))
    (hfactor_dvd_target : factor ∣ target)
    (hfuel : J.card < fuel) :
    ∃ result,
      Hex.recombinationSearchModAux target (d.p ^ d.k) localFactors fuel =
        some result ∧
      ∃ emitted ∈ result,
        Associated (HexPolyZMathlib.toPolynomial emitted)
          (HexPolyZMathlib.toPolynomial factor) := by
  have hcore_lc_le := defaultFactorCoeffBound_leadingCoeff_natAbs_le hcore_ne
  exact recombinationSearchModAux_some_factor_associated_of_liftedFactorSubsetPartition_of_bound
    (Hex.ZPoly.defaultFactorCoeffBound core)
    hcore_lc_le
    (defaultFactorCoeffBound_valid core hcore_ne)
    hcore_ne hcore_monic hd_modulus hd_liftedFactor_monic
    hd_liftedFactor_natDegree_pos hd_liftedFactor_inj hprecision
    htarget_monic htarget_dvd_core hpartition hmatches
    hfactor_irr hfactor_dvd_target hfuel

/--
Abstract-bound variant of
`scaledRecombinationSearchModAux_some_factor_associated_of_liftedFactorSubsetPartition`:
the concrete `2 * defaultFactorCoeffBound core < d.p ^ d.k` Mignotte
precision is replaced by `2 * B' < d.p ^ d.k` against an abstract bound
`B'`, paired with the leading-coefficient bound on `core` and the
universal divisor coefficient bound `∀ g ∣ core, ∀ i, (g.coeff i).natAbs
≤ B'`. Thin wrapper over
`RecoveredScaledSearch.covers_of_bound`
that extracts the per-factor coverage at the supplied `factor`.
-/
theorem scaledRecombinationSearchModAux_some_factor_associated_of_liftedFactorSubsetPartition_of_bound
    {core target factor : Hex.ZPoly} {d : Hex.LiftData}
    {J : LiftedFactorSubset d} {localFactors : List Hex.ZPoly} {fuel : Nat}
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
    (hprecision : 2 * B' < d.p ^ d.k)
    (htarget_primitive : Hex.ZPoly.Primitive target)
    (htarget_lc_pos : 0 < Hex.DensePoly.leadingCoeff target)
    (htarget_dvd_core : target ∣ core)
    (hpartition : LiftedFactorSubsetPartition core d J target)
    (hmatches : LiftedFactorListMatches d J localFactors)
    (hfactor_irr : Irreducible (HexPolyZMathlib.toPolynomial factor))
    (hfactor_dvd_target : factor ∣ target)
    (hfuel : J.card < fuel) :
    ∃ result,
      Hex.scaledRecombinationSearchModAux (Hex.DensePoly.leadingCoeff core)
          target (d.p ^ d.k) localFactors fuel =
        some result ∧
      ∃ emitted ∈ result,
        Associated (HexPolyZMathlib.toPolynomial emitted)
          (HexPolyZMathlib.toPolynomial factor) := by
  obtain ⟨result, hresult, hcovers⟩ :=
    RecoveredScaledSearch.covers_of_bound
      B' hcore_lc_le hvalid hcore_ne hcore_primitive hcore_lc_pos hd_modulus
      hd_liftedFactor_monic hd_liftedFactor_natDegree_pos hd_liftedFactor_inj
      hprecision htarget_primitive htarget_lc_pos htarget_dvd_core hpartition
      hmatches hfuel
  exact ⟨result, hresult, hcovers factor hfactor_irr hfactor_dvd_target⟩

/--
Primitive + positive-leading recursive coverage capstone for
`Hex.scaledRecombinationSearchModAux`.

This is the scaled counterpart of
`recombinationSearchModAux_some_factor_associated_of_liftedFactorSubsetPartition`.
It keeps the same fixed-factor conclusion, but the recursive target invariant is
primitive plus positive leading coefficient, and the executable boundary is the
scaled recombination search.

Thin wrapper over
`scaledRecombinationSearchModAux_some_factor_associated_of_liftedFactorSubsetPartition_of_bound`
that instantiates `B' := Hex.ZPoly.defaultFactorCoeffBound core` and
discharges the abstract bound hypotheses via `defaultFactorCoeffBound_valid`
paired with `leadingCoeff_eq_coeff_last`.
-/
theorem scaledRecombinationSearchModAux_some_factor_associated_of_liftedFactorSubsetPartition
    {core target factor : Hex.ZPoly} {d : Hex.LiftData}
    {J : LiftedFactorSubset d} {localFactors : List Hex.ZPoly} {fuel : Nat}
    (hcore_ne : core ≠ 0)
    (hcore_primitive : Hex.ZPoly.Primitive core)
    (hcore_lc_pos : 0 < Hex.DensePoly.leadingCoeff core)
    (hd_modulus : 2 ≤ d.p ^ d.k)
    (hd_liftedFactor_monic :
      ∀ i, Hex.DensePoly.Monic (liftedFactor d i))
    (hd_liftedFactor_natDegree_pos :
      ∀ i, 0 < (HexPolyZMathlib.toPolynomial (liftedFactor d i)).natDegree)
    (hd_liftedFactor_inj : Function.Injective (liftedFactor d))
    (hprecision : 2 * Hex.ZPoly.defaultFactorCoeffBound core < d.p ^ d.k)
    (htarget_primitive : Hex.ZPoly.Primitive target)
    (htarget_lc_pos : 0 < Hex.DensePoly.leadingCoeff target)
    (htarget_dvd_core : target ∣ core)
    (hpartition : LiftedFactorSubsetPartition core d J target)
    (hmatches : LiftedFactorListMatches d J localFactors)
    (hfactor_irr : Irreducible (HexPolyZMathlib.toPolynomial factor))
    (hfactor_dvd_target : factor ∣ target)
    (hfuel : J.card < fuel) :
    ∃ result,
      Hex.scaledRecombinationSearchModAux (Hex.DensePoly.leadingCoeff core)
          target (d.p ^ d.k) localFactors fuel =
        some result ∧
      ∃ emitted ∈ result,
        Associated (HexPolyZMathlib.toPolynomial emitted)
          (HexPolyZMathlib.toPolynomial factor) := by
  have hcore_lc_le := defaultFactorCoeffBound_leadingCoeff_natAbs_le hcore_ne
  exact scaledRecombinationSearchModAux_some_factor_associated_of_liftedFactorSubsetPartition_of_bound
    (Hex.ZPoly.defaultFactorCoeffBound core)
    hcore_lc_le
    (defaultFactorCoeffBound_valid core hcore_ne)
    hcore_ne hcore_primitive hcore_lc_pos hd_modulus hd_liftedFactor_monic
    hd_liftedFactor_natDegree_pos hd_liftedFactor_inj hprecision
    htarget_primitive htarget_lc_pos htarget_dvd_core hpartition hmatches
    hfactor_irr hfactor_dvd_target hfuel

/--
Abstract-bound variant of
`recombinationSearchModAux_some_factor_associated_of_liftedFactorSubsetPartition_of_primitive_pos_lc_core`:
the concrete `2 * defaultFactorCoeffBound core < d.p ^ d.k` Mignotte
precision is replaced by `2 * B' < d.p ^ d.k` against an abstract bound
`B'`, paired with the leading-coefficient bound on `core` and the
universal divisor coefficient bound `∀ g ∣ core, ∀ i, (g.coeff i).natAbs
≤ B'`. Thin wrapper that forwards verbatim to
`scaledRecombinationSearchModAux_some_factor_associated_of_liftedFactorSubsetPartition_of_bound`.
-/
theorem recombinationSearchModAux_some_factor_associated_of_liftedFactorSubsetPartition_of_primitive_pos_lc_core_of_bound
    {core target factor : Hex.ZPoly} {d : Hex.LiftData}
    {J : LiftedFactorSubset d} {localFactors : List Hex.ZPoly} {fuel : Nat}
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
    (hprecision : 2 * B' < d.p ^ d.k)
    (htarget_primitive : Hex.ZPoly.Primitive target)
    (htarget_lc_pos : 0 < Hex.DensePoly.leadingCoeff target)
    (htarget_dvd_core : target ∣ core)
    (hpartition : LiftedFactorSubsetPartition core d J target)
    (hmatches : LiftedFactorListMatches d J localFactors)
    (hfactor_irr : Irreducible (HexPolyZMathlib.toPolynomial factor))
    (hfactor_dvd_target : factor ∣ target)
    (hfuel : J.card < fuel) :
    ∃ result,
      Hex.scaledRecombinationSearchModAux (Hex.DensePoly.leadingCoeff core)
          target (d.p ^ d.k) localFactors fuel =
        some result ∧
      ∃ emitted ∈ result,
        Associated (HexPolyZMathlib.toPolynomial emitted)
          (HexPolyZMathlib.toPolynomial factor) := by
  exact
    scaledRecombinationSearchModAux_some_factor_associated_of_liftedFactorSubsetPartition_of_bound
      B' hcore_lc_le hvalid hcore_ne hcore_primitive hcore_lc_pos hd_modulus
      hd_liftedFactor_monic hd_liftedFactor_natDegree_pos hd_liftedFactor_inj
      hprecision htarget_primitive htarget_lc_pos htarget_dvd_core hpartition
      hmatches hfactor_irr hfactor_dvd_target hfuel

/--
Primitive + positive-leading public wrapper for the scaled recombination
search.  This is the #4648 boundary form of the old monic-core
`recombinationSearchModAux_some_factor_associated_of_liftedFactorSubsetPartition`
surface: callers with a primitive positive-leading core and recursive target
use the scaled executable search directly, while the monic wrapper remains
available for existing unscaled callers.

Thin wrapper over
`recombinationSearchModAux_some_factor_associated_of_liftedFactorSubsetPartition_of_primitive_pos_lc_core_of_bound`
that instantiates `B' := Hex.ZPoly.defaultFactorCoeffBound core` and
discharges the abstract bound hypotheses via `defaultFactorCoeffBound_valid`
paired with `leadingCoeff_eq_coeff_last`.
-/
theorem recombinationSearchModAux_some_factor_associated_of_liftedFactorSubsetPartition_of_primitive_pos_lc_core
    {core target factor : Hex.ZPoly} {d : Hex.LiftData}
    {J : LiftedFactorSubset d} {localFactors : List Hex.ZPoly} {fuel : Nat}
    (hcore_ne : core ≠ 0)
    (hcore_primitive : Hex.ZPoly.Primitive core)
    (hcore_lc_pos : 0 < Hex.DensePoly.leadingCoeff core)
    (hd_modulus : 2 ≤ d.p ^ d.k)
    (hd_liftedFactor_monic :
      ∀ i, Hex.DensePoly.Monic (liftedFactor d i))
    (hd_liftedFactor_natDegree_pos :
      ∀ i, 0 < (HexPolyZMathlib.toPolynomial (liftedFactor d i)).natDegree)
    (hd_liftedFactor_inj : Function.Injective (liftedFactor d))
    (hprecision : 2 * Hex.ZPoly.defaultFactorCoeffBound core < d.p ^ d.k)
    (htarget_primitive : Hex.ZPoly.Primitive target)
    (htarget_lc_pos : 0 < Hex.DensePoly.leadingCoeff target)
    (htarget_dvd_core : target ∣ core)
    (hpartition : LiftedFactorSubsetPartition core d J target)
    (hmatches : LiftedFactorListMatches d J localFactors)
    (hfactor_irr : Irreducible (HexPolyZMathlib.toPolynomial factor))
    (hfactor_dvd_target : factor ∣ target)
    (hfuel : J.card < fuel) :
    ∃ result,
      Hex.scaledRecombinationSearchModAux (Hex.DensePoly.leadingCoeff core)
          target (d.p ^ d.k) localFactors fuel =
        some result ∧
      ∃ emitted ∈ result,
        Associated (HexPolyZMathlib.toPolynomial emitted)
          (HexPolyZMathlib.toPolynomial factor) := by
  have hcore_lc_le := defaultFactorCoeffBound_leadingCoeff_natAbs_le hcore_ne
  exact recombinationSearchModAux_some_factor_associated_of_liftedFactorSubsetPartition_of_primitive_pos_lc_core_of_bound
    (Hex.ZPoly.defaultFactorCoeffBound core)
    hcore_lc_le
    (defaultFactorCoeffBound_valid core hcore_ne)
    hcore_ne hcore_primitive hcore_lc_pos hd_modulus hd_liftedFactor_monic
    hd_liftedFactor_natDegree_pos hd_liftedFactor_inj hprecision
    htarget_primitive htarget_lc_pos htarget_dvd_core hpartition hmatches
    hfactor_irr hfactor_dvd_target hfuel


/-- Initial lifted-partition evidence for `J = Finset.univ` and `target = core`.

This is the deliberately explicit replacement for the old universal
`liftedFactorSubsetPartition_analytic_obligation` over arbitrary
`PrimeChoiceData`.  The five fields are still exactly the corresponding
`LiftedFactorSubsetPartition` fields; callers must now supply the real
successful-lift / descent / classical partition evidence that proves them,
instead of obtaining them from an unsound arbitrary-prime fallback.

Note: the issue text suggested deriving `pairwise_disjoint` /
`unique_up_to_associated` from `unique_subset` alone, but the public predicate
still represents a chosen integer factor, not an associate class of factors.
Both fields therefore remain part of this explicit evidence package. -/
structure InitialLiftedFactorSubsetPartitionEvidence
    (core : Hex.ZPoly) (d : Hex.LiftData) : Prop where
  cover :
    ∀ {i : LiftedFactorIndex d},
      i ∈ (Finset.univ : LiftedFactorSubset d) →
        ∃ (f : Hex.ZPoly) (S : LiftedFactorSubset d),
          Irreducible (HexPolyZMathlib.toPolynomial f) ∧
            f ∣ core ∧
              S ⊆ (Finset.univ : LiftedFactorSubset d) ∧
                i ∈ S ∧ RepresentsIntegerFactorAtLift core d f S
  pairwise_disjoint :
    ∀ {f g : Hex.ZPoly} {S T : LiftedFactorSubset d},
      Irreducible (HexPolyZMathlib.toPolynomial f) →
        f ∣ core →
          RepresentsIntegerFactorAtLift core d f S →
            Irreducible (HexPolyZMathlib.toPolynomial g) →
              g ∣ core →
                RepresentsIntegerFactorAtLift core d g T →
                  ¬ Associated (HexPolyZMathlib.toPolynomial f)
                      (HexPolyZMathlib.toPolynomial g) →
                    Disjoint S T
  unique_up_to_associated :
    ∀ {f g : Hex.ZPoly} {S T : LiftedFactorSubset d},
      Irreducible (HexPolyZMathlib.toPolynomial f) →
        f ∣ core →
          RepresentsIntegerFactorAtLift core d f S →
            Irreducible (HexPolyZMathlib.toPolynomial g) →
              g ∣ core →
                RepresentsIntegerFactorAtLift core d g T →
                  Associated (HexPolyZMathlib.toPolynomial f)
                      (HexPolyZMathlib.toPolynomial g) →
                    S = T
  support_subset_of_dvd_liftedRecoveryCandidate :
    ∀ {f : Hex.ZPoly} {S T : LiftedFactorSubset d},
      Irreducible (HexPolyZMathlib.toPolynomial f) →
        f ∣ core →
          f ∣ liftedRecoveryCandidate core d T →
            RepresentsIntegerFactorAtLift core d f S →
              S ⊆ T
  liftedRecoveryCandidate_eq :
    ∀ {f : Hex.ZPoly} {S : LiftedFactorSubset d},
      Irreducible (HexPolyZMathlib.toPolynomial f) →
        f ∣ core →
          RepresentsIntegerFactorAtLift core d f S →
            liftedRecoveryCandidate core d S = f
/-- Projection wrapper for the initial lifted-partition evidence package. -/
private theorem liftedFactorSubsetPartition_initial_fields
    {core : Hex.ZPoly} {d : Hex.LiftData}
    (h : InitialLiftedFactorSubsetPartitionEvidence core d) :
    (∀ {i : LiftedFactorIndex d},
        i ∈ (Finset.univ : LiftedFactorSubset d) →
          ∃ (f : Hex.ZPoly) (S : LiftedFactorSubset d),
            Irreducible (HexPolyZMathlib.toPolynomial f) ∧
              f ∣ core ∧
                S ⊆ (Finset.univ : LiftedFactorSubset d) ∧
                  i ∈ S ∧ RepresentsIntegerFactorAtLift core d f S) ∧
      (∀ {f g : Hex.ZPoly} {S T : LiftedFactorSubset d},
          Irreducible (HexPolyZMathlib.toPolynomial f) →
            f ∣ core →
              RepresentsIntegerFactorAtLift core d f S →
                Irreducible (HexPolyZMathlib.toPolynomial g) →
                  g ∣ core →
                    RepresentsIntegerFactorAtLift core d g T →
                      ¬ Associated (HexPolyZMathlib.toPolynomial f)
                          (HexPolyZMathlib.toPolynomial g) →
                        Disjoint S T) ∧
        (∀ {f g : Hex.ZPoly} {S T : LiftedFactorSubset d},
            Irreducible (HexPolyZMathlib.toPolynomial f) →
              f ∣ core →
                RepresentsIntegerFactorAtLift core d f S →
                  Irreducible (HexPolyZMathlib.toPolynomial g) →
                    g ∣ core →
                      RepresentsIntegerFactorAtLift core d g T →
                        Associated (HexPolyZMathlib.toPolynomial f)
                            (HexPolyZMathlib.toPolynomial g) →
                          S = T) ∧
          (∀ {f : Hex.ZPoly} {S T : LiftedFactorSubset d},
              Irreducible (HexPolyZMathlib.toPolynomial f) →
                f ∣ core →
                  f ∣ liftedRecoveryCandidate core d T →
                    RepresentsIntegerFactorAtLift core d f S →
                      S ⊆ T) := by
  exact ⟨h.cover, h.pairwise_disjoint, h.unique_up_to_associated,
    h.support_subset_of_dvd_liftedRecoveryCandidate⟩

/--
Initial-state support containment for recovered recombination candidates in the
successful `choosePrimeData?` lifted-factor package.

This is the recovered-coordinate (dilate) support projection of the localized
lifted-partition analytic obligation.  The unscaled `liftedFactorProductCandidate`
sibling is not a field of `InitialLiftedFactorSubsetPartitionEvidence`: on
non-monic cores it is the wrong coordinate and has no non-circular producer.
The full `LiftedFactorSubsetPartition` exposes unscaled support only under a
leading-coefficient-one side condition and derives that field from this
recovered-coordinate projection.
-/
theorem liftedFactorSubsetPartition_initial_support_subset_of_dvd_liftedRecoveryCandidate_of_choosePrimeData
    (core : Hex.ZPoly) (B : Nat) (primeData : Hex.PrimeChoiceData)
    (hinitial :
      InitialLiftedFactorSubsetPartitionEvidence core
        (Hex.ZPoly.toMonicLiftData core B primeData)) :
    let d := Hex.ZPoly.toMonicLiftData core B primeData
    ∀ {f : Hex.ZPoly} {S T : LiftedFactorSubset d},
      Irreducible (HexPolyZMathlib.toPolynomial f) →
      f ∣ core →
      f ∣ liftedRecoveryCandidate core d T →
      RepresentsIntegerFactorAtLift core d f S →
      S ⊆ T := by
  intro d f S T hirr hdvd_core hdvd_candidate hrep
  exact hinitial.support_subset_of_dvd_liftedRecoveryCandidate
    hirr hdvd_core hdvd_candidate hrep

/--
Initial-state recovered-candidate equality for represented factors in the
successful `choosePrimeData?` lifted-factor package.
-/
theorem liftedFactorSubsetPartition_initial_liftedRecoveryCandidate_eq_of_choosePrimeData
    (core : Hex.ZPoly) (B : Nat) (primeData : Hex.PrimeChoiceData)
    (hinitial :
      InitialLiftedFactorSubsetPartitionEvidence core
        (Hex.ZPoly.toMonicLiftData core B primeData)) :
    let d := Hex.ZPoly.toMonicLiftData core B primeData
    ∀ {f : Hex.ZPoly} {S : LiftedFactorSubset d},
      Irreducible (HexPolyZMathlib.toPolynomial f) →
      f ∣ core →
      RepresentsIntegerFactorAtLift core d f S →
      liftedRecoveryCandidate core d S = f := by
  intro d f S hirr hdvd_core hrep
  exact hinitial.liftedRecoveryCandidate_eq hirr hdvd_core hrep

/-- **#4549 supporting lemma (HO-1).**

Parametric constructor for `LiftedFactorSubsetPartition core d
Finset.univ core` over the successful
`Hex.choosePrimeData? core = some primeData` surface, parametric in the core
and the precision count `B` passed to `Hex.ZPoly.toMonicLiftData`.

Square-freeness of `HexPolyZMathlib.toPolynomial core` is taken as an
explicit hypothesis `hcore_sqfree`: the outer-bound specialisation
below threads it in at
`core = (Hex.normalizeForFactor f).squareFreeCore` (where it is
expected to hold by construction), and downstream HO-1 assemblies
supply it from the caller's own square-free-core invariants.  This
matches the issue's option (a) for handling
`target_squarefree`.

Composes:

* `henselSubsetCorrespondenceRest_initial` applied to the explicit `hcorr`
  witness for `toHenselSubsetCorrespondenceRest`;
* `hcore_sqfree` for `target_squarefree`;
* `hinitial` for the recovered-coordinate analytic fields (`cover`,
  `pairwise_disjoint`, `unique_up_to_associated`,
  `support_subset_of_dvd_liftedRecoveryCandidate`, `liftedRecoveryCandidate_eq`).
  The monic-only unscaled support field is derived by rewriting the unscaled
  product candidate to `liftedRecoveryCandidate` under its leading-coefficient
  side condition.

The constructor body does not manufacture correspondence or partition fields
from arbitrary `PrimeChoiceData`; callers must supply the successful-lift
correspondence and partition evidence explicitly. -/
theorem liftedFactorSubsetPartition_of_choosePrimeData
    (core : Hex.ZPoly) (B : Nat)
    (primeData : Hex.PrimeChoiceData)
    (_hchoose : Hex.choosePrimeData? core = some primeData)
    (hcorr :
      HenselSubsetCorrespondenceHypotheses core B primeData
        (Hex.ZPoly.toMonicLiftData core B primeData) True True)
    (hcore_sqfree : Squarefree (HexPolyZMathlib.toPolynomial core))
    (hinitial :
      InitialLiftedFactorSubsetPartitionEvidence core
        (Hex.ZPoly.toMonicLiftData core B primeData)) :
    let d := Hex.ZPoly.toMonicLiftData core B primeData
    LiftedFactorSubsetPartition core d Finset.univ core := by
    obtain ⟨hcover, hdisj, huniq, _⟩ :=
      liftedFactorSubsetPartition_initial_fields hinitial
    exact
      { toHenselSubsetCorrespondenceRest :=
          henselSubsetCorrespondenceRest_initial hcorr
        target_squarefree := hcore_sqfree
        cover := by
          intro i hi
          exact hcover hi
        pairwise_disjoint := by
          intro f g S T hirr_f hdvd_f _ hSrep hirr_g hdvd_g _ hTrep hnoassoc
          exact hdisj (f := f) (g := g) (S := S) (T := T)
            hirr_f hdvd_f hSrep hirr_g hdvd_g hTrep hnoassoc
        unique_up_to_associated := by
          intro f g S T hirr_f hdvd_f _ hSrep hirr_g hdvd_g _ hTrep hassoc
          exact huniq (f := f) (g := g) (S := S) (T := T)
            hirr_f hdvd_f hSrep hirr_g hdvd_g hTrep hassoc
        support_subset_of_dvd_recombinationCandidate := by
          intro f S T hirr hdvd_target _ hcore_lc_one hdvd_cand _ hSrep
          have hdvd_rec :
              f ∣ liftedRecoveryCandidate core
                (Hex.ZPoly.toMonicLiftData core B primeData) T := by
            rw [liftedRecoveryCandidate.eq_recombinationCandidate_of_lc_one
              hcore_lc_one, recombinationCandidate_eq_liftedFactorProductCandidate]
            exact hdvd_cand
          exact
            liftedFactorSubsetPartition_initial_support_subset_of_dvd_liftedRecoveryCandidate_of_choosePrimeData
              core B primeData hinitial hirr hdvd_target hdvd_rec hSrep
        support_subset_of_dvd_liftedRecoveryCandidate := by
          intro f S T hirr hdvd_target _ hdvd_cand _ hSrep
          exact
            liftedFactorSubsetPartition_initial_support_subset_of_dvd_liftedRecoveryCandidate_of_choosePrimeData
              core B primeData hinitial hirr hdvd_target hdvd_cand hSrep
        liftedRecoveryCandidate_eq := by
          intro f S hirr hdvd_target _ hSrep
          exact
            liftedFactorSubsetPartition_initial_liftedRecoveryCandidate_eq_of_choosePrimeData
              core B primeData hinitial hirr hdvd_target hSrep }

/-- **#6172 supporting lemma (HO-1, non-monic-core sibling).**

Parallel to `liftedFactorSubsetPartition_of_choosePrimeData` but consumes
the `Hex.ZPoly.toMonicPrimeData? core = some primeData` witness directly.
Used by the non-monic-friendly substrate constructor
`slowPathHenselSubstrate_of_toMonicChoosePrimeData` below, which feeds the
slow-path arm of #4170 from `(Hex.normalizeForFactor f).squareFreeCore`.
The embedded Hensel correspondence is supplied explicitly as `hcorr`. -/
theorem liftedFactorSubsetPartition_of_toMonicPrimeData
    (core : Hex.ZPoly) (B : Nat)
    (primeData : Hex.PrimeChoiceData)
    (_hselected : Hex.ZPoly.toMonicPrimeData? core = some primeData)
    (hcorr :
      HenselSubsetCorrespondenceHypotheses core B primeData
        (Hex.ZPoly.toMonicLiftData core B primeData) True True)
    (hcore_sqfree : Squarefree (HexPolyZMathlib.toPolynomial core))
    (hinitial :
      InitialLiftedFactorSubsetPartitionEvidence core
        (Hex.ZPoly.toMonicLiftData core B primeData)) :
    let d := Hex.ZPoly.toMonicLiftData core B primeData
    LiftedFactorSubsetPartition core d Finset.univ core := by
    obtain ⟨hcover, hdisj, huniq, _⟩ :=
      liftedFactorSubsetPartition_initial_fields hinitial
    exact
      { toHenselSubsetCorrespondenceRest :=
          henselSubsetCorrespondenceRest_initial hcorr
        target_squarefree := hcore_sqfree
        cover := by
          intro i hi
          exact hcover hi
        pairwise_disjoint := by
          intro f g S T hirr_f hdvd_f _ hSrep hirr_g hdvd_g _ hTrep hnoassoc
          exact hdisj (f := f) (g := g) (S := S) (T := T)
            hirr_f hdvd_f hSrep hirr_g hdvd_g hTrep hnoassoc
        unique_up_to_associated := by
          intro f g S T hirr_f hdvd_f _ hSrep hirr_g hdvd_g _ hTrep hassoc
          exact huniq (f := f) (g := g) (S := S) (T := T)
            hirr_f hdvd_f hSrep hirr_g hdvd_g hTrep hassoc
        support_subset_of_dvd_recombinationCandidate := by
          intro f S T hirr hdvd_target _ hcore_lc_one hdvd_cand _ hSrep
          have hdvd_rec :
              f ∣ liftedRecoveryCandidate core
                (Hex.ZPoly.toMonicLiftData core B primeData) T := by
            rw [liftedRecoveryCandidate.eq_recombinationCandidate_of_lc_one
              hcore_lc_one, recombinationCandidate_eq_liftedFactorProductCandidate]
            exact hdvd_cand
          exact
            liftedFactorSubsetPartition_initial_support_subset_of_dvd_liftedRecoveryCandidate_of_choosePrimeData
              core B primeData hinitial hirr hdvd_target hdvd_rec hSrep
        support_subset_of_dvd_liftedRecoveryCandidate := by
          intro f S T hirr hdvd_target _ hdvd_cand _ hSrep
          exact
            liftedFactorSubsetPartition_initial_support_subset_of_dvd_liftedRecoveryCandidate_of_choosePrimeData
              core B primeData hinitial hirr hdvd_target hdvd_cand hSrep
        liftedRecoveryCandidate_eq := by
          intro f S hirr hdvd_target _ hSrep
          exact
            liftedFactorSubsetPartition_initial_liftedRecoveryCandidate_eq_of_choosePrimeData
              core B primeData hinitial hirr hdvd_target hSrep }

/-! ### `ModPSubsetPartitionHypotheses` existence/uniqueness assembly

These theorems compose the `monicModPImage` divisibility lemma,
`factors_irreducible_of_choosePrimeData_of_some`, and the UFD subset
existence/uniqueness lemma from `UFDPartition.lean` to discharge the
`exists_subset` / `unique_subset` fields of `ModPSubsetPartitionHypotheses`
in the `choosePrimeData? core = some primeData` branch. The wrapper
exposes the caller-facing shape under the same `hsome` hypothesis. -/

/-- `factorsModP.toList` mapped to Mathlib polynomials has product equal to the
Mathlib transport of `monicModularImage (modP p core)`. -/
private lemma toMathlibPolynomial_factorsModP_product_eq_monicModularImage
    {core : Hex.ZPoly} {primeData : Hex.PrimeChoiceData}
    (hsome : Hex.choosePrimeData? core = some primeData) :
    letI := primeData.bounds
    ((primeData.factorsModP.toList : Multiset _).map
        HexBerlekampMathlib.toMathlibPolynomial).prod =
      HexBerlekampMathlib.toMathlibPolynomial
        (Hex.monicModularImage
          (@Hex.ZPoly.modP primeData.p primeData.bounds core)) := by
  letI := primeData.bounds
  have hprime : Hex.Nat.Prime primeData.p :=
    Hex.choosePrimeData?_prime core primeData hsome
  letI : Hex.ZMod64.PrimeModulus primeData.p :=
    Hex.ZMod64.primeModulusOfPrime hprime
  obtain ⟨hzero, hfactors_eq⟩ :=
    Hex.choosePrimeData?_factorsModP_berlekamp_form core primeData hsome
  let hfield := @Hex.zmod64FieldOfPrime primeData.p primeData.bounds
    (Hex.ZMod64.primeModulusOfPrime hprime)
  letI := hfield
  set raw :=
      (@Hex.Berlekamp.berlekampFactor primeData.p primeData.bounds
        (Hex.monicModularImage (Hex.ZPoly.modP primeData.p core))
        (Hex.monicModularImage_monic hprime _ hzero)
        hfield).factors with hraw_def
  have hraw_ne : ∀ g ∈ raw, g ≠ 0 :=
    Hex.Berlekamp.berlekampFactor_factors_ne_zero
      (Hex.monicModularImage (Hex.ZPoly.modP primeData.p core))
      (Hex.monicModularImage_monic hprime _ hzero)
  have hmonic_image_monic :
      Hex.DensePoly.Monic
        (Hex.monicModularImage (Hex.ZPoly.modP primeData.p core)) :=
    Hex.monicModularImage_monic hprime _ hzero
  have hprod_raw :
      Hex.Berlekamp.factorProduct raw =
        Hex.monicModularImage (Hex.ZPoly.modP primeData.p core) :=
    Hex.Berlekamp.factorProduct_berlekampFactor _ _
  have hprod_mapped :
      Hex.Berlekamp.factorProduct (raw.map Hex.monicModularImage) =
        Hex.monicModularImage (Hex.ZPoly.modP primeData.p core) := by
    rw [Hex.factorProduct_map_monicModularImage_eq_monicModularImage_factorProduct
        hprime raw hraw_ne, hprod_raw]
    exact Hex.monicModularImage_eq_self_of_monic hprime _ hmonic_image_monic
  have hlist : primeData.factorsModP.toList = raw.map Hex.monicModularImage := by
    rw [hfactors_eq]
  have hbridge :
      (primeData.factorsModP.toList.map HexBerlekampMathlib.toMathlibPolynomial).prod =
        HexBerlekampMathlib.toMathlibPolynomial
          (Hex.monicModularImage (Hex.ZPoly.modP primeData.p core)) := by
    rw [hlist, ← toMathlibPolynomial_listFoldlMul_one (raw.map Hex.monicModularImage)]
    show HexBerlekampMathlib.toMathlibPolynomial
        (Hex.Berlekamp.factorProduct (raw.map Hex.monicModularImage)) = _
    rw [hprod_mapped]
  rw [← hbridge]
  exact Multiset.prod_coe _

/-- `Finset.univ.val.map` of the indexed Mathlib factor function recovers the
mapped-to-Mathlib multiset of `factorsModP.toList`. -/
private lemma univ_val_map_modPFactor_eq_factorsModP_map
    (primeData : Hex.PrimeChoiceData) :
    letI := primeData.bounds
    ((Finset.univ : Finset (ModPFactorIndex primeData)).val.map fun i =>
        HexBerlekampMathlib.toMathlibPolynomial (modPFactor primeData i)) =
      ((primeData.factorsModP.toList : Multiset _).map
        HexBerlekampMathlib.toMathlibPolynomial) := by
  letI := primeData.bounds
  unfold modPFactor
  rw [Finset.val_univ_fin]
  rw [show (primeData.factorsModP.toList : List _) =
        List.ofFn (fun i : Fin primeData.factorsModP.size => primeData.factorsModP[i]) from
        List.ofFn_getElem.symm]
  rw [Multiset.map_coe, Multiset.map_coe]
  congr 1
  rw [List.ofFn_eq_map, List.map_map]
  rfl

/-- A submultiset of an injective Finset image can be recovered by filtering. -/
private lemma map_filter_eq_of_le_map_val
    {α β : Type*} [DecidableEq β]
    {f : α → β} (hf_inj : Function.Injective f)
    (S : Finset α)
    {t : Multiset β}
    (h : t ≤ S.val.map f) :
    (S.filter (fun a => f a ∈ t)).val.map f = t := by
  classical
  have hSnodup : S.val.Nodup := S.nodup
  have hmap_nodup : (S.val.map f).Nodup := hSnodup.map hf_inj
  have ht_nodup : t.Nodup := Multiset.nodup_of_le h hmap_nodup
  have hSfilter_nodup : (S.filter (fun a => f a ∈ t)).val.Nodup :=
    (S.filter _).nodup
  have hLHS_nodup :
      ((S.filter (fun a => f a ∈ t)).val.map f).Nodup :=
    hSfilter_nodup.map hf_inj
  refine Multiset.Nodup.ext hLHS_nodup ht_nodup |>.mpr ?_
  intro x
  constructor
  · intro hx
    rw [Multiset.mem_map] at hx
    obtain ⟨a, ha_mem, ha_eq⟩ := hx
    rw [Finset.mem_val, Finset.mem_filter] at ha_mem
    rw [← ha_eq]; exact ha_mem.2
  · intro hxt
    have hxmap : x ∈ S.val.map f := Multiset.mem_of_le h hxt
    rw [Multiset.mem_map] at hxmap
    obtain ⟨a, ha_mem, ha_eq⟩ := hxmap
    rw [Multiset.mem_map]
    refine ⟨a, ?_, ha_eq⟩
    rw [Finset.mem_val, Finset.mem_filter]
    refine ⟨ha_mem, ?_⟩
    rw [ha_eq]; exact hxt

/-- For every indexed modular factor selected by a successful
`choosePrimeData?` run, recover an irreducible integer divisor whose monic
mod-`p` image is divisible by that indexed factor. -/
theorem exists_factor_of_modPIndex
    (core : Hex.ZPoly) (hcore_ne : core ≠ 0)
    (hcore_pos : 0 < core.degree?.getD 0)
    (primeData : Hex.PrimeChoiceData)
    (hsome : Hex.choosePrimeData? core = some primeData)
    (i : ModPFactorIndex primeData) :
    letI := primeData.bounds
    ∃ g : Hex.ZPoly,
      Irreducible (HexPolyZMathlib.toPolynomial g) ∧
      g ∣ core ∧
      HexBerlekampMathlib.toMathlibPolynomial (modPFactor primeData i) ∣
        HexBerlekampMathlib.toMathlibPolynomial
          (monicModPImage (Hex.ZPoly.modP primeData.p g)) := by
  classical
  letI := primeData.bounds
  have hprime : Hex.Nat.Prime primeData.p :=
    Hex.choosePrimeData?_prime core primeData hsome
  letI : Hex.ZMod64.PrimeModulus primeData.p :=
    Hex.ZMod64.primeModulusOfPrime hprime
  have hprime_root : _root_.Nat.Prime primeData.p := by
    refine _root_.Nat.prime_def_lt.mpr ⟨hprime.two_le, ?_⟩
    intro m hmlt hmdvd
    rcases hprime.right m hmdvd with h | h
    · exact h
    · exact absurd h (Nat.ne_of_lt hmlt)
  haveI : Fact (_root_.Nat.Prime primeData.p) := ⟨hprime_root⟩
  have hgood : @Hex.isGoodPrime core primeData.p primeData.bounds = true :=
    Hex.choosePrimeData?_isGoodPrime core primeData hsome
  have hcore_modP_iszero :
      (@Hex.ZPoly.modP primeData.p primeData.bounds core).isZero = false :=
    Hex.isGoodPrime_modP_isZero_false core primeData.p hgood
  let hfield := @Hex.zmod64FieldOfPrime primeData.p primeData.bounds
    (Hex.ZMod64.primeModulusOfPrime hprime)
  letI := hfield
  set f : ModPFactorIndex primeData → Polynomial (ZMod primeData.p) :=
      fun i => HexBerlekampMathlib.toMathlibPolynomial (modPFactor primeData i)
      with hf_def
  have hirr_i : Irreducible (f i) := by
    rw [hf_def]
    exact factors_irreducible_of_choosePrimeData_of_some core primeData hsome hcore_pos i
  have hprime_i : Prime (f i) :=
    UniqueFactorizationMonoid.irreducible_iff_prime.mp hirr_i
  have hfi_dvd_monic_core :
      f i ∣
        HexBerlekampMathlib.toMathlibPolynomial
          (Hex.monicModularImage
            (@Hex.ZPoly.modP primeData.p primeData.bounds core)) := by
    rw [← toMathlibPolynomial_factorsModP_product_eq_monicModularImage hsome,
      ← univ_val_map_modPFactor_eq_factorsModP_map primeData]
    exact Multiset.dvd_prod (by
      rw [Multiset.mem_map]
      exact ⟨i, by simp, rfl⟩)
  have hmonic_core_dvd_core :
      HexBerlekampMathlib.toMathlibPolynomial
          (Hex.monicModularImage
            (@Hex.ZPoly.modP primeData.p primeData.bounds core)) ∣
        HexBerlekampMathlib.toMathlibPolynomial
          (@Hex.ZPoly.modP primeData.p primeData.bounds core) :=
    toMathlibPolynomial_dvd
      (monicModularImage_dvd_self_of_isZero_false hprime hcore_modP_iszero)
  have hfi_dvd_map_core :
      f i ∣ (HexPolyZMathlib.toPolynomial core).map
        (Int.castRingHom (ZMod primeData.p)) := by
    rw [← toMathlibPolynomial_modP_eq_map_intCast_zmod]
    exact hfi_dvd_monic_core.trans hmonic_core_dvd_core
  set corePoly : Polynomial ℤ := HexPolyZMathlib.toPolynomial core with hcorePoly_def
  have hcorePoly_ne : corePoly ≠ 0 := by
    intro hzero
    apply hcore_ne
    apply HexPolyZMathlib.equiv.injective
    simpa [hcorePoly_def] using hzero
  have hfi_dvd_map_norm :
      f i ∣ (normalize corePoly).map (Int.castRingHom (ZMod primeData.p)) := by
    have hcore_dvd_norm : corePoly ∣ normalize corePoly :=
      (associated_normalize corePoly).dvd
    have hmap_core_dvd_norm :
        corePoly.map (Int.castRingHom (ZMod primeData.p)) ∣
          (normalize corePoly).map (Int.castRingHom (ZMod primeData.p)) :=
      Polynomial.map_dvd _ hcore_dvd_norm
    have hfi_dvd_map_core' :
        f i ∣ corePoly.map (Int.castRingHom (ZMod primeData.p)) := by
      simpa [hcorePoly_def] using hfi_dvd_map_core
    exact hfi_dvd_map_core'.trans hmap_core_dvd_norm
  set qList : List (Polynomial ℤ) :=
    (UniqueFactorizationMonoid.normalizedFactors corePoly).toList with hqList_def
  have hmap_list_prod (xs : List (Polynomial ℤ)) :
      (xs.map
          (fun q : Polynomial ℤ =>
            q.map (Int.castRingHom (ZMod primeData.p)))).prod =
        xs.prod.map (Int.castRingHom (ZMod primeData.p)) := by
    induction xs with
    | nil =>
        simp
    | cons q qs ih =>
        simp [ih, Polynomial.map_mul]
  have hmap_prod :
      (qList.map
          (fun q : Polynomial ℤ =>
            q.map (Int.castRingHom (ZMod primeData.p)))).prod =
        (normalize corePoly).map (Int.castRingHom (ZMod primeData.p)) := by
    have hnorm_prod_list : qList.prod = normalize corePoly := by
      rw [hqList_def]
      simpa [Multiset.prod_coe] using
        UniqueFactorizationMonoid.prod_normalizedFactors_eq hcorePoly_ne
    rw [hmap_list_prod, hnorm_prod_list]
  have hfi_dvd_normprod :
      f i ∣
        (qList.map
          (fun q : Polynomial ℤ =>
            q.map (Int.castRingHom (ZMod primeData.p)))).prod := by
    rw [hmap_prod]
    exact hfi_dvd_map_norm
  obtain ⟨qMap, hqMap_mem, hfi_dvd_qMap⟩ :=
    (Prime.dvd_prod_iff hprime_i).mp hfi_dvd_normprod
  rcases List.mem_map.mp hqMap_mem with ⟨q, hq_mem_list, hqMap_eq⟩
  have hq_mem : q ∈ UniqueFactorizationMonoid.normalizedFactors corePoly := by
    rw [← Multiset.mem_toList, ← hqList_def]
    exact hq_mem_list
  subst qMap
  set g : Hex.ZPoly := HexPolyZMathlib.ofPolynomial q with hg_def
  have hg_toPoly : HexPolyZMathlib.toPolynomial g = q := by
    simp [hg_def]
  have hg_irr : Irreducible (HexPolyZMathlib.toPolynomial g) := by
    rw [hg_toPoly]
    exact UniqueFactorizationMonoid.irreducible_of_normalized_factor q hq_mem
  have hg_dvd : g ∣ core := by
    have hq_dvd : q ∣ corePoly :=
      UniqueFactorizationMonoid.dvd_of_mem_normalizedFactors hq_mem
    rcases hq_dvd with ⟨r, hr⟩
    refine ⟨HexPolyZMathlib.ofPolynomial r, ?_⟩
    apply HexPolyZMathlib.equiv.injective
    show HexPolyZMathlib.toPolynomial core =
      HexPolyZMathlib.toPolynomial (g * HexPolyZMathlib.ofPolynomial r)
    rw [HexPolyZMathlib.toPolynomial_mul, hg_toPoly,
      HexPolyZMathlib.toPolynomial_ofPolynomial, ← hcorePoly_def]
    exact hr
  have hfi_dvd_modP_g :
      f i ∣
        HexBerlekampMathlib.toMathlibPolynomial
          (@Hex.ZPoly.modP primeData.p primeData.bounds g) := by
    rw [toMathlibPolynomial_modP_eq_map_intCast_zmod, hg_toPoly]
    exact hfi_dvd_qMap
  have hfi_dvd_monic_g :
      f i ∣
        HexBerlekampMathlib.toMathlibPolynomial
          (@monicModPImage primeData.p primeData.bounds
            (@Hex.ZPoly.modP primeData.p primeData.bounds g)) := by
    by_cases hzero :
        (@Hex.ZPoly.modP primeData.p primeData.bounds g).isZero = true
    · have hmonic_zero :
          @monicModPImage primeData.p primeData.bounds
              (@Hex.ZPoly.modP primeData.p primeData.bounds g) = 0 := by
        unfold monicModPImage
        rw [if_pos hzero]
      rw [hmonic_zero]
      have hz : HexBerlekampMathlib.toMathlibPolynomial
          (0 : Hex.FpPoly primeData.p) = 0 := by
        apply Polynomial.ext
        intro n
        rw [Polynomial.coeff_zero, HexBerlekampMathlib.coeff_toMathlibPolynomial,
          Hex.DensePoly.coeff_eq_zero_of_size_le _
            (show (0 : Hex.FpPoly primeData.p).size ≤ n by simp)]
        exact HexModArithMathlib.ZMod64.toZMod_zero
      rw [hz]
      exact dvd_zero (f i)
    · have hnz :
          (@Hex.ZPoly.modP primeData.p primeData.bounds g).isZero = false := by
        cases h :
            (@Hex.ZPoly.modP primeData.p primeData.bounds g).isZero <;>
          simp_all
      exact hfi_dvd_modP_g.trans
        (toMathlibPolynomial_dvd (self_dvd_monicModPImage hnz))
  refine ⟨g, hg_irr, hg_dvd, ?_⟩
  simpa [hf_def] using hfi_dvd_monic_g

/-- Final assembly: the analyzable `choosePrimeData? core = some primeData`
branch of the integer-irreducible → mod-`p` representing-subset existence
and uniqueness statement. -/
theorem existsUnique_modPFactorSubset_of_choosePrimeData_of_some
    (core : Hex.ZPoly) {factor : Hex.ZPoly}
    (hirr : Irreducible (HexPolyZMathlib.toPolynomial factor))
    (hdvd : factor ∣ core)
    (hcore_ne : core ≠ 0)
    (hcore_pos : 0 < core.degree?.getD 0)
    (primeData : Hex.PrimeChoiceData)
    (hsome : Hex.choosePrimeData? core = some primeData) :
    ∃! S : ModPFactorSubset primeData,
      RepresentsIntegerFactorModP primeData factor S := by
  classical
  letI := primeData.bounds
  have hprime : Hex.Nat.Prime primeData.p :=
    Hex.choosePrimeData?_prime core primeData hsome
  letI : Hex.ZMod64.PrimeModulus primeData.p :=
    Hex.ZMod64.primeModulusOfPrime hprime
  have hprime_root : _root_.Nat.Prime primeData.p := by
    refine _root_.Nat.prime_def_lt.mpr ⟨hprime.two_le, ?_⟩
    intro m hmlt hmdvd
    rcases hprime.right m hmdvd with h | h
    · exact h
    · exact absurd h (Nat.ne_of_lt hmlt)
  haveI : Fact (_root_.Nat.Prime primeData.p) := ⟨hprime_root⟩
  obtain ⟨hzero, hfactors_eq⟩ :=
    Hex.choosePrimeData?_factorsModP_berlekamp_form core primeData hsome
  have hform : Hex.factorsModPBerlekampForm core primeData :=
    ⟨hprime, hzero, hfactors_eq⟩
  have hgood : @Hex.isGoodPrime core primeData.p primeData.bounds = true :=
    Hex.choosePrimeData?_isGoodPrime core primeData hsome
  have hnodup : primeData.factorsModP.toList.Nodup :=
    factorsModP_nodup_of_factorsModPBerlekampForm core primeData hform hgood
  let hfield := @Hex.zmod64FieldOfPrime primeData.p primeData.bounds
    (Hex.ZMod64.primeModulusOfPrime hprime)
  letI := hfield
  -- Set up abbreviations.
  set f : ModPFactorIndex primeData → Polynomial (ZMod primeData.p) :=
      fun i => HexBerlekampMathlib.toMathlibPolynomial (modPFactor primeData i)
      with hf_def
  set factorsM : Multiset (Polynomial (ZMod primeData.p)) :=
      ((primeData.factorsModP.toList : Multiset _).map
        HexBerlekampMathlib.toMathlibPolynomial) with hfactorsM_def
  set mathD : Polynomial (ZMod primeData.p) :=
      HexBerlekampMathlib.toMathlibPolynomial
        (@monicModPImage primeData.p primeData.bounds
          (@Hex.ZPoly.modP primeData.p primeData.bounds factor))
      with hmathD_def
  -- `factorsM` equals the univ-image of `f`.
  have hfactorsM_univ : factorsM = Finset.univ.val.map f :=
    (univ_val_map_modPFactor_eq_factorsModP_map primeData).symm
  -- `toMathlibPolynomial` is injective via `fpPolyEquiv`.
  have hinjPoly :
      Function.Injective
        (HexBerlekampMathlib.toMathlibPolynomial : Hex.FpPoly primeData.p → _) :=
    HexBerlekampMathlib.fpPolyEquiv.injective
  -- `modPFactor` is injective on `Fin n` (via factorsModP.toList.Nodup).
  have hmodPFactor_inj :
      Function.Injective (modPFactor primeData) := by
    intro i j hij
    have h_get_i :
        primeData.factorsModP.toList[i.val]'(by
          rw [Array.length_toList]; exact i.isLt) = primeData.factorsModP[i] := by
      simp
    have h_get_j :
        primeData.factorsModP.toList[j.val]'(by
          rw [Array.length_toList]; exact j.isLt) = primeData.factorsModP[j] := by
      simp
    have h_eq :
        primeData.factorsModP.toList[i.val]'(by
            rw [Array.length_toList]; exact i.isLt) =
          primeData.factorsModP.toList[j.val]'(by
            rw [Array.length_toList]; exact j.isLt) := by
      rw [h_get_i, h_get_j]; exact hij
    exact Fin.ext (List.Nodup.getElem_inj_iff hnodup |>.mp h_eq)
  -- `f` is injective.
  have hf_inj : Function.Injective f := fun i j hij =>
    hmodPFactor_inj (hinjPoly hij)
  -- factorsM is nodup.
  have hfactorsM_nodup : factorsM.Nodup := by
    rw [hfactorsM_def]
    exact (Multiset.coe_nodup.mpr hnodup).map hinjPoly
  -- Each q in factorsM is irreducible.
  have hirr_each : ∀ q ∈ factorsM, Irreducible q := by
    intro q hq
    rw [hfactorsM_def, Multiset.mem_map] at hq
    obtain ⟨g, hg_mem, hg_eq⟩ := hq
    rw [Multiset.mem_coe] at hg_mem
    obtain ⟨i, hi⟩ := List.mem_iff_get.mp hg_mem
    have hi_eq : modPFactor primeData ⟨i.val, by
        rw [← Array.length_toList]; exact i.isLt⟩ = g := by
      unfold modPFactor
      have hget : primeData.factorsModP.toList.get i = g := hi
      simpa [List.get_eq_getElem] using hget
    rw [← hg_eq, ← hi_eq]
    exact factors_irreducible_of_choosePrimeData_of_some core primeData hsome hcore_pos _
  -- Each q in factorsM is monic, hence normalize-fixed.
  have hmonic_each : ∀ q ∈ factorsM, q.Monic := by
    intro q hq
    rw [hfactorsM_def, Multiset.mem_map] at hq
    obtain ⟨g, hg_mem, hg_eq⟩ := hq
    rw [Multiset.mem_coe] at hg_mem
    have hg_monic : Hex.DensePoly.Monic g :=
      factorsModP_monic_of_factorsModPBerlekampForm core primeData hform g
        (Array.mem_toList_iff.mp hg_mem)
    rw [← hg_eq]
    exact HexBerlekampMathlib.toMathlibPolynomial_monic g hg_monic
  have hnorm_each : ∀ q ∈ factorsM, normalize q = q := fun q hq =>
    (hmonic_each q hq).normalize_eq_self
  -- mathD is monic, hence normalize-fixed.
  have hmonicModPImage_monic :
      Hex.DensePoly.Monic
        (@monicModPImage primeData.p primeData.bounds
          (@Hex.ZPoly.modP primeData.p primeData.bounds factor)) := by
    apply monicModPImage_monic_of_ne_zero hprime
    -- factor must not vanish mod p; derived from the divisibility facts.
    have hfactor_dvd_core_modP :
        @Hex.ZPoly.modP primeData.p primeData.bounds factor ∣
          @Hex.ZPoly.modP primeData.p primeData.bounds core :=
      modP_dvd_modP_of_dvd primeData.p hdvd
    have hcore_modP_iszero :
        (@Hex.ZPoly.modP primeData.p primeData.bounds core).isZero = false :=
      Hex.isGoodPrime_modP_isZero_false core primeData.p hgood
    exact fpPoly_isZero_false_of_dvd_of_isZero_false
      hfactor_dvd_core_modP hcore_modP_iszero
  have hmathD_monic : mathD.Monic := by
    rw [hmathD_def]
    exact HexBerlekampMathlib.toMathlibPolynomial_monic _ hmonicModPImage_monic
  have hmathD_norm : normalize mathD = mathD := hmathD_monic.normalize_eq_self
  -- mathD ∣ factorsM.prod.
  have hbridge_dvd :
      @monicModPImage primeData.p primeData.bounds
          (@Hex.ZPoly.modP primeData.p primeData.bounds factor) ∣
        Hex.monicModularImage
          (@Hex.ZPoly.modP primeData.p primeData.bounds core) :=
    monicModPImage_dvd_monicModularImage_of_dvd_of_choosePrimeData?_some
      hdvd hcore_ne hsome
  have hmathD_dvd : mathD ∣ factorsM.prod := by
    rw [hfactorsM_def, toMathlibPolynomial_factorsModP_product_eq_monicModularImage hsome,
      hmathD_def]
    rcases hbridge_dvd with ⟨c, hc⟩
    refine ⟨HexBerlekampMathlib.toMathlibPolynomial c, ?_⟩
    rw [hc, toMathlibPolynomial_mul]
  -- Apply the UFD lemma.
  obtain ⟨T, ⟨hT_le, hT_prod⟩, hT_uniq⟩ :=
    HexBerlekampZassenhausMathlib.UFDPartition.existsUnique_subset_product_eq_of_dvd_of_squarefree_prod
      hirr_each hnorm_each hfactorsM_nodup hmathD_norm hmathD_dvd
  -- Construct S from T.
  set Stwit : ModPFactorSubset primeData :=
      Finset.univ.filter (fun i : ModPFactorIndex primeData => f i ∈ T) with hStwit_def
  have hStwit_map : Stwit.val.map f = T := by
    rw [hStwit_def]
    have hle : T ≤ Finset.univ.val.map f := by
      rw [← hfactorsM_univ]; exact hT_le
    exact map_filter_eq_of_le_map_val hf_inj Finset.univ hle
  refine ⟨Stwit, ?_, ?_⟩
  · -- Existence.
    show modPFactorProduct primeData Stwit =
        @monicModPImage primeData.p primeData.bounds
          (@Hex.ZPoly.modP primeData.p primeData.bounds factor)
    apply hinjPoly
    rw [toMathlibPolynomial_modPFactorProduct]
    show (∏ i ∈ Stwit, f i) = mathD
    rw [Finset.prod_eq_multiset_prod, hStwit_map]; exact hT_prod
  · -- Uniqueness.
    intro S' hS'
    have hS'_prod :
        modPFactorProduct primeData S' =
          @monicModPImage primeData.p primeData.bounds
            (@Hex.ZPoly.modP primeData.p primeData.bounds factor) := hS'
    apply Finset.val_inj.mp
    apply Multiset.map_injective hf_inj
    have hS'_map_le : S'.val.map f ≤ factorsM := by
      rw [hfactorsM_univ]
      apply Multiset.map_le_map
      exact Finset.val_le_iff.mpr (Finset.subset_univ _)
    have hS'_map_prod : (S'.val.map f).prod = mathD := by
      rw [← Finset.prod_eq_multiset_prod, ← toMathlibPolynomial_modPFactorProduct,
        hS'_prod]
    have hS'_T : S'.val.map f = T :=
      hT_uniq _ ⟨hS'_map_le, hS'_map_prod⟩
    rw [hS'_T, ← hStwit_map]

/-- Caller-facing wrapper for the witness-form
`Hex.choosePrimeData? core = some primeData` branch required by the
`ModPSubsetPartitionHypotheses` constructor. The explicit `hchoose` witness
excludes the `none` branch where the mod-`p` factorisation invariant is
unavailable. -/
theorem existsUnique_modPFactorSubset_of_choosePrimeData
    (core : Hex.ZPoly) {factor : Hex.ZPoly}
    (primeData : Hex.PrimeChoiceData)
    (hirr : Irreducible (HexPolyZMathlib.toPolynomial factor))
    (hdvd : factor ∣ core)
    (hcore_pos : 0 < core.degree?.getD 0)
    (hchoose : Hex.choosePrimeData? core = some primeData) :
    ∃! S : ModPFactorSubset primeData,
      RepresentsIntegerFactorModP primeData factor S := by
  letI : Hex.ZMod64.Bounds primeData.p := primeData.bounds
  -- `core ≠ 0` from `isGoodPrime` (which forces `(modP p core).isZero = false`).
  have hcore_ne : core ≠ 0 := by
    intro hcore_zero
    have hgood : @Hex.isGoodPrime core primeData.p primeData.bounds = true :=
      Hex.choosePrimeData?_isGoodPrime core primeData hchoose
    have hcore_modP_iszero :
        (@Hex.ZPoly.modP primeData.p primeData.bounds core).isZero = false :=
      Hex.isGoodPrime_modP_isZero_false core primeData.p hgood
    have hzero_modP : @Hex.ZPoly.modP primeData.p primeData.bounds 0 = 0 := by
      apply Hex.DensePoly.ext_coeff
      intro k
      rw [Hex.ZPoly.coeff_modP, Hex.DensePoly.coeff_zero]
      rfl
    rw [hcore_zero, hzero_modP] at hcore_modP_iszero
    exact Bool.noConfusion hcore_modP_iszero
  exact existsUnique_modPFactorSubset_of_choosePrimeData_of_some core
    hirr hdvd hcore_ne hcore_pos primeData hchoose

/-- **HO-1 supporting lemma (#4688).**

`ModPSubsetPartitionHypotheses` constructor at the executable
`Hex.choosePrimeData` boundary.

Composes:

* `Hex.choosePrimeData?_fModP_eq` for `fModP_eq`;
* `trivial` for the `True` `admissible_prime` / `square_free_reduction` hooks;
* `factors_irreducible_of_choosePrimeData_of_some` (#4686) for the per-factor
  irreducibility component;
* `existsUnique_modPFactorSubset_of_choosePrimeData` (#4693) for both the
  existence and uniqueness components.

The `hchoose` hypothesis is an explicit `choosePrimeData? = some` witness,
so the `none` branch (where the mod-`p` factorisation invariant is
unavailable) is excluded; downstream callers discharge it from the same
`choosePrimeData?` chain that supplies the other partition fields. -/
theorem modPSubsetPartitionHypotheses_of_choosePrimeData
    (core : Hex.ZPoly)
    (primeData : Hex.PrimeChoiceData)
    (hcore_pos : 0 < core.degree?.getD 0)
    (hchoose : Hex.choosePrimeData? core = some primeData) :
    ModPSubsetPartitionHypotheses core primeData True True := by
  refine
    { fModP_eq := ?_
      admissible_prime := trivial
      square_free_reduction := trivial
      factors_irreducible := ?_
      exists_subset := ?_
      unique_subset := ?_ }
  · exact Hex.choosePrimeData?_fModP_eq core primeData hchoose
  · exact factors_irreducible_of_choosePrimeData_of_some core primeData hchoose hcore_pos
  · intro factor hirr hdvd
    exact (existsUnique_modPFactorSubset_of_choosePrimeData core primeData hirr hdvd hcore_pos hchoose).exists
  · intro factor S T hirr hdvd hS hT
    rcases existsUnique_modPFactorSubset_of_choosePrimeData core primeData hirr hdvd hcore_pos hchoose with
      ⟨_, _, huniq⟩
    exact (huniq S hS).trans (huniq T hT).symm

/-- A successful `choosePrimeData?` run forces a nonzero core: the selected
prime is `isGoodPrime`, which keeps `(modP p core)` nonzero, whereas
`modP p 0 = 0`. -/
theorem core_ne_zero_of_choosePrimeData
    (core : Hex.ZPoly) (primeData : Hex.PrimeChoiceData)
    (hchoose : Hex.choosePrimeData? core = some primeData) :
    core ≠ 0 := by
  letI : Hex.ZMod64.Bounds primeData.p := primeData.bounds
  intro hcore_zero
  have hgood : @Hex.isGoodPrime core primeData.p primeData.bounds = true :=
    Hex.choosePrimeData?_isGoodPrime core primeData hchoose
  have hcore_modP_iszero :
      (@Hex.ZPoly.modP primeData.p primeData.bounds core).isZero = false :=
    Hex.isGoodPrime_modP_isZero_false core primeData.p hgood
  have hzero_modP : @Hex.ZPoly.modP primeData.p primeData.bounds 0 = 0 := by
    apply Hex.DensePoly.ext_coeff
    intro k
    rw [Hex.ZPoly.coeff_modP, Hex.DensePoly.coeff_zero]
    rfl
  rw [hcore_zero, hzero_modP] at hcore_modP_iszero
  exact Bool.noConfusion hcore_modP_iszero

/-- The Mathlib images of the selected modular factors are distinct: `choosePrimeData?`
guarantees `factorsModP.toList.Nodup`, and `toMathlibPolynomial` is injective. -/
theorem toMathlibPolynomial_modPFactor_injective_of_choosePrimeData
    (core : Hex.ZPoly) (primeData : Hex.PrimeChoiceData)
    (hchoose : Hex.choosePrimeData? core = some primeData) :
    letI := primeData.bounds
    Function.Injective (fun i : ModPFactorIndex primeData =>
      HexBerlekampMathlib.toMathlibPolynomial (modPFactor primeData i)) := by
  letI := primeData.bounds
  have hprime : Hex.Nat.Prime primeData.p :=
    Hex.choosePrimeData?_prime core primeData hchoose
  obtain ⟨hzero, hfactors_eq⟩ :=
    Hex.choosePrimeData?_factorsModP_berlekamp_form core primeData hchoose
  have hform : Hex.factorsModPBerlekampForm core primeData := ⟨hprime, hzero, hfactors_eq⟩
  have hgood : @Hex.isGoodPrime core primeData.p primeData.bounds = true :=
    Hex.choosePrimeData?_isGoodPrime core primeData hchoose
  have hnodup : primeData.factorsModP.toList.Nodup :=
    factorsModP_nodup_of_factorsModPBerlekampForm core primeData hform hgood
  have hinjPoly : Function.Injective
      (HexBerlekampMathlib.toMathlibPolynomial : Hex.FpPoly primeData.p → _) :=
    HexBerlekampMathlib.fpPolyEquiv.injective
  intro i j hij
  by_contra hne
  exact modPFactor_ne_of_ne hnodup hne (hinjPoly hij)

/-- The Mathlib images of the selected modular factors are monic: `choosePrimeData?`
guarantees each `factorsModP` entry is monic, preserved by `toMathlibPolynomial`. -/
theorem toMathlibPolynomial_modPFactor_monic_of_choosePrimeData
    (core : Hex.ZPoly) (primeData : Hex.PrimeChoiceData)
    (hchoose : Hex.choosePrimeData? core = some primeData) :
    letI := primeData.bounds
    ∀ i : ModPFactorIndex primeData,
      (HexBerlekampMathlib.toMathlibPolynomial (modPFactor primeData i)).Monic := by
  letI := primeData.bounds
  have hprime : Hex.Nat.Prime primeData.p :=
    Hex.choosePrimeData?_prime core primeData hchoose
  obtain ⟨hzero, hfactors_eq⟩ :=
    Hex.choosePrimeData?_factorsModP_berlekamp_form core primeData hchoose
  have hform : Hex.factorsModPBerlekampForm core primeData := ⟨hprime, hzero, hfactors_eq⟩
  have hmonic := factorsModP_monic_of_factorsModPBerlekampForm core primeData hform
  intro i
  exact HexBerlekampMathlib.toMathlibPolynomial_monic _ (hmonic _ (Array.getElem_mem _))

/-- **modP cover (#6796).** Every selected modular factor index lies in the
representing subset of some irreducible integer divisor of `core`.

Assembled from `exists_factor_of_modPIndex` (recover an irreducible divisor `g`
whose monic mod-`p` image the indexed factor divides), the subset-partition
existence projection (a representing subset `S` for `g`), and
`mem_modPSubset_of_dvd` (the divisibility forces `i ∈ S`). -/
theorem modPFactor_index_cover
    (core : Hex.ZPoly) (primeData : Hex.PrimeChoiceData)
    (hcore_pos : 0 < core.degree?.getD 0)
    (hchoose : Hex.choosePrimeData? core = some primeData)
    (i : ModPFactorIndex primeData) :
    ∃ (g : Hex.ZPoly) (S : ModPFactorSubset primeData),
      Irreducible (HexPolyZMathlib.toPolynomial g) ∧
      g ∣ core ∧
      i ∈ S ∧
      RepresentsIntegerFactorModP primeData g S := by
  letI := primeData.bounds
  have hcore_ne : core ≠ 0 := core_ne_zero_of_choosePrimeData core primeData hchoose
  obtain ⟨g, hirr, hdvd, hfi_dvd⟩ :=
    exists_factor_of_modPIndex core hcore_ne hcore_pos primeData hchoose i
  have hpart : ModPSubsetPartitionHypotheses core primeData True True :=
    modPSubsetPartitionHypotheses_of_choosePrimeData core primeData hcore_pos hchoose
  obtain ⟨S, hS⟩ :=
    exists_modPFactorSubset_of_modPSubsetPartition hpart hirr hdvd
  have hprime : _root_.Nat.Prime primeData.p :=
    natPrime_of_hexNatPrime (Hex.choosePrimeData?_prime core primeData hchoose)
  have hf_inj :=
    toMathlibPolynomial_modPFactor_injective_of_choosePrimeData core primeData hchoose
  have hmonic :=
    toMathlibPolynomial_modPFactor_monic_of_choosePrimeData core primeData hchoose
  have hiS : i ∈ S := mem_modPSubset_of_dvd hprime hpart hf_inj hmonic hS hfi_dvd
  exact ⟨g, S, hirr, hdvd, hiS, hS⟩

/--
Non-circular `choosePrimeData`/`Hex.ZPoly.toMonicLiftData` constructor for
`HenselSubsetLiftHypotheses`.

Unlike `henselSubsetLiftHypotheses_of_choosePrimeData_henselLiftData`, this
surface consumes the lifted-side descent package directly instead of
requiring a full `HenselSubsetCorrespondenceHypotheses` value.
-/
theorem henselSubsetLiftHypotheses_of_choosePrimeData_henselLiftData_descent
    (core : Hex.ZPoly) (B : Nat)
    (primeData : Hex.PrimeChoiceData)
    (hchoose : Hex.choosePrimeData? core = some primeData)
    (hdescent :
      HenselLiftDescentHypotheses core B primeData
        (Hex.ZPoly.toMonicLiftData core B primeData) True True)
    (hlifted_of_modP :
      ∀ {factor : Hex.ZPoly} {S : ModPFactorSubset primeData},
        Irreducible (HexPolyZMathlib.toPolynomial factor) →
        factor ∣ core →
        RepresentsIntegerFactorModP primeData factor S →
        RepresentsIntegerFactorAtLift core
          (Hex.ZPoly.toMonicLiftData core B primeData) factor
          (liftedSubsetOfModPSubset primeData
            (Hex.ZPoly.toMonicLiftData core B primeData)
            hdescent.factor_count_eq S)) :
    let d := Hex.ZPoly.toMonicLiftData core B primeData
    HenselSubsetLiftHypotheses core B primeData d True True True True := by
  intro d
  have _ := hchoose
  exact
    henselSubsetLiftHypotheses_of_forwardTransport_descent
      (hadmissible := trivial)
      (hsquareFree := trivial)
      hdescent
      hlifted_of_modP

/-- **#4697 supporting lemma (HO-1).**

Assembly constructor for `HenselSubsetLiftHypotheses` at the executable
`Hex.choosePrimeData` / `Hex.henselLiftData` surface.

The constructor composes:

* `henselLiftData_liftedFactors_size_eq` (PR #4698) for `factor_count_eq`;
* the supplied forward transport `hlifted_of_modP` for `represents_lifted_of_modP`
  (sourced in practice from `henselLiftData_represents_lifted_of_modP`, landed
  in #4733, once the caller has discharged its analytic prerequisites);
* the landed descent wrapper `henselLiftData_represents_modP_of_lifted`
  (PR #4739) for `represents_modP_of_lifted`, instantiated with the supplied
  `hmod` / `hcorr` partition-and-correspondence inputs together with
  `hlifted_of_modP`.

The four proposition hooks `admissible_prime`, `square_free_reduction`,
`successful_lift`, `coprime_lift` are instantiated with `True`.

Downstream caller: `henselSubsetCorrespondence_of_modPSubsetPartition`
(line above), which composes this value with `hmod` to recover the
`HenselSubsetCorrespondenceHypotheses` package on the lifted surface. -/
theorem henselSubsetLiftHypotheses_of_choosePrimeData_henselLiftData
    (core : Hex.ZPoly) (B : Nat)
    (primeData : Hex.PrimeChoiceData)
    (hchoose : Hex.choosePrimeData? core = some primeData)
    (hmod :
      ModPSubsetPartitionHypotheses core primeData True True)
    (hcorr :
      HenselSubsetCorrespondenceHypotheses core B primeData
        (Hex.ZPoly.toMonicLiftData core B primeData) True True)
    (hlifted_of_modP :
      ∀ {factor : Hex.ZPoly} {S : ModPFactorSubset primeData},
        Irreducible (HexPolyZMathlib.toPolynomial factor) →
        factor ∣ core →
        RepresentsIntegerFactorModP primeData factor S →
        RepresentsIntegerFactorAtLift core
          (Hex.ZPoly.toMonicLiftData core B primeData) factor
          (liftedSubsetOfModPSubset primeData
            (Hex.ZPoly.toMonicLiftData core B primeData)
            (Hex.ZPoly.toMonicLiftData_liftedFactors_size_eq core B primeData)
            S)) :
    let d := Hex.ZPoly.toMonicLiftData core B primeData
    HenselSubsetLiftHypotheses core B primeData d True True True True := by
  intro d
  have _ := hchoose
  refine
    { lift_eq := rfl
      factor_count_eq := Hex.ZPoly.toMonicLiftData_liftedFactors_size_eq core B primeData
      admissible_prime := trivial
      square_free_reduction := trivial
      successful_lift := trivial
      coprime_lift := trivial
      represents_lifted_of_modP := ?_
      represents_modP_of_lifted := ?_ }
  · intro factor S hirr hdvd hrep
    exact hlifted_of_modP hirr hdvd hrep
  · intro factor T hirr hdvd hT
    exact henselLiftData_represents_modP_of_lifted hmod hcorr
      (Hex.ZPoly.toMonicLiftData_liftedFactors_size_eq core B primeData)
      hlifted_of_modP hirr hdvd hT

/-- **#5689 supporting lemma (HO-1 successful branch).**

Successful-branch constructor for the lifted Hensel subset correspondence at
the witness-form `Hex.choosePrimeData?` boundary.

The explicit `hchoose` hypothesis selects the analyzable
`Hex.choosePrimeData? core = some primeData` branch, supplying the mod-`p`
subset partition.  The Hensel-lift obligations remain packaged as
an explicit `HenselSubsetLiftHypotheses` input, so callers do not have to use
an arbitrary-prime correspondence assumption. -/
theorem henselSubsetCorrespondenceHypotheses_of_choosePrimeData_success
    (core : Hex.ZPoly) (B : Nat)
    (primeData : Hex.PrimeChoiceData)
    (hcore_pos : 0 < core.degree?.getD 0)
    (hchoose : Hex.choosePrimeData? core = some primeData)
    (hlift :
      HenselSubsetLiftHypotheses core B primeData
        (Hex.ZPoly.toMonicLiftData core B primeData)
        True True True True) :
    let d := Hex.ZPoly.toMonicLiftData core B primeData
    HenselSubsetCorrespondenceHypotheses core B primeData d True True := by
  intro d
  exact
    henselSubsetCorrespondence_of_modPSubsetPartition
      (modPSubsetPartitionHypotheses_of_choosePrimeData core primeData hcore_pos hchoose)
      hlift

/-- **#5689 supporting lemma (HO-1 successful branch).**

Caller-facing wrapper for the common successful-branch shape: compose the
`choosePrimeData? = some ...` mod-`p` partition with a non-circular lifted-side
descent package and explicit forward Hensel transport to obtain the standard
`HenselSubsetCorrespondenceHypotheses` surface. -/
theorem henselSubsetCorrespondenceHypotheses_of_choosePrimeData_success_descent
    (core : Hex.ZPoly) (B : Nat)
    (primeData : Hex.PrimeChoiceData)
    (hcore_pos : 0 < core.degree?.getD 0)
    (hchoose : Hex.choosePrimeData? core = some primeData)
    (hdescent :
      HenselLiftDescentHypotheses core B primeData
        (Hex.ZPoly.toMonicLiftData core B primeData) True True)
    (hlifted_of_modP :
      ∀ {factor : Hex.ZPoly} {S : ModPFactorSubset primeData},
        Irreducible (HexPolyZMathlib.toPolynomial factor) →
        factor ∣ core →
        RepresentsIntegerFactorModP primeData factor S →
        RepresentsIntegerFactorAtLift core
          (Hex.ZPoly.toMonicLiftData core B primeData) factor
          (liftedSubsetOfModPSubset primeData
            (Hex.ZPoly.toMonicLiftData core B primeData)
            hdescent.factor_count_eq S)) :
    let d := Hex.ZPoly.toMonicLiftData core B primeData
    HenselSubsetCorrespondenceHypotheses core B primeData d True True := by
  intro d
  exact
    henselSubsetCorrespondenceHypotheses_of_choosePrimeData_success core B primeData
      hcore_pos hchoose
      (henselSubsetLiftHypotheses_of_choosePrimeData_henselLiftData_descent
        core B primeData hchoose hdescent hlifted_of_modP)

/-- **#6683 supporting lemma (HO-1), outer-bound successful branch.**

Successful-descent specialisation of
`henselSubsetCorrespondenceHypotheses_of_choosePrimeData_success_descent` at the
precision count consumed by the slow exhaustive branch of `Hex.factor f`. -/
theorem henselSubsetCorrespondenceHypotheses_outerBound_of_choosePrimeData
    (f : Hex.ZPoly)
    (primeData : Hex.PrimeChoiceData)
    (hcore_pos :
      0 < (Hex.normalizeForFactor f).squareFreeCore.degree?.getD 0)
    (hchoose :
      Hex.choosePrimeData? (Hex.normalizeForFactor f).squareFreeCore = some primeData)
    (hdescent :
      HenselLiftDescentHypotheses (Hex.normalizeForFactor f).squareFreeCore
        (Hex.ZPoly.exhaustiveLiftBound (Hex.normalizeForFactor f).squareFreeCore
          (Hex.ZPoly.defaultFactorCoeffBound f)) primeData
        (Hex.ZPoly.toMonicLiftData (Hex.normalizeForFactor f).squareFreeCore
          (Hex.ZPoly.exhaustiveLiftBound (Hex.normalizeForFactor f).squareFreeCore
            (Hex.ZPoly.defaultFactorCoeffBound f)) primeData) True True)
    (hlifted_of_modP :
      ∀ {factor : Hex.ZPoly} {S : ModPFactorSubset primeData},
        Irreducible (HexPolyZMathlib.toPolynomial factor) →
        factor ∣ (Hex.normalizeForFactor f).squareFreeCore →
        RepresentsIntegerFactorModP primeData factor S →
        RepresentsIntegerFactorAtLift (Hex.normalizeForFactor f).squareFreeCore
          (Hex.ZPoly.toMonicLiftData (Hex.normalizeForFactor f).squareFreeCore
            (Hex.ZPoly.exhaustiveLiftBound (Hex.normalizeForFactor f).squareFreeCore
              (Hex.ZPoly.defaultFactorCoeffBound f)) primeData) factor
          (liftedSubsetOfModPSubset primeData
            (Hex.ZPoly.toMonicLiftData (Hex.normalizeForFactor f).squareFreeCore
              (Hex.ZPoly.exhaustiveLiftBound (Hex.normalizeForFactor f).squareFreeCore
                (Hex.ZPoly.defaultFactorCoeffBound f)) primeData)
            hdescent.factor_count_eq S)) :
    let core := (Hex.normalizeForFactor f).squareFreeCore
    let B := Hex.ZPoly.defaultFactorCoeffBound f
    let d := Hex.ZPoly.toMonicLiftData core (Hex.ZPoly.exhaustiveLiftBound core B)
      primeData
    HenselSubsetCorrespondenceHypotheses core (Hex.ZPoly.exhaustiveLiftBound core B)
      primeData d True True :=
  henselSubsetCorrespondenceHypotheses_of_choosePrimeData_success_descent
    _ _ primeData hcore_pos hchoose hdescent hlifted_of_modP

/-- **#6354 supporting lemma (HO-1 successful branch).**

Successful-branch sibling of `liftedFactorSubsetPartition_of_choosePrimeData`.
The partition-cover fields still come from the localized partition analytic
obligation, but the embedded Hensel subset correspondence is sourced from the
non-circular descent/forward-transport path. -/
theorem liftedFactorSubsetPartition_of_choosePrimeData_success_descent
    (core : Hex.ZPoly) (B : Nat)
    (primeData : Hex.PrimeChoiceData)
    (hcore_pos : 0 < core.degree?.getD 0)
    (hchoose : Hex.choosePrimeData? core = some primeData)
    (hcore_sqfree : Squarefree (HexPolyZMathlib.toPolynomial core))
    (hdescent :
      HenselLiftDescentHypotheses core B primeData
        (Hex.ZPoly.toMonicLiftData core B primeData) True True)
    (hlifted_of_modP :
      ∀ {factor : Hex.ZPoly} {S : ModPFactorSubset primeData},
        Irreducible (HexPolyZMathlib.toPolynomial factor) →
        factor ∣ core →
        RepresentsIntegerFactorModP primeData factor S →
        RepresentsIntegerFactorAtLift core
          (Hex.ZPoly.toMonicLiftData core B primeData) factor
          (liftedSubsetOfModPSubset primeData
            (Hex.ZPoly.toMonicLiftData core B primeData)
            hdescent.factor_count_eq S))
    (hinitial :
      InitialLiftedFactorSubsetPartitionEvidence core
        (Hex.ZPoly.toMonicLiftData core B primeData)) :
    let d := Hex.ZPoly.toMonicLiftData core B primeData
    LiftedFactorSubsetPartition core d Finset.univ core := by
    obtain ⟨hcover, hdisj, huniq, _⟩ :=
      liftedFactorSubsetPartition_initial_fields hinitial
    exact
      { toHenselSubsetCorrespondenceRest :=
          henselSubsetCorrespondenceRest_initial
            (henselSubsetCorrespondenceHypotheses_of_choosePrimeData_success_descent
              core B primeData hcore_pos hchoose hdescent hlifted_of_modP)
        target_squarefree := hcore_sqfree
        cover := by
          intro i hi
          exact hcover hi
        pairwise_disjoint := by
          intro f g S T hirr_f hdvd_f _ hSrep hirr_g hdvd_g _ hTrep hnoassoc
          exact hdisj (f := f) (g := g) (S := S) (T := T)
            hirr_f hdvd_f hSrep hirr_g hdvd_g hTrep hnoassoc
        unique_up_to_associated := by
          intro f g S T hirr_f hdvd_f _ hSrep hirr_g hdvd_g _ hTrep hassoc
          exact huniq (f := f) (g := g) (S := S) (T := T)
            hirr_f hdvd_f hSrep hirr_g hdvd_g hTrep hassoc
        support_subset_of_dvd_recombinationCandidate := by
          intro f S T hirr hdvd_target _ hcore_lc_one hdvd_cand _ hSrep
          have hdvd_rec :
              f ∣ liftedRecoveryCandidate core
                (Hex.ZPoly.toMonicLiftData core B primeData) T := by
            rw [liftedRecoveryCandidate.eq_recombinationCandidate_of_lc_one
              hcore_lc_one, recombinationCandidate_eq_liftedFactorProductCandidate]
            exact hdvd_cand
          exact
            liftedFactorSubsetPartition_initial_support_subset_of_dvd_liftedRecoveryCandidate_of_choosePrimeData
              core B primeData hinitial hirr hdvd_target hdvd_rec hSrep
        support_subset_of_dvd_liftedRecoveryCandidate := by
          intro f S T hirr hdvd_target _ hdvd_cand _ hSrep
          exact
            liftedFactorSubsetPartition_initial_support_subset_of_dvd_liftedRecoveryCandidate_of_choosePrimeData
              core B primeData hinitial hirr hdvd_target hdvd_cand hSrep
        liftedRecoveryCandidate_eq := by
          intro f S hirr hdvd_target _ hSrep
          exact
            liftedFactorSubsetPartition_initial_liftedRecoveryCandidate_eq_of_choosePrimeData
              core B primeData hinitial hirr hdvd_target hSrep }

end

end HexBerlekampZassenhausMathlib
