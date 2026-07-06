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

public import HexBerlekampZassenhausMathlib.RecombinationSplit
import all HexBerlekampZassenhausMathlib.PublicSurface
import all HexBerlekampZassenhausMathlib.ModPFactor
import all HexBerlekampZassenhausMathlib.LiftedFactor
import all HexBerlekampZassenhausMathlib.M1Recovery
import all HexBerlekampZassenhausMathlib.RecombinationSplit

public section
set_option backward.proofsInPublic true

/-!
This module collects `recombinationCandidate` and the candidate-equals-factor lemmas.
-/

namespace HexBerlekampZassenhausMathlib

noncomputable section

open Polynomial

/-- The executable recombination candidate associated to a lifted-factor
subset: this is the `Hex.ZPoly` value that the recombination search compares
against the running target via `shouldRecordPolynomialFactor` /
`exactQuotient?`.  Definitionally equal to the inline expression used inside
`Hex.recombinationSearchModAux`. -/
def recombinationCandidate (d : Hex.LiftData) (S : LiftedFactorSubset d) :
    Hex.ZPoly :=
  Hex.normalizeFactorSign <|
    Hex.ZPoly.primitivePart <|
      Hex.centeredLiftPoly
        (Array.polyProduct (liftedSubsetSelectedList d S).toArray)
        (d.p ^ d.k)

/-- The executable-list recombination candidate agrees with the proof-side
product candidate. -/
theorem recombinationCandidate_eq_liftedFactorProductCandidate
    (d : Hex.LiftData) (S : LiftedFactorSubset d) :
    recombinationCandidate d S = liftedFactorProductCandidate d S := by
  unfold recombinationCandidate liftedFactorProductCandidate
  rw [polyProduct_liftedSubsetSelectedList_eq_liftedFactorProduct]

namespace liftedRecoveryCandidate

/-- On monic cores, the recovered non-monic candidate is the executable
unscaled recombination candidate. -/
theorem eq_recombinationCandidate_of_lc_one
    {core : Hex.ZPoly} {d : Hex.LiftData} {S : LiftedFactorSubset d}
    (hlead : Hex.DensePoly.leadingCoeff core = (1 : Int)) :
    liftedRecoveryCandidate core d S = recombinationCandidate d S := by
  rw [eq_productCandidate_of_lc_one hlead,
    recombinationCandidate_eq_liftedFactorProductCandidate]

end liftedRecoveryCandidate

/-- Every list is the all-unselected split of itself: `([], xs) ∈ subsetSplits xs`. -/
theorem subsetSplits_nil_left_mem (xs : List Hex.ZPoly) :
    (([], xs) : List Hex.ZPoly × List Hex.ZPoly) ∈ Hex.subsetSplits xs := by
  induction xs with
  | nil => exact Hex.subsetSplits_nil_mem
  | cons x xs ih => exact Hex.subsetSplits_cons_right_mem ih

/-- Membership bridge between the two recombination enumerators: every
`(selected, rest)` partition the size-ordered enumerator
`subsetsOfSizeWithComplement` produces is also an (order-preserving) member of
the full `subsetSplits` enumeration.  Both enumerators range over exactly the
order-preserving partitions of the list; only their visitation order differs.
This lets the size-ordered (smart) search reuse the `subsetSplits` subset
machinery. -/
theorem subsetsOfSizeWithComplement_mem_subsetSplits
    {xs sel rest : List Hex.ZPoly} {k : Nat}
    (h : (sel, rest) ∈ Hex.subsetsOfSizeWithComplement xs k) :
    (sel, rest) ∈ Hex.subsetSplits xs := by
  induction xs generalizing sel rest k with
  | nil =>
      cases k with
      | zero =>
          rw [show Hex.subsetsOfSizeWithComplement ([] : List Hex.ZPoly) 0 = [([], [])]
            from rfl] at h
          simp only [List.mem_singleton, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          exact Hex.subsetSplits_nil_mem
      | succ k =>
          rw [show Hex.subsetsOfSizeWithComplement ([] : List Hex.ZPoly) (k + 1) = []
            from rfl] at h
          simp at h
  | cons x xs ih =>
      cases k with
      | zero =>
          rw [show Hex.subsetsOfSizeWithComplement (x :: xs) 0 = [([], x :: xs)]
            from rfl] at h
          simp only [List.mem_singleton, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          exact subsetSplits_nil_left_mem (x :: xs)
      | succ k =>
          rw [show Hex.subsetsOfSizeWithComplement (x :: xs) (k + 1) =
              (Hex.subsetsOfSizeWithComplement xs k).map (fun sc => (x :: sc.1, sc.2)) ++
                (Hex.subsetsOfSizeWithComplement xs (k + 1)).map
                  (fun sc => (sc.1, x :: sc.2)) from rfl] at h
          rcases List.mem_append.mp h with hleft | hright
          · rcases List.mem_map.mp hleft with ⟨⟨a, b⟩, hmem, heq⟩
            simp only [Prod.mk.injEq] at heq
            obtain ⟨rfl, rfl⟩ := heq
            exact Hex.subsetSplits_cons_left_mem (ih hmem)
          · rcases List.mem_map.mp hright with ⟨⟨a, b⟩, hmem, heq⟩
            simp only [Prod.mk.injEq] at heq
            obtain ⟨rfl, rfl⟩ := heq
            exact Hex.subsetSplits_cons_right_mem (ih hmem)

/-- The head-forced size-ordered split lies in `subsetSplitsWithFirst`: this is
the executable enumeration shape the size-ordered search actually iterates (the
head lifted factor forced into the selected component, the tail partitioned by
`subsetsOfSizeWithComplement`). -/
theorem subsetsOfSizeWithComplement_cons_mem_subsetSplitsWithFirst
    {head : Hex.ZPoly} {tail sc_sel sc_rest : List Hex.ZPoly} {k : Nat}
    (h : (sc_sel, sc_rest) ∈ Hex.subsetsOfSizeWithComplement tail k) :
    (head :: sc_sel, sc_rest) ∈ Hex.subsetSplitsWithFirst (head :: tail) := by
  unfold Hex.subsetSplitsWithFirst
  exact List.mem_map.mpr
    ⟨(sc_sel, sc_rest), subsetsOfSizeWithComplement_mem_subsetSplits h, rfl⟩

/-- Identify a split produced by the size-ordered (smart) recombination
enumerator with a lifted-factor subset.

At the top level the smart search forces the head lifted factor into the
selected component and partitions the remaining tail by
`subsetsOfSizeWithComplement`.  Every such split `(head :: sc_sel, sc_rest)` is
the `(selected, rejected)` list partition of a lifted-factor subset `S`: its
selected sublist is `liftedSubsetSelectedList d S`, hence its product is the
proof-side `liftedFactorProduct d S`, and the executable scaled candidate built
from the selected product (the candidate `scaledRecombinationSmartCandLoop`
forms, with `coreLc = leadingCoeff core` and `modulus = d.p ^ d.k`) is exactly
the proof-side `liftedRecoveryCandidate core d S`.

Existence of the identifying subset needs no distinctness hypothesis — the
subset is recovered from the mask over the matched *index* list, which is
intrinsically `Nodup`.  Distinctness of the lifted factors is what pins the
subset *uniquely*; that is supplied separately by
`subsetsOfSizeWithComplement_liftedFactors_exists_unique_subset`. -/
theorem subsetsOfSizeWithComplement_liftedFactors_exists_subset
    (core : Hex.ZPoly) (d : Hex.LiftData)
    {head : Hex.ZPoly} {tail : List Hex.ZPoly}
    (hloc : d.liftedFactors.toList = head :: tail)
    {sc_sel sc_rest : List Hex.ZPoly} {k : Nat}
    (hmem : (sc_sel, sc_rest) ∈ Hex.subsetsOfSizeWithComplement tail k) :
    ∃ S : LiftedFactorSubset d,
      head :: sc_sel = liftedSubsetSelectedList d S ∧
      sc_rest = liftedSubsetRejectedList d S ∧
      Array.polyProduct (head :: sc_sel).toArray = liftedFactorProduct d S ∧
      Hex.normalizeFactorSign (Hex.ZPoly.primitivePart
          (Hex.ZPoly.dilate (Hex.DensePoly.leadingCoeff core)
            (Hex.centeredLiftPoly (Array.polyProduct (head :: sc_sel).toArray)
              (d.p ^ d.k))))
        = liftedRecoveryCandidate core d S := by
  classical
  have hpos : 0 < d.liftedFactors.size := by
    rw [← Array.length_toList, hloc]; simp
  haveI : Nonempty (LiftedFactorIndex d) := ⟨⟨0, hpos⟩⟩
  have hne : (Finset.univ : LiftedFactorSubset d).Nonempty := Finset.univ_nonempty
  -- A Boolean mask over the tail, from the `subsetSplits` enumeration.
  have hsplit : (sc_sel, sc_rest) ∈ Hex.subsetSplits tail :=
    subsetsOfSizeWithComplement_mem_subsetSplits hmem
  obtain ⟨mask, hmask_len, hsel, hrest⟩ := subsetSplits_mem_exists_mask hsplit
  -- Recover the subset from the mask, matched against the full universe of indices.
  obtain ⟨T, -, -, hTsel, hTrej⟩ :=
    liftedSubsetSelectedList_eq_mask_partition_of_matches
      (LiftedFactorListMatches.univ d) hne hloc mask hmask_len
  have hsel_eq : head :: sc_sel = liftedSubsetSelectedList d T := by rw [hTsel, hsel]
  refine ⟨T, hsel_eq, ?_, ?_, ?_⟩
  · rw [liftedSubsetRejectedList_eq_liftedSubsetSelectedList_sdiff, hTrej]; exact hrest
  · rw [hsel_eq, polyProduct_liftedSubsetSelectedList_eq_liftedFactorProduct]
  · unfold liftedRecoveryCandidate
    rw [hsel_eq, polyProduct_liftedSubsetSelectedList_eq_liftedFactorProduct]

/-- The selected-list map of a lifted-factor subset determines the subset when
the lifted factors are distinct: `liftedSubsetSelectedList d` is injective in
`S` whenever `liftedFactor d` is injective.  This is the distinctness step the
`RecoveredScaledSearch.covers` completeness argument relies on, discharged for
`toMonicLiftData core B primeData` (squarefree `core`) by the existing
mod-`p`-nodup lifted-factor injectivity lemmas. -/
theorem liftedSubsetSelectedList_injective
    {d : Hex.LiftData} (hinj : Function.Injective (liftedFactor d))
    {S S' : LiftedFactorSubset d}
    (h : liftedSubsetSelectedList d S = liftedSubsetSelectedList d S') :
    S = S' := by
  rw [liftedSubsetSelectedList_eq_filter_map, liftedSubsetSelectedList_eq_filter_map] at h
  have hfilter := List.map_injective_iff.mpr hinj h
  ext i
  have hi : i ∈ (List.finRange d.liftedFactors.size).filter (fun j => decide (j ∈ S)) ↔
      i ∈ (List.finRange d.liftedFactors.size).filter (fun j => decide (j ∈ S')) := by
    rw [hfilter]
  simpa only [List.mem_filter, List.mem_finRange, true_and, decide_eq_true_eq] using hi

/-- Full identification of a size-ordered (smart) enumerator split with its
lifted-factor subset: when the lifted factors are distinct the subset `S` is
*unique*, so the executable candidate the search forms is identified with the
single proof-side `liftedRecoveryCandidate core d S`.

This packages `subsetsOfSizeWithComplement_liftedFactors_exists_subset` with the
distinctness-driven uniqueness, taking `Function.Injective (liftedFactor d)` as
an explicit hypothesis (the same one `RecoveredScaledSearch.covers` carries). -/
theorem subsetsOfSizeWithComplement_liftedFactors_exists_unique_subset
    (core : Hex.ZPoly) (d : Hex.LiftData)
    (hinj : Function.Injective (liftedFactor d))
    {head : Hex.ZPoly} {tail : List Hex.ZPoly}
    (hloc : d.liftedFactors.toList = head :: tail)
    {sc_sel sc_rest : List Hex.ZPoly} {k : Nat}
    (hmem : (sc_sel, sc_rest) ∈ Hex.subsetsOfSizeWithComplement tail k) :
    ∃ S : LiftedFactorSubset d,
      head :: sc_sel = liftedSubsetSelectedList d S ∧
      sc_rest = liftedSubsetRejectedList d S ∧
      Array.polyProduct (head :: sc_sel).toArray = liftedFactorProduct d S ∧
      Hex.normalizeFactorSign (Hex.ZPoly.primitivePart
          (Hex.ZPoly.dilate (Hex.DensePoly.leadingCoeff core)
            (Hex.centeredLiftPoly (Array.polyProduct (head :: sc_sel).toArray)
              (d.p ^ d.k))))
        = liftedRecoveryCandidate core d S ∧
      ∀ S' : LiftedFactorSubset d,
        head :: sc_sel = liftedSubsetSelectedList d S' → S' = S := by
  obtain ⟨S, hsel, hrej, hprod, hcand⟩ :=
    subsetsOfSizeWithComplement_liftedFactors_exists_subset core d hloc hmem
  exact ⟨S, hsel, hrej, hprod, hcand,
    fun S' hS' => liftedSubsetSelectedList_injective hinj (hS'.symm.trans hsel)⟩

/-- Matched-state generalisation of
`subsetsOfSizeWithComplement_liftedFactors_exists_subset`, for the recursive
size-ordered coverage walk: at an intermediate state whose running local-factor
list matches a sub-universe `J` (`LiftedFactorListMatches d J localFactors`), a
head-forced size-ordered split of the tail is the `(selected, rejected)` list
partition of a subset `T ⊆ J` containing `J.min'`.  The rejected component is the
selected list of `J \ T` (the natural form for the descent into `scaledRecombinationSmartAux`
on the rest list), and the product / candidate identities specialise as before.

This is the shape `#8413` consumes when walking
`scaledRecombinationSmartAux`/`SizeLoop`/`CandLoop`, where the running
`localFactors` is the matched list of the remaining indices `J`, not the full
universe. -/
theorem subsetsOfSizeWithComplement_liftedFactors_exists_subset_of_matches
    (core : Hex.ZPoly) (d : Hex.LiftData)
    {J : LiftedFactorSubset d} {localFactors : List Hex.ZPoly}
    (hmatches : LiftedFactorListMatches d J localFactors) (hne : J.Nonempty)
    {head : Hex.ZPoly} {tail : List Hex.ZPoly}
    (hloc : localFactors = head :: tail)
    {sc_sel sc_rest : List Hex.ZPoly} {k : Nat}
    (hmem : (sc_sel, sc_rest) ∈ Hex.subsetsOfSizeWithComplement tail k) :
    ∃ T : LiftedFactorSubset d,
      T ⊆ J ∧ J.min' hne ∈ T ∧
      head :: sc_sel = liftedSubsetSelectedList d T ∧
      sc_rest = liftedSubsetSelectedList d (J \ T) ∧
      Array.polyProduct (head :: sc_sel).toArray = liftedFactorProduct d T ∧
      Hex.normalizeFactorSign (Hex.ZPoly.primitivePart
          (Hex.ZPoly.dilate (Hex.DensePoly.leadingCoeff core)
            (Hex.centeredLiftPoly (Array.polyProduct (head :: sc_sel).toArray)
              (d.p ^ d.k))))
        = liftedRecoveryCandidate core d T := by
  have hsplit : (sc_sel, sc_rest) ∈ Hex.subsetSplits tail :=
    subsetsOfSizeWithComplement_mem_subsetSplits hmem
  obtain ⟨mask, hmask_len, hsel, hrest⟩ := subsetSplits_mem_exists_mask hsplit
  obtain ⟨T, hTJ, hmin, hTsel, hTrej⟩ :=
    liftedSubsetSelectedList_eq_mask_partition_of_matches hmatches hne hloc mask hmask_len
  have hsel_eq : head :: sc_sel = liftedSubsetSelectedList d T := by rw [hTsel, hsel]
  refine ⟨T, hTJ, hmin, hsel_eq, ?_, ?_, ?_⟩
  · rw [hTrej]; exact hrest
  · rw [hsel_eq, polyProduct_liftedSubsetSelectedList_eq_liftedFactorProduct]
  · unfold liftedRecoveryCandidate
    rw [hsel_eq, polyProduct_liftedSubsetSelectedList_eq_liftedFactorProduct]

/--
On a monic core, the partition's lifted-recovery equality upgrades to the
executable recombination-candidate equality consumed by the search recursion.

The partition's `liftedRecoveryCandidate_eq` field soundly pins the recovered
candidate `liftedRecoveryCandidate core d S` to the represented factor `f`; on a
monic core, `liftedRecoveryCandidate.eq_recombinationCandidate_of_lc_one`
rewrites that into the unscaled executable `recombinationCandidate d S`. This is
the sound replacement for passing `RepresentsIntegerFactorAtLift` to the old
scaled-product modular recovery lemmas.
-/
theorem LiftedFactorSubsetPartition.recombinationCandidate_eq
    {core target f : Hex.ZPoly} {d : Hex.LiftData} {J S : LiftedFactorSubset d}
    (hpartition : LiftedFactorSubsetPartition core d J target)
    (hcore_monic : Hex.DensePoly.Monic core)
    (hirr : Irreducible (HexPolyZMathlib.toPolynomial f))
    (hf_dvd_target : f ∣ target)
    (hSJ : S ⊆ J)
    (hrep : RepresentsIntegerFactorAtLift core d f S) :
    recombinationCandidate d S = f := by
  have hlead : Hex.DensePoly.leadingCoeff core = (1 : Int) := hcore_monic
  rw [← liftedRecoveryCandidate.eq_recombinationCandidate_of_lc_one hlead]
  exact hpartition.liftedRecoveryCandidate_eq hirr hf_dvd_target hSJ hrep

/--
Structural support containment for a divisor of an executable recombination
candidate under a lifted-factor subset partition.

This is the projection consumed by the cover-at-min assembler: an irreducible
integer factor represented by `S` cannot divide the candidate built from `T`
unless all local factors in `S` were selected by `T`.
-/
theorem representingSubset_subset_of_dvd_recombinationCandidate
    {core target f : Hex.ZPoly} {d : Hex.LiftData}
    {J T S : LiftedFactorSubset d}
    (_hcore_ne : core ≠ 0)
    (hcore_monic : Hex.DensePoly.Monic core)
    (_hprecision : 2 * Hex.ZPoly.defaultFactorCoeffBound core < d.p ^ d.k)
    (hpartition : LiftedFactorSubsetPartition core d J target)
    (hTJ : T ⊆ J)
    (hirr : Irreducible (HexPolyZMathlib.toPolynomial f))
    (hfactor_dvd_target : f ∣ target)
    (hfactor_dvd_candidate : f ∣ recombinationCandidate d T)
    (hSJ : S ⊆ J)
    (hrep : RepresentsIntegerFactorAtLift core d f S) :
    S ⊆ T := by
  apply hpartition.support_subset_of_dvd_recombinationCandidate
    hirr hfactor_dvd_target hTJ
  · exact hcore_monic
  · rw [← recombinationCandidate_eq_liftedFactorProductCandidate]
    exact hfactor_dvd_candidate
  · exact hSJ
  · exact hrep

/-- Abstract-bound variant of
`representingSubset_subset_of_dvd_recombinationCandidate`: takes
`_B' : Nat`, `_hvalid : ∀ i, (f.coeff i).natAbs ≤ _B'`, and
`_hprecision : 2 * _B' < d.p ^ d.k` in place of the core-shape
`defaultFactorCoeffBound core` precision constraint.  Both the
abstract bound and the precision hypothesis are vestigial here (the
proof body delegates to the structural support field of
`LiftedFactorSubsetPartition`, which never consumes precision); they
are threaded purely for API parity with the broader `_of_bound`
propagation chain. -/
theorem representingSubset_subset_of_dvd_recombinationCandidate_of_bound
    {core target f : Hex.ZPoly} {d : Hex.LiftData}
    {J T S : LiftedFactorSubset d}
    (_B' : Nat)
    (_hvalid : ∀ i, (f.coeff i).natAbs ≤ _B')
    (_hcore_ne : core ≠ 0)
    (hcore_monic : Hex.DensePoly.Monic core)
    (_hprecision : 2 * _B' < d.p ^ d.k)
    (hpartition : LiftedFactorSubsetPartition core d J target)
    (hTJ : T ⊆ J)
    (hirr : Irreducible (HexPolyZMathlib.toPolynomial f))
    (hfactor_dvd_target : f ∣ target)
    (hfactor_dvd_candidate : f ∣ recombinationCandidate d T)
    (hSJ : S ⊆ J)
    (hrep : RepresentsIntegerFactorAtLift core d f S) :
    S ⊆ T := by
  apply hpartition.support_subset_of_dvd_recombinationCandidate
    hirr hfactor_dvd_target hTJ
  · exact hcore_monic
  · rw [← recombinationCandidate_eq_liftedFactorProductCandidate]
    exact hfactor_dvd_candidate
  · exact hSJ
  · exact hrep

/-- Structural support containment for a divisor of a recovered recombination
candidate under a lifted-factor subset partition.

This is the recovered-coordinate sibling of
`representingSubset_subset_of_dvd_recombinationCandidate`: it projects the
partition's sound recovered support field directly, without routing through the
unscaled product-candidate surface. -/
theorem representingSubset_subset_of_dvd_liftedRecoveryCandidate
    {core target f : Hex.ZPoly} {d : Hex.LiftData}
    {J T S : LiftedFactorSubset d}
    (_hcore_ne : core ≠ 0)
    (_hcore_monic : Hex.DensePoly.Monic core)
    (_hprecision : 2 * Hex.ZPoly.defaultFactorCoeffBound core < d.p ^ d.k)
    (hpartition : LiftedFactorSubsetPartition core d J target)
    (hTJ : T ⊆ J)
    (hirr : Irreducible (HexPolyZMathlib.toPolynomial f))
    (hfactor_dvd_target : f ∣ target)
    (hfactor_dvd_candidate : f ∣ liftedRecoveryCandidate core d T)
    (hSJ : S ⊆ J)
    (hrep : RepresentsIntegerFactorAtLift core d f S) :
    S ⊆ T := by
  exact hpartition.support_subset_of_dvd_liftedRecoveryCandidate
    hirr hfactor_dvd_target hTJ hfactor_dvd_candidate hSJ hrep

/-- Abstract-bound variant of
`representingSubset_subset_of_dvd_liftedRecoveryCandidate`: takes
`_B' : Nat`, `_hvalid : ∀ i, (f.coeff i).natAbs ≤ _B'`, and
`_hprecision : 2 * _B' < d.p ^ d.k` in place of the core-shape
`defaultFactorCoeffBound core` precision constraint.  The proof body delegates
directly to the recovered support field of `LiftedFactorSubsetPartition`. -/
theorem representingSubset_subset_of_dvd_liftedRecoveryCandidate_of_bound
    {core target f : Hex.ZPoly} {d : Hex.LiftData}
    {J T S : LiftedFactorSubset d}
    (_B' : Nat)
    (_hvalid : ∀ i, (f.coeff i).natAbs ≤ _B')
    (_hcore_ne : core ≠ 0)
    (_hcore_monic : Hex.DensePoly.Monic core)
    (_hprecision : 2 * _B' < d.p ^ d.k)
    (hpartition : LiftedFactorSubsetPartition core d J target)
    (hTJ : T ⊆ J)
    (hirr : Irreducible (HexPolyZMathlib.toPolynomial f))
    (hfactor_dvd_target : f ∣ target)
    (hfactor_dvd_candidate : f ∣ liftedRecoveryCandidate core d T)
    (hSJ : S ⊆ J)
    (hrep : RepresentsIntegerFactorAtLift core d f S) :
    S ⊆ T := by
  exact hpartition.support_subset_of_dvd_liftedRecoveryCandidate
    hirr hfactor_dvd_target hTJ hfactor_dvd_candidate hSJ hrep

/-- Primitive + positive-leading-core variant of
`representingSubset_subset_of_dvd_recombinationCandidate` (#4646 chain).

The original `hcore_monic` parameter is vestigial in the monic version (the
proof body never uses it), so the primitive variant has identical body and
threads `hcore_primitive` and `hcore_lc_pos` purely for API uniformity with
the rest of the primitive-core chain. -/
theorem representingSubset_subset_of_dvd_recombinationCandidate_of_primitive_pos_lc_core
    {core target f : Hex.ZPoly} {d : Hex.LiftData}
    {J T S : LiftedFactorSubset d}
    (_hcore_ne : core ≠ 0)
    (_hcore_primitive : Hex.ZPoly.Primitive core)
    (_hcore_lc_pos : 0 < Hex.DensePoly.leadingCoeff core)
    (hcore_monic : Hex.DensePoly.Monic core)
    (_hprecision : 2 * Hex.ZPoly.defaultFactorCoeffBound core < d.p ^ d.k)
    (hpartition : LiftedFactorSubsetPartition core d J target)
    (hTJ : T ⊆ J)
    (hirr : Irreducible (HexPolyZMathlib.toPolynomial f))
    (hfactor_dvd_target : f ∣ target)
    (hfactor_dvd_candidate : f ∣ recombinationCandidate d T)
    (hSJ : S ⊆ J)
    (hrep : RepresentsIntegerFactorAtLift core d f S) :
    S ⊆ T := by
  apply hpartition.support_subset_of_dvd_recombinationCandidate
    hirr hfactor_dvd_target hTJ
  · exact hcore_monic
  · rw [← recombinationCandidate_eq_liftedFactorProductCandidate]
    exact hfactor_dvd_candidate
  · exact hSJ
  · exact hrep

/-- Abstract-bound variant of
`representingSubset_subset_of_dvd_recombinationCandidate_of_primitive_pos_lc_core`:
takes `_B' : Nat`, `_hvalid : ∀ i, (f.coeff i).natAbs ≤ _B'`, and
`_hprecision : 2 * _B' < d.p ^ d.k` in place of the core-shape
`defaultFactorCoeffBound core` precision constraint.  Both the
abstract bound and the precision hypothesis are vestigial here; they
are threaded purely for API parity with the broader `_of_bound`
propagation chain. -/
theorem representingSubset_subset_of_dvd_recombinationCandidate_of_primitive_pos_lc_core_of_bound
    {core target f : Hex.ZPoly} {d : Hex.LiftData}
    {J T S : LiftedFactorSubset d}
    (_B' : Nat)
    (_hvalid : ∀ i, (f.coeff i).natAbs ≤ _B')
    (_hcore_ne : core ≠ 0)
    (_hcore_primitive : Hex.ZPoly.Primitive core)
    (_hcore_lc_pos : 0 < Hex.DensePoly.leadingCoeff core)
    (hcore_monic : Hex.DensePoly.Monic core)
    (_hprecision : 2 * _B' < d.p ^ d.k)
    (hpartition : LiftedFactorSubsetPartition core d J target)
    (hTJ : T ⊆ J)
    (hirr : Irreducible (HexPolyZMathlib.toPolynomial f))
    (hfactor_dvd_target : f ∣ target)
    (hfactor_dvd_candidate : f ∣ recombinationCandidate d T)
    (hSJ : S ⊆ J)
    (hrep : RepresentsIntegerFactorAtLift core d f S) :
    S ⊆ T := by
  apply hpartition.support_subset_of_dvd_recombinationCandidate
    hirr hfactor_dvd_target hTJ
  · exact hcore_monic
  · rw [← recombinationCandidate_eq_liftedFactorProductCandidate]
    exact hfactor_dvd_candidate
  · exact hSJ
  · exact hrep

/-- Primitive + positive-leading-core support containment for recovered
recombination candidates.

The support conclusion is supplied by the recovered support field of
`LiftedFactorSubsetPartition`. -/
theorem representingSubset_subset_of_dvd_liftedRecoveryCandidate_of_primitive_pos_lc_core
    {core target f : Hex.ZPoly} {d : Hex.LiftData}
    {J T S : LiftedFactorSubset d}
    (_hcore_ne : core ≠ 0)
    (_hcore_primitive : Hex.ZPoly.Primitive core)
    (_hcore_lc_pos : 0 < Hex.DensePoly.leadingCoeff core)
    (_hprecision : 2 * Hex.ZPoly.defaultFactorCoeffBound core < d.p ^ d.k)
    (_htarget_dvd_core : target ∣ core)
    (hpartition : LiftedFactorSubsetPartition core d J target)
    (hTJ : T ⊆ J)
    (hirr : Irreducible (HexPolyZMathlib.toPolynomial f))
    (hfactor_dvd_target : f ∣ target)
    (_hfactor_prim : Hex.ZPoly.content f = 1)
    (_hfactor_norm : Hex.normalizeFactorSign f = f)
    (hfactor_dvd_candidate : f ∣ liftedRecoveryCandidate core d T)
    (hSJ : S ⊆ J)
    (hrep : RepresentsIntegerFactorAtLift core d f S) :
    S ⊆ T := by
  exact hpartition.support_subset_of_dvd_liftedRecoveryCandidate
    hirr hfactor_dvd_target hTJ hfactor_dvd_candidate hSJ hrep

/-- Abstract-bound variant of
`representingSubset_subset_of_dvd_liftedRecoveryCandidate_of_primitive_pos_lc_core`.
The bound and precision hypotheses are threaded for API parity with nearby
support wrappers; the proof body delegates to the partition
support field. -/
theorem representingSubset_subset_of_dvd_liftedRecoveryCandidate_of_primitive_pos_lc_core_of_bound
    {core target f : Hex.ZPoly} {d : Hex.LiftData}
    {J T S : LiftedFactorSubset d}
    (_B' : Nat)
    (_hvalid : ∀ i, (f.coeff i).natAbs ≤ _B')
    (_hcore_ne : core ≠ 0)
    (_hcore_primitive : Hex.ZPoly.Primitive core)
    (_hcore_lc_pos : 0 < Hex.DensePoly.leadingCoeff core)
    (_hprecision : 2 * _B' < d.p ^ d.k)
    (_htarget_dvd_core : target ∣ core)
    (hpartition : LiftedFactorSubsetPartition core d J target)
    (hTJ : T ⊆ J)
    (hirr : Irreducible (HexPolyZMathlib.toPolynomial f))
    (hfactor_dvd_target : f ∣ target)
    (_hfactor_prim : Hex.ZPoly.content f = 1)
    (_hfactor_norm : Hex.normalizeFactorSign f = f)
    (hfactor_dvd_candidate : f ∣ liftedRecoveryCandidate core d T)
    (hSJ : S ⊆ J)
    (hrep : RepresentsIntegerFactorAtLift core d f S) :
    S ⊆ T := by
  exact hpartition.support_subset_of_dvd_liftedRecoveryCandidate
    hirr hfactor_dvd_target hTJ hfactor_dvd_candidate hSJ hrep

/-- Abstract-bound variant of
`centeredLiftPoly_scaledLiftedFactorProduct_eq_factor_of_recovery`:
takes `B' : Nat`, `hvalid : ∀ i, (factor.coeff i).natAbs ≤ B'`, and
`hprecision : 2 * B' < d.p ^ d.k` in place of the core-shape
`defaultFactorCoeffBound core` precision constraint. -/
theorem centeredLiftPoly_scaledLiftedFactorProduct_eq_factor_of_recovery_of_bound
    {core factor : Hex.ZPoly} {d : Hex.LiftData} {S : LiftedFactorSubset d}
    (B' : Nat)
    (hvalid : ∀ i, (factor.coeff i).natAbs ≤ B')
    (hscaled :
      Hex.ZPoly.reduceModPow (scaledLiftedFactorProduct core d S) d.p d.k =
        Hex.ZPoly.reduceModPow factor d.p d.k)
    (hprecision : 2 * B' < d.p ^ d.k) :
    Hex.centeredLiftPoly (scaledLiftedFactorProduct core d S) (d.p ^ d.k) =
      factor := by
  have h := centeredLift_scaledLiftedFactorProduct_eq_of_mignottePrecision_of_bound
    B' hvalid hscaled hprecision
  rwa [centeredLiftPoly_reduceModPow_eq _ _ _ d.p_pos] at h

/-- The A2 recovery equality reformulated against the executable centred-lift
of the **scaled** lifted product, ready to feed downstream packaging that
relates the scaled centered lift to the unscaled `recombinationCandidate`.

This is the cleanest form in which the proof-side recovery is expressed for
later integration with executable-side normalisation reasoning (which removes
the `lc(core)` scale and chooses a sign).

This is a thin wrapper over
`centeredLiftPoly_scaledLiftedFactorProduct_eq_factor_of_recovery_of_bound`
that instantiates `B' := defaultFactorCoeffBound core` and discharges
`hvalid` via `defaultFactorCoeffBound_valid core hcore_ne factor hdvd`. -/
theorem centeredLiftPoly_scaledLiftedFactorProduct_eq_factor_of_recovery
    {core factor : Hex.ZPoly} {d : Hex.LiftData} {S : LiftedFactorSubset d}
    (hcore_ne : core ≠ 0)
    (hdvd : factor ∣ core)
    (hscaled :
      Hex.ZPoly.reduceModPow (scaledLiftedFactorProduct core d S) d.p d.k =
        Hex.ZPoly.reduceModPow factor d.p d.k)
    (hprecision : 2 * Hex.ZPoly.defaultFactorCoeffBound core < d.p ^ d.k) :
    Hex.centeredLiftPoly (scaledLiftedFactorProduct core d S) (d.p ^ d.k) =
      factor :=
  centeredLiftPoly_scaledLiftedFactorProduct_eq_factor_of_recovery_of_bound
    (Hex.ZPoly.defaultFactorCoeffBound core)
    (defaultFactorCoeffBound_valid core hcore_ne factor hdvd)
    hscaled hprecision

/-- **M1 recovery-witness constructor (primitivePart-aware).**

Build a `RecoveredAtLiftM1 core d factor S` from genuine core-coordinate recovery
data, in the *honest* scale coordinate.  The recovery input is the proportional
congruence

  `ℓf · (∏ S) ≡ c · factor (mod p^k)`,   `ℓf = leadingCoeff core`,   `c > 0`,

which is the true shape of the M1 recovery: the `ℓf`-scaled lifted product lands on
a *constant multiple* of the primitive integer factor (the constant `c` is the
leading coefficient of the cofactor), not on `factor` itself.  Together with a
monic-coordinate witness `monicFactor` congruent to the selected lifted product and
dividing `monicTarget core p k`, the factor's primitivity, and a Mignotte precision
bound on `c · factor`, this recovers `factor` as the primitive part of the centred
lift.

This replaces the earlier `_of_recovery` constructor whose `hscaled` premise asked
for the *strong* congruence `reduceModPow (scaledLiftedFactorProduct …) =
reduceModPow factor`, which is provably **false** for proper factors with a non-unit
cofactor leading coefficient (the scale carries the spurious constant `c`).  The
`primitivePart` in `RecoveredAtLiftM1.recovered_eq` is exactly what strips that
constant, so the honest proportional congruence above is the satisfiable premise.

This is the core-coordinate (`scale`/`monicTarget`) analogue of
`recoveredLiftOfRepresents`.  `recovered_eq` is discharged by
`centeredLiftPoly_eq_of_reduceModPow_eq` on the target `c · factor` (its centred
lift is `scale c factor` exactly), followed by `primitivePart (scale c factor) =
primitivePart factor = factor` (`c > 0`, `factor` primitive).  `congr` and
`monic_dvd` are recorded verbatim.  No `dilate` and no `(toMonic core).monic`
divisibility: the `monicTarget` coordinate already is `core`'s own coordinate. -/
def recoveredAtLiftM1_of_recovery
    {core factor monicFactor : Hex.ZPoly} {d : Hex.LiftData} {S : LiftedFactorSubset d}
    (c : Int) (hc_pos : 0 < c)
    (hcongr :
      Hex.ZPoly.reduceModPow (liftedFactorProduct d S) d.p d.k =
        Hex.ZPoly.reduceModPow monicFactor d.p d.k)
    (hmonic_dvd : monicFactor ∣ Hex.ZPoly.monicTarget core d.p d.k)
    (hhonest :
      Hex.ZPoly.congr
        (Hex.DensePoly.scale (Hex.DensePoly.leadingCoeff core) (liftedFactorProduct d S))
        (Hex.DensePoly.scale c factor)
        (d.p ^ d.k))
    (hfactor_prim : Hex.ZPoly.primitivePart factor = factor)
    (B' : Nat)
    (hvalid : ∀ i, ((Hex.DensePoly.scale c factor).coeff i).natAbs ≤ B')
    (hprecision : 2 * B' < d.p ^ d.k) :
    RecoveredAtLiftM1 core d factor S where
  monicFactor := monicFactor
  congr := hcongr
  monic_dvd := hmonic_dvd
  recovered_eq := by
    have hp_pos : 0 < d.p := d.p_pos
    have hpk : 0 < d.p ^ d.k := Nat.pow_pos hp_pos
    -- `∏S ≡ monicFactor (mod p^k)`, from the reduced-form congruence.
    have hcongr_poly :
        Hex.ZPoly.congr (liftedFactorProduct d S) monicFactor (d.p ^ d.k) := by
      have hf := Hex.ZPoly.congr_reduceModPow (liftedFactorProduct d S) d.p d.k hpk
      have hg := Hex.ZPoly.congr_reduceModPow monicFactor d.p d.k hpk
      rw [hcongr] at hf
      exact Hex.ZPoly.congr_trans _ _ _ _ (Hex.ZPoly.congr_symm _ _ _ hf) hg
    -- `ℓf·monicFactor ≡ ℓf·∏S ≡ c·factor (mod p^k)`.
    have hscale_eq :
        Hex.ZPoly.reduceModPow
            (Hex.DensePoly.scale (Hex.DensePoly.leadingCoeff core) monicFactor) d.p d.k
          = Hex.ZPoly.reduceModPow (Hex.DensePoly.scale c factor) d.p d.k :=
      Hex.ZPoly.reduceModPow_eq_of_congr _ _ d.p d.k
        (Hex.ZPoly.congr_trans _ _ _ _
          (scale_congr_of_congr (Hex.DensePoly.leadingCoeff core) _ _ _
            (Hex.ZPoly.congr_symm _ _ _ hcongr_poly))
          hhonest)
    -- Recover `c·factor` exactly, then strip the positive constant via primitivePart.
    have hcl :
        Hex.centeredLiftPoly
            (Hex.ZPoly.reduceModPow
              (Hex.DensePoly.scale (Hex.DensePoly.leadingCoeff core) monicFactor) d.p d.k)
            (d.p ^ d.k) =
          Hex.DensePoly.scale c factor :=
      Hex.centeredLiftPoly_eq_of_reduceModPow_eq
        (Hex.DensePoly.scale c factor)
        (Hex.DensePoly.scale (Hex.DensePoly.leadingCoeff core) monicFactor)
        d.p d.k B' hvalid hprecision hscale_eq
    rw [hcl, primitivePart_scale_of_pos hc_pos factor, hfactor_prim]

/-- Abstract-bound recovered-coordinate equality: if the variable-dilated
centred lifted-factor product is congruent to `factor` modulo the Hensel
modulus, then Mignotte precision recovers `factor` exactly. -/
theorem centeredLiftPoly_dilatedCenteredLiftProduct_eq_factor_of_bound
    {core factor : Hex.ZPoly} {d : Hex.LiftData} {S : LiftedFactorSubset d}
    (B' : Nat)
    (hvalid : ∀ i, (factor.coeff i).natAbs ≤ B')
    (hcong :
      Hex.ZPoly.reduceModPow
          (Hex.ZPoly.dilate (Hex.DensePoly.leadingCoeff core)
            (Hex.centeredLiftPoly (liftedFactorProduct d S) (d.p ^ d.k)))
          d.p d.k =
        Hex.ZPoly.reduceModPow factor d.p d.k)
    (hprecision : 2 * B' < d.p ^ d.k) :
    Hex.centeredLiftPoly
        (Hex.ZPoly.dilate (Hex.DensePoly.leadingCoeff core)
          (Hex.centeredLiftPoly (liftedFactorProduct d S) (d.p ^ d.k)))
        (d.p ^ d.k) =
      factor := by
  have h :=
    Hex.centeredLiftPoly_eq_of_reduceModPow_eq
      factor
      (Hex.ZPoly.dilate (Hex.DensePoly.leadingCoeff core)
        (Hex.centeredLiftPoly (liftedFactorProduct d S) (d.p ^ d.k)))
      d.p d.k B' hvalid hprecision hcong
  rwa [centeredLiftPoly_reduceModPow_eq _ _ _ d.p_pos] at h

/-- Abstract-bound exact recovery for the corrected non-monic candidate
`liftedRecoveryCandidate`.  The equality hypothesis is stated in the coordinate
system used by the executable search: centre the selected lifted product first,
then dilate by `lc(core)`. -/
theorem liftedRecoveryCandidate_eq_factor_of_recovery_of_bound
    {core factor : Hex.ZPoly} {d : Hex.LiftData} {S : LiftedFactorSubset d}
    (_B' : Nat)
    (_hvalid : ∀ i, (factor.coeff i).natAbs ≤ _B')
    (hfactor_prim : Hex.ZPoly.content factor = 1)
    (hfactor_norm : Hex.normalizeFactorSign factor = factor)
    (hrecovered :
      Hex.ZPoly.dilate (Hex.DensePoly.leadingCoeff core)
          (Hex.centeredLiftPoly (liftedFactorProduct d S) (d.p ^ d.k)) =
        factor)
    (_hprecision : 2 * _B' < d.p ^ d.k) :
    liftedRecoveryCandidate core d S = factor := by
  unfold liftedRecoveryCandidate
  rw [hrecovered]
  have hprimitive : Hex.ZPoly.primitivePart factor = factor :=
    Hex.ZPoly.primitivePart_eq_self_of_primitive factor
      (by simpa [Hex.ZPoly.Primitive] using hfactor_prim)
  rw [hprimitive]
  exact hfactor_norm

/-- Default-bound wrapper for
`liftedRecoveryCandidate_eq_factor_of_recovery_of_bound`. -/
theorem liftedRecoveryCandidate_eq_factor_of_recovery
    {core factor : Hex.ZPoly} {d : Hex.LiftData} {S : LiftedFactorSubset d}
    (hcore_ne : core ≠ 0)
    (hdvd : factor ∣ core)
    (hfactor_prim : Hex.ZPoly.content factor = 1)
    (hfactor_norm : Hex.normalizeFactorSign factor = factor)
    (hrecovered :
      Hex.ZPoly.dilate (Hex.DensePoly.leadingCoeff core)
          (Hex.centeredLiftPoly (liftedFactorProduct d S) (d.p ^ d.k)) =
        factor)
    (hprecision : 2 * Hex.ZPoly.defaultFactorCoeffBound core < d.p ^ d.k) :
    liftedRecoveryCandidate core d S = factor :=
  liftedRecoveryCandidate_eq_factor_of_recovery_of_bound
    (Hex.ZPoly.defaultFactorCoeffBound core)
    (defaultFactorCoeffBound_valid core hcore_ne factor hdvd)
    hfactor_prim hfactor_norm hrecovered hprecision

private theorem densePoly_scale_one_int (f : Hex.ZPoly) :
    Hex.DensePoly.scale (1 : Int) f = f := by
  apply Hex.DensePoly.ext_coeff
  intro n
  rw [Hex.DensePoly.coeff_scale (1 : Int) f n (by simp)]
  simp

/-- Abstract-bound variant of
`recombinationCandidate_eq_factor_of_recovery_of_monic_core`: takes
`B' : Nat`, `hvalid : ∀ i, (factor.coeff i).natAbs ≤ B'`, and
`hprecision : 2 * B' < d.p ^ d.k` in place of the core-shape
`defaultFactorCoeffBound core` precision constraint.  The proof mirrors
the core-shape original but invokes
`centeredLiftPoly_scaledLiftedFactorProduct_eq_factor_of_recovery_of_bound`
in place of the core-shape recovery theorem. -/
theorem recombinationCandidate_eq_factor_of_recovery_of_monic_core_of_bound
    {core factor : Hex.ZPoly} {d : Hex.LiftData} {S : LiftedFactorSubset d}
    (B' : Nat)
    (hvalid : ∀ i, (factor.coeff i).natAbs ≤ B')
    (_hcore_ne : core ≠ 0)
    (hcore_monic : Hex.DensePoly.Monic core)
    (hfactor_prim : Hex.ZPoly.content factor = 1)
    (hfactor_norm : Hex.normalizeFactorSign factor = factor)
    (_hirr : Irreducible (HexPolyZMathlib.toPolynomial factor))
    (hscaled :
      Hex.ZPoly.reduceModPow (scaledLiftedFactorProduct core d S) d.p d.k =
        Hex.ZPoly.reduceModPow factor d.p d.k)
    (hprecision : 2 * B' < d.p ^ d.k) :
    recombinationCandidate d S = factor := by
  have hlead : Hex.DensePoly.leadingCoeff core = (1 : Int) := by
    simpa [Hex.DensePoly.Monic] using hcore_monic
  have hscaled_eq :
      scaledLiftedFactorProduct core d S = liftedFactorProduct d S := by
    unfold scaledLiftedFactorProduct
    rw [hlead]
    exact densePoly_scale_one_int (liftedFactorProduct d S)
  have hcenter :
      Hex.centeredLiftPoly (liftedFactorProduct d S) (d.p ^ d.k) = factor := by
    have h :=
      centeredLiftPoly_scaledLiftedFactorProduct_eq_factor_of_recovery_of_bound
        B' hvalid hscaled hprecision
    rwa [hscaled_eq] at h
  unfold recombinationCandidate
  rw [polyProduct_liftedSubsetSelectedList_eq_liftedFactorProduct, hcenter]
  have hprimitive :
      Hex.ZPoly.primitivePart factor = factor :=
    Hex.ZPoly.primitivePart_eq_self_of_primitive factor
      (by simpa [Hex.ZPoly.Primitive] using hfactor_prim)
  rw [hprimitive]
  exact hfactor_norm

/--
Under a monic core hypothesis, the scaled recovery theorem identifies the
unscaled executable recombination candidate with the represented integer
factor.  This is the core recovery statement; the older
`recombinationCandidate_eq_factor_of_recovery` wrapper also accepts the
executable record-filter hypothesis needed by some callers.

This is a thin wrapper over
`recombinationCandidate_eq_factor_of_recovery_of_monic_core_of_bound`
that instantiates `B' := defaultFactorCoeffBound core` and discharges
`hvalid` via `defaultFactorCoeffBound_valid core hcore_ne factor hdvd`.
-/
theorem recombinationCandidate_eq_factor_of_recovery_of_monic_core
    {core factor : Hex.ZPoly} {d : Hex.LiftData} {S : LiftedFactorSubset d}
    (hcore_ne : core ≠ 0)
    (hcore_monic : Hex.DensePoly.Monic core)
    (hdvd : factor ∣ core)
    (hfactor_prim : Hex.ZPoly.content factor = 1)
    (hfactor_norm : Hex.normalizeFactorSign factor = factor)
    (_hirr : Irreducible (HexPolyZMathlib.toPolynomial factor))
    (hscaled :
      Hex.ZPoly.reduceModPow (scaledLiftedFactorProduct core d S) d.p d.k =
        Hex.ZPoly.reduceModPow factor d.p d.k)
    (hprecision : 2 * Hex.ZPoly.defaultFactorCoeffBound core < d.p ^ d.k) :
    recombinationCandidate d S = factor :=
  recombinationCandidate_eq_factor_of_recovery_of_monic_core_of_bound
    (Hex.ZPoly.defaultFactorCoeffBound core)
    (defaultFactorCoeffBound_valid core hcore_ne factor hdvd)
    hcore_ne hcore_monic hfactor_prim hfactor_norm _hirr hscaled hprecision

/-- Abstract-bound variant of
`recombinationCandidate_eq_factor_of_recovery`: takes `B' : Nat`,
`hvalid : ∀ i, (factor.coeff i).natAbs ≤ B'`, and
`hprecision : 2 * B' < d.p ^ d.k` in place of the core-shape
`defaultFactorCoeffBound core` precision constraint.  Delegates to
`recombinationCandidate_eq_factor_of_recovery_of_monic_core_of_bound`. -/
theorem recombinationCandidate_eq_factor_of_recovery_of_bound
    {core factor : Hex.ZPoly} {d : Hex.LiftData} {S : LiftedFactorSubset d}
    (B' : Nat)
    (hvalid : ∀ i, (factor.coeff i).natAbs ≤ B')
    (hcore_ne : core ≠ 0)
    (hcore_monic : Hex.DensePoly.Monic core)
    (_hcore_record : Hex.shouldRecordPolynomialFactor core = true)
    (hfactor_prim : Hex.ZPoly.content factor = 1)
    (hfactor_norm : Hex.normalizeFactorSign factor = factor)
    (_hirr : Irreducible (HexPolyZMathlib.toPolynomial factor))
    (hscaled :
      Hex.ZPoly.reduceModPow (scaledLiftedFactorProduct core d S) d.p d.k =
        Hex.ZPoly.reduceModPow factor d.p d.k)
    (hprecision : 2 * B' < d.p ^ d.k) :
    recombinationCandidate d S = factor :=
  recombinationCandidate_eq_factor_of_recovery_of_monic_core_of_bound
    B' hvalid hcore_ne hcore_monic hfactor_prim hfactor_norm _hirr hscaled hprecision

/--
Under a monic core hypothesis, the scaled recovery theorem identifies the
unscaled executable recombination candidate with the represented integer
factor.

This is a thin wrapper over
`recombinationCandidate_eq_factor_of_recovery_of_bound` that instantiates
`B' := defaultFactorCoeffBound core` and discharges `hvalid` via
`defaultFactorCoeffBound_valid core hcore_ne factor hdvd`.
-/
theorem recombinationCandidate_eq_factor_of_recovery
    {core factor : Hex.ZPoly} {d : Hex.LiftData} {S : LiftedFactorSubset d}
    (hcore_ne : core ≠ 0)
    (hcore_monic : Hex.DensePoly.Monic core)
    (_hcore_record : Hex.shouldRecordPolynomialFactor core = true)
    (hdvd : factor ∣ core)
    (hfactor_prim : Hex.ZPoly.content factor = 1)
    (hfactor_norm : Hex.normalizeFactorSign factor = factor)
    (_hirr : Irreducible (HexPolyZMathlib.toPolynomial factor))
    (hscaled :
      Hex.ZPoly.reduceModPow (scaledLiftedFactorProduct core d S) d.p d.k =
        Hex.ZPoly.reduceModPow factor d.p d.k)
    (hprecision : 2 * Hex.ZPoly.defaultFactorCoeffBound core < d.p ^ d.k) :
    recombinationCandidate d S = factor :=
  recombinationCandidate_eq_factor_of_recovery_of_bound
    (Hex.ZPoly.defaultFactorCoeffBound core)
    (defaultFactorCoeffBound_valid core hcore_ne factor hdvd)
    hcore_ne hcore_monic _hcore_record hfactor_prim hfactor_norm _hirr hscaled hprecision

/-- Abstract-bound variant of
`recombinationCandidate_eq_factor_of_henselSubsetCorrespondence`: takes
`B' : Nat`, `hvalid : ∀ i, (factor.coeff i).natAbs ≤ B'`, and
`hprecision : 2 * B' < d.p ^ d.k` in place of the core-shape
`defaultFactorCoeffBound core` precision constraint.  Delegates to
`recombinationCandidate_eq_factor_of_recovery_of_bound`. -/
theorem recombinationCandidate_eq_factor_of_henselSubsetCorrespondence_of_bound
    {core factor : Hex.ZPoly} {B : Nat} {primeData : Hex.PrimeChoiceData}
    {d : Hex.LiftData} {admissiblePrime successfulLift : Prop}
    {S : LiftedFactorSubset d}
    (_h :
      HenselSubsetCorrespondenceHypotheses core B primeData d
        admissiblePrime successfulLift)
    (B' : Nat)
    (hvalid : ∀ i, (factor.coeff i).natAbs ≤ B')
    (hcore_ne : core ≠ 0)
    (hcore_monic : Hex.DensePoly.Monic core)
    (hcore_record : Hex.shouldRecordPolynomialFactor core = true)
    (hirr : Irreducible (HexPolyZMathlib.toPolynomial factor))
    (hfactor_prim : Hex.ZPoly.content factor = 1)
    (hfactor_norm : Hex.normalizeFactorSign factor = factor)
    (hscaled :
      Hex.ZPoly.reduceModPow (scaledLiftedFactorProduct core d S) d.p d.k =
        Hex.ZPoly.reduceModPow factor d.p d.k)
    (hprecision : 2 * B' < d.p ^ d.k) :
    recombinationCandidate d S = factor :=
  recombinationCandidate_eq_factor_of_recovery_of_bound
    B' hvalid hcore_ne hcore_monic hcore_record hfactor_prim hfactor_norm hirr
    hscaled hprecision

/--
Hensel-correspondence wrapper for the monic-core recovery theorem.

Once a proof-side subset is known to represent an irreducible integer divisor
at the Hensel lift, the executable recombination candidate is exactly that
factor under the monic/primitive/sign-normalised hypotheses required by the
centered-lift recovery bound.

This is a thin wrapper over
`recombinationCandidate_eq_factor_of_henselSubsetCorrespondence_of_bound`
that instantiates `B' := defaultFactorCoeffBound core` and discharges
`hvalid` via `defaultFactorCoeffBound_valid core hcore_ne factor hdvd`.
-/
theorem recombinationCandidate_eq_factor_of_henselSubsetCorrespondence
    {core factor : Hex.ZPoly} {B : Nat} {primeData : Hex.PrimeChoiceData}
    {d : Hex.LiftData} {admissiblePrime successfulLift : Prop}
    {S : LiftedFactorSubset d}
    (_h :
      HenselSubsetCorrespondenceHypotheses core B primeData d
        admissiblePrime successfulLift)
    (hcore_ne : core ≠ 0)
    (hcore_monic : Hex.DensePoly.Monic core)
    (hcore_record : Hex.shouldRecordPolynomialFactor core = true)
    (hirr : Irreducible (HexPolyZMathlib.toPolynomial factor))
    (hdvd : factor ∣ core)
    (hfactor_prim : Hex.ZPoly.content factor = 1)
    (hfactor_norm : Hex.normalizeFactorSign factor = factor)
    (hscaled :
      Hex.ZPoly.reduceModPow (scaledLiftedFactorProduct core d S) d.p d.k =
        Hex.ZPoly.reduceModPow factor d.p d.k)
    (hprecision : 2 * Hex.ZPoly.defaultFactorCoeffBound core < d.p ^ d.k) :
    recombinationCandidate d S = factor :=
  recombinationCandidate_eq_factor_of_henselSubsetCorrespondence_of_bound
    _h
    (Hex.ZPoly.defaultFactorCoeffBound core)
    (defaultFactorCoeffBound_valid core hcore_ne factor hdvd)
    hcore_ne hcore_monic hcore_record hirr hfactor_prim hfactor_norm hscaled hprecision

/-- Abstract-bound variant of
`scaledRecombinationCandidate_eq_factor_of_recovery`: takes `B' : Nat`,
`hvalid : ∀ i, (factor.coeff i).natAbs ≤ B'`, and
`hprecision : 2 * B' < d.p ^ d.k` in place of the core-shape
`defaultFactorCoeffBound core` precision constraint.  The body mirrors
the original but invokes the `_of_bound` centered-lift recovery theorem
instead of the core-shape one.  The original core-shape theorem is a
wrapper around this variant. -/
theorem scaledRecombinationCandidate_eq_factor_of_recovery_of_bound
    {core factor : Hex.ZPoly} {d : Hex.LiftData} {S : LiftedFactorSubset d}
    (B' : Nat)
    (hvalid : ∀ i, (factor.coeff i).natAbs ≤ B')
    (_hcore_ne : core ≠ 0)
    (hfactor_prim : Hex.ZPoly.content factor = 1)
    (hfactor_norm : Hex.normalizeFactorSign factor = factor)
    (hscaled :
      Hex.ZPoly.reduceModPow (scaledLiftedFactorProduct core d S) d.p d.k =
        Hex.ZPoly.reduceModPow factor d.p d.k)
    (hprecision : 2 * B' < d.p ^ d.k) :
    scaledRecombinationCandidate core d S = factor := by
  unfold scaledRecombinationCandidate
  rw [centeredLiftPoly_scaledLiftedFactorProduct_eq_factor_of_recovery_of_bound
        B' hvalid hscaled hprecision]
  have hprimitive : Hex.ZPoly.primitivePart factor = factor :=
    Hex.ZPoly.primitivePart_eq_self_of_primitive factor
      (by simpa [Hex.ZPoly.Primitive] using hfactor_prim)
  rw [hprimitive]
  exact hfactor_norm

/--
Primitive non-monic recovery supporting lemma: the scaled recombination candidate
equals the represented integer `factor` under primitive/sign-normalised
hypotheses on `factor` plus the standard Mignotte-precision and representation
hypotheses. This is the corrected first recovery step for the primitive
non-monic recombination chain (parent #4638, replaces stale #4643).

Unlike `recombinationCandidate_eq_factor_of_recovery_of_monic_core`, this
theorem does *not* require `Monic core` and does *not* route through the
leading-coefficient collapse `scaledLiftedFactorProduct = liftedFactorProduct`.
The inner equality is supplied directly by
`centeredLiftPoly_scaledLiftedFactorProduct_eq_factor_of_recovery`;
`primitivePart_eq_self_of_primitive` and the supplied `normalizeFactorSign`
fixed-point discharge the outer normalisation pipeline.

Downstream callers (#4644, #4646, #4647, #4648) call this in place of the
monic-core recovery when the core hypotheses are
`core ≠ 0 ∧ Primitive core ∧ 0 < leadingCoeff core`; the primitive/sign
hypotheses on `factor` are supplied by their primitive-factor packaging step.

This is a thin wrapper over
`scaledRecombinationCandidate_eq_factor_of_recovery_of_bound` that
instantiates `B' := defaultFactorCoeffBound core` and discharges
`hvalid` via `defaultFactorCoeffBound_valid core hcore_ne factor hdvd`.
-/
theorem scaledRecombinationCandidate_eq_factor_of_recovery
    {core factor : Hex.ZPoly} {d : Hex.LiftData} {S : LiftedFactorSubset d}
    (hcore_ne : core ≠ 0)
    (hdvd : factor ∣ core)
    (hfactor_prim : Hex.ZPoly.content factor = 1)
    (hfactor_norm : Hex.normalizeFactorSign factor = factor)
    (hscaled :
      Hex.ZPoly.reduceModPow (scaledLiftedFactorProduct core d S) d.p d.k =
        Hex.ZPoly.reduceModPow factor d.p d.k)
    (hprecision : 2 * Hex.ZPoly.defaultFactorCoeffBound core < d.p ^ d.k) :
    scaledRecombinationCandidate core d S = factor :=
  scaledRecombinationCandidate_eq_factor_of_recovery_of_bound
    (Hex.ZPoly.defaultFactorCoeffBound core)
    (defaultFactorCoeffBound_valid core hcore_ne factor hdvd)
    hcore_ne hfactor_prim hfactor_norm hscaled hprecision

/-- Abstract-bound variant of
`scaledRecombinationCandidate_eq_factor_of_henselSubsetCorrespondence`:
takes `B' : Nat`, `hvalid : ∀ i, (factor.coeff i).natAbs ≤ B'`, and
`hprecision : 2 * B' < d.p ^ d.k` in place of the core-shape
`defaultFactorCoeffBound core` precision constraint.  Body is a
one-line delegation to
`scaledRecombinationCandidate_eq_factor_of_recovery_of_bound`. -/
theorem scaledRecombinationCandidate_eq_factor_of_henselSubsetCorrespondence_of_bound
    {core factor : Hex.ZPoly} {B : Nat} {primeData : Hex.PrimeChoiceData}
    {d : Hex.LiftData} {admissiblePrime successfulLift : Prop}
    {S : LiftedFactorSubset d}
    (_h :
      HenselSubsetCorrespondenceHypotheses core B primeData d
        admissiblePrime successfulLift)
    (B' : Nat)
    (hvalid : ∀ i, (factor.coeff i).natAbs ≤ B')
    (hcore_ne : core ≠ 0)
    (hfactor_prim : Hex.ZPoly.content factor = 1)
    (hfactor_norm : Hex.normalizeFactorSign factor = factor)
    (hscaled :
      Hex.ZPoly.reduceModPow (scaledLiftedFactorProduct core d S) d.p d.k =
        Hex.ZPoly.reduceModPow factor d.p d.k)
    (hprecision : 2 * B' < d.p ^ d.k) :
    scaledRecombinationCandidate core d S = factor :=
  scaledRecombinationCandidate_eq_factor_of_recovery_of_bound
    B' hvalid hcore_ne hfactor_prim hfactor_norm hscaled hprecision

/--
Hensel-correspondence wrapper for the primitive-core scaled recovery theorem.

Primitive-core analogue of
`recombinationCandidate_eq_factor_of_henselSubsetCorrespondence`: once a
proof-side subset is known to represent an irreducible integer divisor at the
Hensel lift, the *scaled* recombination candidate is exactly that factor under
the primitive/sign-normalised hypotheses required by the centered-lift
recovery bound.

This is a thin wrapper over
`scaledRecombinationCandidate_eq_factor_of_henselSubsetCorrespondence_of_bound`
that instantiates `B' := defaultFactorCoeffBound core` and discharges
`hvalid` via `defaultFactorCoeffBound_valid core hcore_ne factor hdvd`.
-/
theorem scaledRecombinationCandidate_eq_factor_of_henselSubsetCorrespondence
    {core factor : Hex.ZPoly} {B : Nat} {primeData : Hex.PrimeChoiceData}
    {d : Hex.LiftData} {admissiblePrime successfulLift : Prop}
    {S : LiftedFactorSubset d}
    (_h :
      HenselSubsetCorrespondenceHypotheses core B primeData d
        admissiblePrime successfulLift)
    (hcore_ne : core ≠ 0)
    (hdvd : factor ∣ core)
    (hfactor_prim : Hex.ZPoly.content factor = 1)
    (hfactor_norm : Hex.normalizeFactorSign factor = factor)
    (hscaled :
      Hex.ZPoly.reduceModPow (scaledLiftedFactorProduct core d S) d.p d.k =
        Hex.ZPoly.reduceModPow factor d.p d.k)
    (hprecision : 2 * Hex.ZPoly.defaultFactorCoeffBound core < d.p ^ d.k) :
    scaledRecombinationCandidate core d S = factor :=
  scaledRecombinationCandidate_eq_factor_of_henselSubsetCorrespondence_of_bound
    _h (Hex.ZPoly.defaultFactorCoeffBound core)
    (defaultFactorCoeffBound_valid core hcore_ne factor hdvd)
    hcore_ne hfactor_prim hfactor_norm hscaled hprecision

end

end HexBerlekampZassenhausMathlib
