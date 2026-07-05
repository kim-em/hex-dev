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

public import HexBerlekampZassenhausMathlib.M1Recovery
import all HexBerlekampZassenhausMathlib.PublicSurface
import all HexBerlekampZassenhausMathlib.ModPFactor
import all HexBerlekampZassenhausMathlib.LiftedFactor
import all HexBerlekampZassenhausMathlib.M1Recovery

public section
set_option backward.proofsInPublic true
set_option backward.privateInPublic true

/-!
This module collects the mask/list combinatorics bridging `Finset` subsets to executable enumeration.
-/

namespace HexBerlekampZassenhausMathlib

noncomputable section

open Polynomial

/-! ### LiftedFactorSubset → executable recombination split

The executable recombination search at the lifted-factor surface enumerates
order-preserving partitions of `d.liftedFactors.toList` via
`Hex.subsetSplitsWithFirst`.  These helpers transport a proof-side
`LiftedFactorSubset d` (a `Finset` of indices) into a concrete `(selected,
rest)` partition that lies in the executable enumeration, with the
selected/rejected lists ordered by their original `d.liftedFactors` index.

The product equality matches the executable
`Array.polyProduct selected.toArray` against the proof-side
`liftedFactorProduct d S` after transport to `Polynomial ℤ`, where
multiplication is commutative and the order difference between the
index-preserving partition and `S.toList` becomes a permutation.
-/

/-- Boolean indicator vector for `S`, indexed by the same `Fin` order as
`d.liftedFactors.toList`. -/
def liftedSubsetMask (d : Hex.LiftData) (S : LiftedFactorSubset d) : List Bool :=
  (List.finRange d.liftedFactors.size).map fun i => decide (i ∈ S)

theorem liftedSubsetMask_length (d : Hex.LiftData) (S : LiftedFactorSubset d) :
    (liftedSubsetMask d S).length = d.liftedFactors.toList.length := by
  unfold liftedSubsetMask; simp

/-- The list of lifted factors selected by `S`, ordered by their original
`d.liftedFactors` index. -/
def liftedSubsetSelectedList (d : Hex.LiftData) (S : LiftedFactorSubset d) :
    List Hex.ZPoly :=
  (d.liftedFactors.toList.zip (liftedSubsetMask d S)).filterMap fun p =>
    if p.2 then some p.1 else none

/-- The list of lifted factors not selected by `S`, ordered by their original
`d.liftedFactors` index. -/
def liftedSubsetRejectedList (d : Hex.LiftData) (S : LiftedFactorSubset d) :
    List Hex.ZPoly :=
  (d.liftedFactors.toList.zip (liftedSubsetMask d S)).filterMap fun p =>
    if p.2 then none else some p.1

/-- Generalised partition lemma: for any list paired with a Boolean mask of
matching length, the order-preserving selected/rejected partition lies in
`Hex.subsetSplits`. -/
private theorem subsetSplits_zip_filterMap_partition :
    ∀ (xs : List Hex.ZPoly) (mask : List Bool), mask.length = xs.length →
      ((xs.zip mask).filterMap (fun p => if p.2 then some p.1 else none),
        (xs.zip mask).filterMap (fun p => if p.2 then none else some p.1)) ∈
        Hex.subsetSplits xs := by
  intro xs
  induction xs with
  | nil =>
      intro mask hmask
      have : mask = [] := List.length_eq_zero_iff.mp hmask
      subst this
      simpa using Hex.subsetSplits_nil_mem
  | cons x xs ih =>
      intro mask hmask
      cases mask with
      | nil => simp at hmask
      | cons b bs =>
          simp only [List.length_cons, Nat.add_right_cancel_iff] at hmask
          rw [List.zip_cons_cons, List.filterMap_cons, List.filterMap_cons]
          by_cases hb : b = true
          · subst hb
            simp only [if_true]
            exact Hex.subsetSplits_cons_left_mem (ih bs hmask)
          · have hb' : b = false := by cases b <;> simp_all
            subst hb'
            simp only
            exact Hex.subsetSplits_cons_right_mem (ih bs hmask)

/-- Converse to `subsetSplits_zip_filterMap_partition`: every executable
`subsetSplits` member is induced by a Boolean mask over the input list. -/
theorem subsetSplits_mem_exists_mask :
    ∀ {xs selected rest : List Hex.ZPoly},
      (selected, rest) ∈ Hex.subsetSplits xs →
        ∃ mask : List Bool,
          mask.length = xs.length ∧
            selected =
              (xs.zip mask).filterMap (fun p => if p.2 then some p.1 else none) ∧
            rest =
              (xs.zip mask).filterMap (fun p => if p.2 then none else some p.1)
  | [], selected, rest, h => by
      simp [Hex.subsetSplits] at h
      rcases h with ⟨rfl, rfl⟩
      exact ⟨[], rfl, rfl, rfl⟩
  | x :: xs, selected, rest, h => by
      unfold Hex.subsetSplits at h
      rcases List.mem_append.mp h with hright | hleft
      · rcases List.mem_map.mp hright with ⟨split, hsplit, hsplit_eq⟩
        rcases split with ⟨selectedTail, restTail⟩
        simp only at hsplit_eq
        rcases hsplit_eq with ⟨rfl, rfl⟩
        rcases subsetSplits_mem_exists_mask hsplit with
          ⟨mask, hmask_len, hselected, hrest⟩
        refine ⟨false :: mask, by simp [hmask_len], ?_, ?_⟩
        · simp [hselected]
        · simp [hrest]
      · rcases List.mem_map.mp hleft with ⟨split, hsplit, hsplit_eq⟩
        rcases split with ⟨selectedTail, restTail⟩
        simp only at hsplit_eq
        rcases hsplit_eq with ⟨rfl, rfl⟩
        rcases subsetSplits_mem_exists_mask hsplit with
          ⟨mask, hmask_len, hselected, hrest⟩
        refine ⟨true :: mask, by simp [hmask_len], ?_, ?_⟩
        · simp [hselected]
        · simp [hrest]

/-- The lifted-factor subset partition lies in the executable
`Hex.subsetSplits` enumeration of the lifted-factor list. -/
theorem liftedSubsetSplit_mem_subsetSplits
    (d : Hex.LiftData) (S : LiftedFactorSubset d) :
    (liftedSubsetSelectedList d S, liftedSubsetRejectedList d S) ∈
      Hex.subsetSplits d.liftedFactors.toList := by
  unfold liftedSubsetSelectedList liftedSubsetRejectedList
  exact subsetSplits_zip_filterMap_partition d.liftedFactors.toList
    (liftedSubsetMask d S) (liftedSubsetMask_length d S)

/-- Auxiliary partition lemma at the `subsetSplitsWithFirst` surface: when the
mask starts with `true`, the partition lies in
`Hex.subsetSplitsWithFirst (x :: xs)`. -/
private theorem subsetSplitsWithFirst_zip_filterMap_partition
    (x : Hex.ZPoly) (xs : List Hex.ZPoly) (bs : List Bool) (h : bs.length = xs.length) :
    (((x :: xs).zip (true :: bs)).filterMap (fun p => if p.2 then some p.1 else none),
      ((x :: xs).zip (true :: bs)).filterMap (fun p => if p.2 then none else some p.1)) ∈
      Hex.subsetSplitsWithFirst (x :: xs) := by
  rw [List.zip_cons_cons, List.filterMap_cons, List.filterMap_cons]
  simp only [if_true]
  exact Hex.subsetSplitsWithFirst_mem_cons (subsetSplits_zip_filterMap_partition xs bs h)

/-- Converse at the `subsetSplitsWithFirst` surface: every split comes from a
Boolean mask over the tail, with the head forced into the selected side. -/
theorem subsetSplitsWithFirst_mem_exists_tail_mask
    {x : Hex.ZPoly} {xs selected rest : List Hex.ZPoly}
    (h : (selected, rest) ∈ Hex.subsetSplitsWithFirst (x :: xs)) :
    ∃ mask : List Bool,
      mask.length = xs.length ∧
        selected =
          x :: (xs.zip mask).filterMap (fun p => if p.2 then some p.1 else none) ∧
        rest =
          (xs.zip mask).filterMap (fun p => if p.2 then none else some p.1) := by
  unfold Hex.subsetSplitsWithFirst at h
  rcases List.mem_map.mp h with ⟨split, hsplit, hsplit_eq⟩
  rcases split with ⟨selectedTail, restTail⟩
  simp only at hsplit_eq
  rcases hsplit_eq with ⟨rfl, rfl⟩
  rcases subsetSplits_mem_exists_mask hsplit with
    ⟨mask, hmask_len, hselected, hrest⟩
  exact ⟨mask, hmask_len, by simp [hselected], hrest⟩

/-- The first entry of `liftedSubsetMask d S`, via `head?`, records membership
of index `0` in `S`. -/
private theorem liftedSubsetMask_head?_eq_decide
    (d : Hex.LiftData) (S : LiftedFactorSubset d)
    (hpos : 0 < d.liftedFactors.size) :
    (liftedSubsetMask d S).head? =
      some (decide ((⟨0, hpos⟩ : LiftedFactorIndex d) ∈ S)) := by
  unfold liftedSubsetMask
  rw [List.head?_map]
  have hfin : (List.finRange d.liftedFactors.size).head? =
      some (⟨0, hpos⟩ : Fin d.liftedFactors.size) := by
    have h : (List.finRange d.liftedFactors.size)[0]? =
        some (⟨0, hpos⟩ : Fin d.liftedFactors.size) := by
      rw [List.getElem?_eq_getElem (by simp; exact hpos)]
      simp
    simpa [List.head?_eq_getElem?] using h
  rw [hfin]
  rfl

/-- General `filterMap`/`filter`-`map` equivalence: a `filterMap` whose body is
either `some (f x)` or `none` is the same as filtering then mapping. -/
private theorem List.filterMap_if_eq_map_filter
    {α β : Type _} (l : List α) (p : α → Bool) (f : α → β) :
    l.filterMap (fun x => if p x then some (f x) else none) =
      (l.filter p).map f := by
  induction l with
  | nil => simp
  | cons x xs ih =>
      cases hp : p x with
      | true => simp [hp, ih]
      | false => simp [hp, ih]

/-- The selected list has the clean `filter`/`map` characterisation needed for
multiset/permutation reasoning. -/
private theorem liftedSubsetSelectedList_eq_filter_map
    (d : Hex.LiftData) (S : LiftedFactorSubset d) :
    liftedSubsetSelectedList d S =
      ((List.finRange d.liftedFactors.size).filter fun i => decide (i ∈ S)).map
        (liftedFactor d) := by
  unfold liftedSubsetSelectedList liftedSubsetMask liftedFactor
  -- Rewrite d.liftedFactors.toList as a finRange map.
  have hxs : d.liftedFactors.toList =
      (List.finRange d.liftedFactors.size).map (fun i => d.liftedFactors[i]) := by
    apply List.ext_getElem
    · simp
    · intro n h₁ h₂
      simp [List.getElem_finRange]
  rw [hxs, List.zip_map', List.filterMap_map]
  simp only [Function.comp_def]
  exact List.filterMap_if_eq_map_filter
    (List.finRange d.liftedFactors.size) (fun i => decide (i ∈ S))
    (fun i => d.liftedFactors[i])

/-- The order-preserving filter of `List.finRange n` by membership in a Finset
of `Fin n` is a permutation of the Finset's `toList`. -/
private theorem finRange_filter_mem_perm_toList
    {n : Nat} (S : Finset (Fin n)) :
    ((List.finRange n).filter (fun i => decide (i ∈ S))).Perm S.toList := by
  apply List.perm_of_nodup_nodup_toFinset_eq
  · exact (List.nodup_finRange n).filter _
  · exact S.nodup_toList
  · simp [List.toFinset_filter, List.toFinset_finRange,
      Finset.filter_univ_mem, Finset.toList_toFinset]

/-- The rejected list has the dual `filter`/`map` characterisation: it is the
order-preserving filter of the universe of lifted-factor indices by
non-membership in `S`, mapped through `liftedFactor d`. -/
private theorem liftedSubsetRejectedList_eq_filter_map
    (d : Hex.LiftData) (S : LiftedFactorSubset d) :
    liftedSubsetRejectedList d S =
      ((List.finRange d.liftedFactors.size).filter fun i => decide (i ∉ S)).map
        (liftedFactor d) := by
  unfold liftedSubsetRejectedList liftedSubsetMask liftedFactor
  have hxs : d.liftedFactors.toList =
      (List.finRange d.liftedFactors.size).map (fun i => d.liftedFactors[i]) := by
    apply List.ext_getElem
    · simp
    · intro n h₁ h₂
      simp [List.getElem_finRange]
  rw [hxs, List.zip_map', List.filterMap_map]
  simp only [Function.comp_def]
  -- Convert `if p then none else some` into `if !p then some else none`.
  have hrewrite :
      (fun x : Fin d.liftedFactors.size =>
          if decide (x ∈ S) then (none : Option Hex.ZPoly)
          else some d.liftedFactors[x]) =
        fun x : Fin d.liftedFactors.size =>
          if decide (x ∉ S) then some d.liftedFactors[x] else none := by
    funext x
    by_cases hx : x ∈ S
    · simp [hx]
    · simp [hx]
  rw [hrewrite]
  exact List.filterMap_if_eq_map_filter
    (List.finRange d.liftedFactors.size) (fun i => decide (i ∉ S))
    (fun i => d.liftedFactors[i])

/-- Predicate capturing that `localFactors` is the order-preserving list of
lifted factors at the indices in `J`.  This is the invariant preserved by the
recursive recombination search: at every level the executable's running
`localFactors` is exactly the list of lifted factors at the remaining
unconsumed indices.

Used by the recursive coverage proof to connect the proof-side
`HenselSubsetCorrespondenceRest core d J target` to the executable list
threaded through `Hex.recombinationSearchModAux`. -/
def LiftedFactorListMatches (d : Hex.LiftData) (J : LiftedFactorSubset d)
    (localFactors : List Hex.ZPoly) : Prop :=
  localFactors =
    ((List.finRange d.liftedFactors.size).filter fun i => decide (i ∈ J)).map
      (liftedFactor d)

/-- The matching predicate is equivalent to `localFactors = liftedSubsetSelectedList d J`,
the cleanest form for connecting to the executable recombination split API. -/
theorem LiftedFactorListMatches_iff_eq_liftedSubsetSelectedList
    (d : Hex.LiftData) (J : LiftedFactorSubset d)
    (localFactors : List Hex.ZPoly) :
    LiftedFactorListMatches d J localFactors ↔
      localFactors = liftedSubsetSelectedList d J := by
  unfold LiftedFactorListMatches
  rw [liftedSubsetSelectedList_eq_filter_map]

/-- Initial-state instance: the full lifted-factor list matches the universe
of indices.  This pairs with `henselSubsetCorrespondenceRest_initial` at the
start of the recursive coverage induction. -/
theorem LiftedFactorListMatches.univ (d : Hex.LiftData) :
    LiftedFactorListMatches d Finset.univ d.liftedFactors.toList := by
  unfold LiftedFactorListMatches liftedFactor
  have hxs : d.liftedFactors.toList =
      (List.finRange d.liftedFactors.size).map (fun i => d.liftedFactors[i]) := by
    apply List.ext_getElem
    · simp
    · intro n h₁ h₂
      simp [List.getElem_finRange]
  rw [hxs]
  congr 1
  exact (List.filter_eq_self.mpr (by intro a _; simp)).symm

/-- Cardinality lemma: a matched list has length equal to `J.card`.  This is
the natural induction measure for the recursive coverage proof. -/
theorem LiftedFactorListMatches.length_eq_card
    {d : Hex.LiftData} {J : LiftedFactorSubset d} {localFactors : List Hex.ZPoly}
    (h : LiftedFactorListMatches d J localFactors) :
    localFactors.length = J.card := by
  rw [h, List.length_map, (finRange_filter_mem_perm_toList J).length_eq, Finset.length_toList]

/-- A matched `localFactors` is `Nodup` whenever `liftedFactor d` is injective
on the index set `J`.

Discharges the `hlocal_nodup` hypothesis of
`liftedSubsetSplit_prefix_exists_mem_sdiff_of_matches` and
`liftedFactorSubsetPartition_prefix_none`.  The `Set.InjOn` premise is a
Hensel-coprimality fact about the local factors of `d`: distinct lifted
factors are pairwise coprime, so when monic they are not equal as
polynomials.  Producing the injectivity witness from partition data (or
directly from `henselLiftData` invariants) is the caller's responsibility
in #4301; this shim covers only the pure list-level step. -/
theorem LiftedFactorListMatches.nodup_of_injOn
    {d : Hex.LiftData} {J : LiftedFactorSubset d}
    {localFactors : List Hex.ZPoly}
    (h : LiftedFactorListMatches d J localFactors)
    (hinj : Set.InjOn (liftedFactor d) (J : Set (LiftedFactorIndex d))) :
    localFactors.Nodup := by
  rw [h]
  refine List.Nodup.map_on ?_ ((List.nodup_finRange _).filter _)
  intro x hx y hy hxy
  rw [List.mem_filter] at hx hy
  exact hinj (of_decide_eq_true hx.2) (of_decide_eq_true hy.2) hxy

/-- The rejected list of a subset `S` is exactly the selected list of the
complementary universe minus `S`.  This is the executable-side identity that
matches `liftedSubsetRejectedList d S` to `Finset.univ \ S`. -/
theorem liftedSubsetRejectedList_eq_liftedSubsetSelectedList_sdiff
    (d : Hex.LiftData) (S : LiftedFactorSubset d) :
    liftedSubsetRejectedList d S = liftedSubsetSelectedList d (Finset.univ \ S) := by
  rw [liftedSubsetRejectedList_eq_filter_map, liftedSubsetSelectedList_eq_filter_map]
  congr 1
  apply List.filter_congr
  intro i _
  simp [Finset.mem_sdiff]

/-- Rejection-step instance: emitting `S` from the universal initial state
leaves the executable's running `localFactors` matched to `Finset.univ \ S`.
This is the universe-level case of the recursive invariant transition; the
general `J ↦ J \ S` step lives in the recursive coverage proof and uses this
lemma plus a partition-bridging lemma. -/
theorem LiftedFactorListMatches.rejected_of_subset
    (d : Hex.LiftData) (S : LiftedFactorSubset d) :
    LiftedFactorListMatches d (Finset.univ \ S) (liftedSubsetRejectedList d S) := by
  rw [LiftedFactorListMatches_iff_eq_liftedSubsetSelectedList]
  exact liftedSubsetRejectedList_eq_liftedSubsetSelectedList_sdiff d S

/-- The order-preserving filter of `List.finRange n` by membership in a Finset
equals the sorted list of that Finset.  Two sorted lists with the same
multiset of elements are equal, and `filter` of a sorted list is sorted. -/
private theorem finRange_filter_eq_sort
    {n : Nat} (J : Finset (Fin n)) :
    (List.finRange n).filter (fun i => decide (i ∈ J)) = J.sort (· ≤ ·) := by
  classical
  apply List.Perm.eq_of_sortedLE
  · exact ((List.sortedLT_finRange n).pairwise.imp le_of_lt).filter _ |>.sortedLE
  · exact (J.sortedLT_sort).pairwise.imp le_of_lt |>.sortedLE
  · exact (finRange_filter_mem_perm_toList J).trans (J.sort_perm_toList (· ≤ ·)).symm

/-- The `head?` of the order-preserving filter of `List.finRange n` by
membership in a nonempty Finset `J` is `J.min'`.  Combined with the matching
predicate this identifies the head of `localFactors` with the lifted factor
at `J.min'`. -/
private theorem finRange_filter_head?_eq_min'
    {n : Nat} (J : Finset (Fin n)) (hne : J.Nonempty) :
    ((List.finRange n).filter (fun i => decide (i ∈ J))).head? =
      some (J.min' hne) := by
  classical
  rw [finRange_filter_eq_sort]
  have hpos : 0 < (J.sort (· ≤ ·)).length := by
    rw [Finset.length_sort]; exact hne.card_pos
  rw [List.head?_eq_getElem?, List.getElem?_eq_getElem hpos]
  exact congrArg some Finset.sorted_zero_eq_min'

/-- Head identification for a non-empty matching state: the head of
`localFactors` is the lifted factor at `J.min'`.  Used by the recursive
coverage proof to connect the proof-side "first remaining index of `J`" to the
executable-side head of `localFactors`. -/
theorem LiftedFactorListMatches.head?_eq_liftedFactor_min'
    {d : Hex.LiftData} {J : LiftedFactorSubset d} {localFactors : List Hex.ZPoly}
    (h : LiftedFactorListMatches d J localFactors) (hne : J.Nonempty) :
    localFactors.head? = some (liftedFactor d (J.min' hne)) := by
  rw [h, List.head?_map, finRange_filter_head?_eq_min' J hne]
  rfl

/-- The order-preserving filter of `List.finRange n` by membership in `J ∩ S`
equals the filter by `S` when `S ⊆ J`. Used to identify the selected sublist
of a matched `localFactors` with `liftedSubsetSelectedList d S`. -/
private theorem finRange_filter_mem_and_mem_eq_of_subset
    {n : Nat} {J S : Finset (Fin n)} (hSJ : S ⊆ J) :
    ((List.finRange n).filter fun i => decide (i ∈ J)).filter
        (fun i => decide (i ∈ S)) =
      (List.finRange n).filter fun i => decide (i ∈ S) := by
  rw [List.filter_filter]
  apply List.filter_congr
  intro i _
  by_cases hS : i ∈ S
  · simp [hS, hSJ hS]
  · simp [hS]

/-- Dual of `finRange_filter_mem_and_mem_eq_of_subset`: filtering by membership
in `J` then by non-membership in `S` (with `S ⊆ J`) is filtering by membership
in `J \ S`. -/
private theorem finRange_filter_mem_and_not_mem_eq_sdiff_of_subset
    {n : Nat} {J S : Finset (Fin n)} :
    ((List.finRange n).filter fun i => decide (i ∈ J)).filter
        (fun i => decide (i ∉ S)) =
      (List.finRange n).filter fun i => decide (i ∈ J \ S) := by
  rw [List.filter_filter]
  apply List.filter_congr
  intro i _
  by_cases hJ : i ∈ J
  · by_cases hS : i ∈ S
    · simp [hJ, hS, Finset.mem_sdiff]
    · simp [hJ, hS, Finset.mem_sdiff]
  · simp [hJ, Finset.mem_sdiff]

/-- Generalised matching transition: removing `S ⊆ J` from a matching state
yields a matching state for `J \ S` whose `localFactors` is
`liftedSubsetSelectedList d (J \ S)`.  This is the recursive invariant
transition used inside the recombination coverage proof. -/
theorem LiftedFactorListMatches.sdiff_of_subset
    {d : Hex.LiftData} {J S : LiftedFactorSubset d} :
    LiftedFactorListMatches d (J \ S)
      (liftedSubsetSelectedList d (J \ S)) :=
  (LiftedFactorListMatches_iff_eq_liftedSubsetSelectedList d (J \ S) _).mpr rfl

/-- Generalised partition lemma at the `subsetSplitsWithFirst` surface: for any
matching state and any `S ⊆ J` containing `J.min'`, the order-preserving
`(selected, rest)` partition of `localFactors` by `S` lies in
`subsetSplitsWithFirst localFactors`.

The selected component is `liftedSubsetSelectedList d S` (since `S ⊆ J`) and
the rest component is `liftedSubsetSelectedList d (J \ S)`. -/
theorem liftedSubsetSplit_mem_subsetSplitsWithFirst_of_matches
    {d : Hex.LiftData} {J : LiftedFactorSubset d} {localFactors : List Hex.ZPoly}
    (h : LiftedFactorListMatches d J localFactors)
    {S : LiftedFactorSubset d} (hSJ : S ⊆ J) (hne : J.Nonempty)
    (hmin : J.min' hne ∈ S) :
    (liftedSubsetSelectedList d S, liftedSubsetSelectedList d (J \ S)) ∈
      Hex.subsetSplitsWithFirst localFactors := by
  classical
  -- Step 1: decompose `localFactors` as `head :: tail`.
  have hhead := h.head?_eq_liftedFactor_min' hne
  rcases hloc : localFactors with _ | ⟨head, tail⟩
  · rw [hloc] at hhead; simp at hhead
  rw [hloc] at hhead
  simp only [List.head?_cons, Option.some.injEq] at hhead
  -- `hhead : head = liftedFactor d (J.min' hne)`.
  -- Step 2: rewrite `localFactors` via the matching predicate.
  have hloc_eq : head :: tail =
      ((List.finRange d.liftedFactors.size).filter fun i => decide (i ∈ J)).map
        (liftedFactor d) := by
    rw [← hloc]; exact h
  -- Step 3: zip with the membership mask for `S`.
  set xs : List (Fin d.liftedFactors.size) :=
    (List.finRange d.liftedFactors.size).filter (fun i => decide (i ∈ J))
    with hxs_def
  have hloc_eq' : head :: tail = xs.map (liftedFactor d) := hloc_eq
  -- The mask paired with `xs` records membership in `S`.
  set bs : List Bool := xs.map (fun i => decide (i ∈ S))
  -- Step 4: the zip identifies the selected/rejected filterMaps.
  have hzip :
      (xs.map (liftedFactor d)).zip bs =
        xs.map (fun i => (liftedFactor d i, decide (i ∈ S))) := by
    rw [List.zip_map']
  -- Step 5: identify the selected filterMap with `liftedSubsetSelectedList d S`.
  have hsel :
      ((xs.map (liftedFactor d)).zip bs).filterMap
        (fun p => if p.2 then some p.1 else none) =
          liftedSubsetSelectedList d S := by
    rw [hzip, List.filterMap_map]
    simp only [Function.comp_def]
    rw [List.filterMap_if_eq_map_filter xs (fun i => decide (i ∈ S))
      (liftedFactor d)]
    rw [hxs_def, finRange_filter_mem_and_mem_eq_of_subset hSJ,
      ← liftedSubsetSelectedList_eq_filter_map]
  -- Step 6: identify the rejected filterMap with `liftedSubsetSelectedList d (J \ S)`.
  have hrej :
      ((xs.map (liftedFactor d)).zip bs).filterMap
        (fun p => if p.2 then none else some p.1) =
          liftedSubsetSelectedList d (J \ S) := by
    rw [hzip, List.filterMap_map]
    simp only [Function.comp_def]
    -- Convert `if p then none else some` into `if !p then some else none`.
    have hrewrite :
        (fun i : Fin d.liftedFactors.size =>
            if decide (i ∈ S) then (none : Option Hex.ZPoly)
            else some (liftedFactor d i)) =
          fun i => if decide (i ∉ S) then some (liftedFactor d i) else none := by
      funext i
      by_cases hi : i ∈ S
      · simp [hi]
      · simp [hi]
    rw [hrewrite, List.filterMap_if_eq_map_filter xs
      (fun i => decide (i ∉ S)) (liftedFactor d)]
    rw [hxs_def, finRange_filter_mem_and_not_mem_eq_sdiff_of_subset,
      ← liftedSubsetSelectedList_eq_filter_map]
  -- Step 7: show `bs = true :: bs'` since the head index `J.min' hne ∈ S`.
  have hxs_cons : ∃ ys, xs = (J.min' hne) :: ys := by
    have hhead_xs : xs.head? = some (J.min' hne) := by
      rw [hxs_def]; exact finRange_filter_head?_eq_min' J hne
    cases hxs_case : xs with
    | nil => rw [hxs_case] at hhead_xs; simp at hhead_xs
    | cons x ys =>
        rw [hxs_case] at hhead_xs
        simp only [List.head?_cons, Option.some.injEq] at hhead_xs
        exact ⟨ys, by rw [hhead_xs]⟩
  obtain ⟨ys, hxs_cons_eq⟩ := hxs_cons
  -- Step 8: invoke `subsetSplitsWithFirst_zip_filterMap_partition`.
  rw [hloc_eq', hxs_cons_eq, List.map_cons]
  have hbs_cons : bs = true :: ys.map (fun i => decide (i ∈ S)) := by
    show xs.map (fun i => decide (i ∈ S)) =
      true :: ys.map (fun i => decide (i ∈ S))
    rw [hxs_cons_eq, List.map_cons]
    congr 1
    simp [hmin]
  -- The selected/rejected filterMaps via the cons form.
  have hsel_cons :
      liftedSubsetSelectedList d S =
        ((liftedFactor d (J.min' hne) :: ys.map (liftedFactor d)).zip
            (true :: ys.map (fun i => decide (i ∈ S)))).filterMap
          (fun p => if p.2 then some p.1 else none) := by
    have := hsel
    rw [hxs_cons_eq, List.map_cons] at this
    rw [hbs_cons] at this
    exact this.symm
  have hrej_cons :
      liftedSubsetSelectedList d (J \ S) =
        ((liftedFactor d (J.min' hne) :: ys.map (liftedFactor d)).zip
            (true :: ys.map (fun i => decide (i ∈ S)))).filterMap
          (fun p => if p.2 then none else some p.1) := by
    have := hrej
    rw [hxs_cons_eq, List.map_cons] at this
    rw [hbs_cons] at this
    exact this.symm
  rw [hsel_cons, hrej_cons]
  have hys_len_eq : (ys.map (fun i => decide (i ∈ S))).length =
      (ys.map (liftedFactor d)).length := by simp
  exact subsetSplitsWithFirst_zip_filterMap_partition
    (liftedFactor d (J.min' hne))
    (ys.map (liftedFactor d))
    (ys.map (fun i => decide (i ∈ S)))
    hys_len_eq

/-- Filter of a `Nodup` list by membership in the `toFinset` of a Boolean-mask
`filterMap` equals the `filterMap` itself.  This is the key combinatorial step
in the converse to `liftedSubsetSplit_mem_subsetSplitsWithFirst_of_matches`:
the executable enumeration recovers an index-level Finset from a polynomial-
level mask. -/
private theorem List.nodup_filter_mem_toFinset_zip_filterMap_selected
    {α : Type*} [DecidableEq α]
    (xs : List α) (bs : List Bool) (hxs : xs.Nodup) (hlen : bs.length = xs.length) :
    xs.filter (fun x => decide (x ∈ ((xs.zip bs).filterMap
        (fun p => if p.2 then some p.1 else none)).toFinset)) =
      (xs.zip bs).filterMap (fun p => if p.2 then some p.1 else none) := by
  induction xs generalizing bs with
  | nil => simp
  | cons x xs ih =>
      cases bs with
      | nil => simp at hlen
      | cons b bs =>
          simp only [List.length_cons, Nat.add_right_cancel_iff] at hlen
          have hxs_nodup : xs.Nodup := (List.nodup_cons.mp hxs).2
          have hx_notin : x ∉ xs := (List.nodup_cons.mp hxs).1
          set tailSelected : List α :=
            (xs.zip bs).filterMap (fun p => if p.2 then some p.1 else none)
            with htailSelected_def
          cases b with
          | true =>
              -- Both sides reduce to forms involving `x :: tailSelected` via
              -- definitional reduction of `filterMap` on `(x, true) :: ...`.
              show (x :: xs).filter
                  (fun y => decide (y ∈ (x :: tailSelected).toFinset)) =
                x :: tailSelected
              rw [show (x :: xs).filter
                      (fun y => decide (y ∈ (x :: tailSelected).toFinset)) =
                    x :: xs.filter
                      (fun y => decide (y ∈ (x :: tailSelected).toFinset)) from
                List.filter_cons_of_pos (by simp)]
              congr 1
              -- For y ∈ xs, y ≠ x, so membership reduces to tailSelected.toFinset.
              have hcongr : ∀ y ∈ xs,
                  decide (y ∈ (x :: tailSelected).toFinset) =
                    decide (y ∈ tailSelected.toFinset) := by
                intro y hy
                have hyne : y ≠ x := fun heq => hx_notin (heq ▸ hy)
                simp [List.toFinset_cons, hyne]
              rw [List.filter_congr hcongr]
              exact ih bs hxs_nodup hlen
          | false =>
              -- `filterMap` on `(x, false) :: ...` drops x; both sides reduce
              -- to `tailSelected` definitionally.
              show (x :: xs).filter
                  (fun y => decide (y ∈ tailSelected.toFinset)) = tailSelected
              have hx_notin_tail : x ∉ tailSelected := by
                rw [htailSelected_def, List.mem_filterMap]
                rintro ⟨⟨a, b'⟩, hp_mem, hp_eq⟩
                have ha_xs : a ∈ xs := (List.of_mem_zip hp_mem).1
                cases b' with
                | true =>
                    simp only [if_true, Option.some.injEq] at hp_eq
                    rw [← hp_eq] at hx_notin
                    exact hx_notin ha_xs
                | false => simp at hp_eq
              rw [show (x :: xs).filter
                      (fun y => decide (y ∈ tailSelected.toFinset)) =
                    xs.filter
                      (fun y => decide (y ∈ tailSelected.toFinset)) from
                List.filter_cons_of_neg (by simp [hx_notin_tail])]
              exact ih bs hxs_nodup hlen

/-- Dual of `nodup_filter_mem_toFinset_zip_filterMap_selected`: filtering by
non-membership in the selected `toFinset` recovers the rest filterMap. -/
private theorem List.nodup_filter_not_mem_toFinset_zip_filterMap_rest
    {α : Type*} [DecidableEq α]
    (xs : List α) (bs : List Bool) (hxs : xs.Nodup) (hlen : bs.length = xs.length) :
    xs.filter (fun x => decide (x ∉ ((xs.zip bs).filterMap
        (fun p => if p.2 then some p.1 else none)).toFinset)) =
      (xs.zip bs).filterMap (fun p => if p.2 then none else some p.1) := by
  induction xs generalizing bs with
  | nil => simp
  | cons x xs ih =>
      cases bs with
      | nil => simp at hlen
      | cons b bs =>
          simp only [List.length_cons, Nat.add_right_cancel_iff] at hlen
          have hxs_nodup : xs.Nodup := (List.nodup_cons.mp hxs).2
          have hx_notin : x ∉ xs := (List.nodup_cons.mp hxs).1
          set tailSelected : List α :=
            (xs.zip bs).filterMap (fun p => if p.2 then some p.1 else none)
            with htailSelected_def
          set tailRest : List α :=
            (xs.zip bs).filterMap (fun p => if p.2 then none else some p.1)
          cases b with
          | true =>
              -- selected at (x, true) = some x, rest at (x, true) = none.
              show (x :: xs).filter
                  (fun y => decide (y ∉ (x :: tailSelected).toFinset)) = tailRest
              rw [show (x :: xs).filter
                      (fun y => decide (y ∉ (x :: tailSelected).toFinset)) =
                    xs.filter
                      (fun y => decide (y ∉ (x :: tailSelected).toFinset)) from
                List.filter_cons_of_neg (by simp)]
              have hcongr : ∀ y ∈ xs,
                  decide (y ∉ (x :: tailSelected).toFinset) =
                    decide (y ∉ tailSelected.toFinset) := by
                intro y hy
                have hyne : y ≠ x := fun heq => hx_notin (heq ▸ hy)
                simp [List.toFinset_cons, hyne]
              rw [List.filter_congr hcongr]
              exact ih bs hxs_nodup hlen
          | false =>
              -- selected at (x, false) = none, rest at (x, false) = some x.
              show (x :: xs).filter
                  (fun y => decide (y ∉ tailSelected.toFinset)) = x :: tailRest
              have hx_notin_tail : x ∉ tailSelected := by
                rw [htailSelected_def, List.mem_filterMap]
                rintro ⟨⟨a, b'⟩, hp_mem, hp_eq⟩
                have ha_xs : a ∈ xs := (List.of_mem_zip hp_mem).1
                cases b' with
                | true =>
                    simp only [if_true, Option.some.injEq] at hp_eq
                    rw [← hp_eq] at hx_notin
                    exact hx_notin ha_xs
                | false => simp at hp_eq
              rw [show (x :: xs).filter
                      (fun y => decide (y ∉ tailSelected.toFinset)) =
                    x :: xs.filter
                      (fun y => decide (y ∉ tailSelected.toFinset)) from
                List.filter_cons_of_pos (by simp [hx_notin_tail])]
              congr 1
              exact ih bs hxs_nodup hlen

/-- Mask-to-subset lemma: given a Boolean mask of matching length over the
tail of a matched `localFactors` list, there is a `LiftedFactorSubset d`
(containing `J.min'` and contained in `J`) whose `(selected, rest)` list
partition equals the matched-list mask partition.  The natural converse of
`liftedSubsetSplit_mem_subsetSplitsWithFirst_of_matches`, used to recover a
proof-side lifted-factor subset from an arbitrary executable split. -/
theorem liftedSubsetSelectedList_eq_mask_partition_of_matches
    {d : Hex.LiftData} {J : LiftedFactorSubset d}
    {localFactors : List Hex.ZPoly}
    (hmatches : LiftedFactorListMatches d J localFactors)
    (hne : J.Nonempty)
    {head : Hex.ZPoly} {tail : List Hex.ZPoly}
    (hloc : localFactors = head :: tail)
    (mask : List Bool) (hmask_len : mask.length = tail.length) :
    ∃ T : LiftedFactorSubset d,
      T ⊆ J ∧ J.min' hne ∈ T ∧
      liftedSubsetSelectedList d T =
        head :: (tail.zip mask).filterMap (fun p => if p.2 then some p.1 else none) ∧
      liftedSubsetSelectedList d (J \ T) =
        (tail.zip mask).filterMap (fun p => if p.2 then none else some p.1) := by
  classical
  -- The J-filter index list, starting at J.min'.
  set xs : List (LiftedFactorIndex d) :=
    (List.finRange d.liftedFactors.size).filter (fun i => decide (i ∈ J)) with hxs_def
  have hxs_head : xs.head? = some (J.min' hne) := finRange_filter_head?_eq_min' J hne
  obtain ⟨ys, hxs_eq⟩ : ∃ ys, xs = (J.min' hne) :: ys := by
    cases hxs_case : xs with
    | nil => rw [hxs_case] at hxs_head; simp at hxs_head
    | cons x ys =>
        rw [hxs_case] at hxs_head
        simp only [List.head?_cons, Option.some.injEq] at hxs_head
        exact ⟨ys, by rw [hxs_head]⟩
  -- xs is Nodup, hence ys is Nodup and J.min' ∉ ys.
  have hxs_nodup : xs.Nodup := (List.nodup_finRange _).filter _
  rw [hxs_eq] at hxs_nodup
  have hys_nodup : ys.Nodup := (List.nodup_cons.mp hxs_nodup).2
  have hmin_notin_ys : J.min' hne ∉ ys := (List.nodup_cons.mp hxs_nodup).1
  -- Identify head and tail via the matching predicate.
  have hloc_via_xs : localFactors = xs.map (liftedFactor d) := hmatches
  rw [hxs_eq, List.map_cons] at hloc_via_xs
  rw [hloc] at hloc_via_xs
  obtain ⟨hhead_eq, htail_eq⟩ :
      head = liftedFactor d (J.min' hne) ∧ tail = ys.map (liftedFactor d) := by
    simp only [List.cons.injEq] at hloc_via_xs
    exact hloc_via_xs
  -- mask length matches ys length.
  have hys_mask_len : mask.length = ys.length := by
    rw [hmask_len, htail_eq, List.length_map]
  -- The tail-selected index list and T.
  set tailSelected : List (LiftedFactorIndex d) :=
    (ys.zip mask).filterMap (fun p => if p.2 then some p.1 else none)
    with htailSelected_def
  set T : LiftedFactorSubset d :=
    insert (J.min' hne) tailSelected.toFinset with hT_def
  -- tailSelected is a sublist of ys.
  have htailSelected_subset_ys : ∀ x ∈ tailSelected, x ∈ ys := by
    intro x hx
    rw [htailSelected_def, List.mem_filterMap] at hx
    obtain ⟨⟨a, b⟩, hp_mem, hp_eq⟩ := hx
    have ha_ys : a ∈ ys := (List.of_mem_zip hp_mem).1
    cases b with
    | true => simp only [if_true, Option.some.injEq] at hp_eq; rw [← hp_eq]; exact ha_ys
    | false => simp at hp_eq
  -- T ⊆ J.
  have hTJ : T ⊆ J := by
    intro x hx
    rw [hT_def] at hx
    rcases Finset.mem_insert.mp hx with hmin | htf
    · rw [hmin]; exact J.min'_mem hne
    · rw [List.mem_toFinset] at htf
      have hx_ys : x ∈ ys := htailSelected_subset_ys x htf
      have hx_xs : x ∈ xs := by rw [hxs_eq]; exact List.mem_cons_of_mem _ hx_ys
      rw [hxs_def, List.mem_filter] at hx_xs
      exact of_decide_eq_true hx_xs.2
  -- J.min' ∈ T.
  have hmin_in_T : J.min' hne ∈ T := by
    rw [hT_def]; exact Finset.mem_insert_self _ _
  refine ⟨T, hTJ, hmin_in_T, ?_, ?_⟩
  · -- Selected list equality.
    rw [liftedSubsetSelectedList_eq_filter_map]
    -- Reduce (finRange n).filter (· ∈ T) to xs.filter (· ∈ T) via T ⊆ J.
    rw [show (List.finRange d.liftedFactors.size).filter (fun i => decide (i ∈ T)) =
            xs.filter (fun i => decide (i ∈ T)) from by
      rw [hxs_def]; exact (finRange_filter_mem_and_mem_eq_of_subset hTJ).symm]
    rw [hxs_eq]
    rw [show (J.min' hne :: ys).filter (fun i => decide (i ∈ T)) =
            J.min' hne :: ys.filter (fun i => decide (i ∈ T)) from
      List.filter_cons_of_pos (by simp [hmin_in_T])]
    rw [List.map_cons, hhead_eq, htail_eq]
    congr 1
    -- (ys.filter (· ∈ T)).map (liftedFactor d) =
    --   ((ys.map (liftedFactor d)).zip mask).filterMap selected
    have hys_filter_eq :
        ys.filter (fun i => decide (i ∈ T)) =
          ys.filter (fun i => decide (i ∈ tailSelected.toFinset)) := by
      apply List.filter_congr
      intro y hy
      have hyne : y ≠ J.min' hne := fun heq => hmin_notin_ys (heq ▸ hy)
      simp [hT_def, hyne]
    rw [hys_filter_eq]
    rw [List.nodup_filter_mem_toFinset_zip_filterMap_selected ys mask hys_nodup
      hys_mask_len]
    rw [List.zip_map_left, List.filterMap_map, List.map_filterMap]
    congr 1
    funext p
    obtain ⟨a, b⟩ := p
    cases b <;> rfl
  · -- Rest list equality.
    rw [liftedSubsetSelectedList_eq_filter_map]
    rw [show ((List.finRange d.liftedFactors.size).filter
            (fun i => decide (i ∈ J \ T))) =
            xs.filter (fun i => decide (i ∉ T)) from by
      rw [hxs_def]
      exact (finRange_filter_mem_and_not_mem_eq_sdiff_of_subset
        (J := J) (S := T)).symm]
    rw [hxs_eq]
    rw [show (J.min' hne :: ys).filter (fun i => decide (i ∉ T)) =
            ys.filter (fun i => decide (i ∉ T)) from
      List.filter_cons_of_neg (by simp [hmin_in_T])]
    rw [htail_eq]
    have hys_filter_eq :
        ys.filter (fun i => decide (i ∉ T)) =
          ys.filter (fun i => decide (i ∉ tailSelected.toFinset)) := by
      apply List.filter_congr
      intro y hy
      have hyne : y ≠ J.min' hne := fun heq => hmin_notin_ys (heq ▸ hy)
      simp [hT_def, hyne]
    rw [hys_filter_eq]
    rw [List.nodup_filter_not_mem_toFinset_zip_filterMap_rest ys mask hys_nodup
      hys_mask_len]
    rw [List.zip_map_left, List.filterMap_map, List.map_filterMap]
    congr 1
    funext p
    obtain ⟨a, b⟩ := p
    cases b <;> rfl

/-- Structural enumeration-order content of `Hex.subsetSplits` on a `Nodup`
input: if the `mask_S`-induced split sits at the boundary `pre ++ _ :: suffix`
and the `mask_T`-induced split sits somewhere inside `pre`, then `mask_S` has
a `true` at some position where `mask_T` is `false`.

The `Nodup` precondition rules out the duplicate-element ambiguity where a
mask's induced split happens to land in the `false`-branch image of an
inductive step despite the mask's head bit being `true`. Once duplicates are
excluded, the cons step has exactly four sub-cases on the head bits
`(mask_S.head, mask_T.head)`: `(true, false)` yields `i = 0` directly,
`(false, true)` is structurally impossible because `mask_T`'s split lands in
the second half of `Hex.subsetSplits (x :: xs')` (after `mask_S`'s split),
and the head-matching cases recurse into the tail.

Used by the matched-state prefix-with-bit-difference lemma
`liftedSubsetSplit_prefix_exists_mem_sdiff_of_matches` after promoting the
matched J-filter index list (which is `Nodup`) into scope. -/
private theorem subsetSplits_prefix_exists_bit_diff_aux
    {xs : List Hex.ZPoly} (hxs_nodup : xs.Nodup)
    {mask_S mask_T : List Bool}
    (hSlen : mask_S.length = xs.length)
    (hTlen : mask_T.length = xs.length)
    {pre suffix : List (List Hex.ZPoly × List Hex.ZPoly)}
    (hsplits :
      Hex.subsetSplits xs =
        pre ++
          ((xs.zip mask_S).filterMap (fun p => if p.2 then some p.1 else none),
           (xs.zip mask_S).filterMap (fun p => if p.2 then none else some p.1))
            :: suffix)
    (hT_in_pre :
      ((xs.zip mask_T).filterMap (fun p => if p.2 then some p.1 else none),
       (xs.zip mask_T).filterMap (fun p => if p.2 then none else some p.1))
         ∈ pre) :
    ∃ i, ∃ hi : i < xs.length,
      mask_T[i]'(hTlen ▸ hi) = false ∧
      mask_S[i]'(hSlen ▸ hi) = true := by
  induction xs generalizing mask_S mask_T pre suffix with
  | nil =>
      -- Base case: subsetSplits [] = [([], [])], so pre = [] and hT_in_pre is False.
      cases mask_S with
      | nil =>
        cases mask_T with
        | nil =>
          -- hsplits : [([], [])] = pre ++ ([], []) :: suffix; derive pre = []
          have hlen := congrArg List.length hsplits
          simp [Hex.subsetSplits, List.length_append, List.length_cons] at hlen
          have hpre_nil : pre = [] := List.length_eq_zero_iff.mp (by omega)
          subst hpre_nil
          simp at hT_in_pre
        | cons => simp at hTlen
      | cons => simp at hSlen
  | cons x xs' ih =>
      have hx_notin : x ∉ xs' := (List.nodup_cons.mp hxs_nodup).1
      have hxs'_nodup : xs'.Nodup := (List.nodup_cons.mp hxs_nodup).2
      cases mask_S with
      | nil => simp at hSlen
      | cons bS msS =>
        cases mask_T with
        | nil => simp at hTlen
        | cons bT msT =>
          simp only [List.length_cons, Nat.add_right_cancel_iff] at hSlen hTlen
          -- L_false and L_true are the two halves of subsetSplits (x :: xs').
          set L_false :=
            (Hex.subsetSplits xs').map (fun s => (s.1, x :: s.2)) with hLfalse_def
          set L_true :=
            (Hex.subsetSplits xs').map (fun s => (x :: s.1, s.2)) with hLtrue_def
          have hsplits' : Hex.subsetSplits (x :: xs') = L_false ++ L_true := by
            show (let rest := Hex.subsetSplits xs';
                  rest.map (fun split => (split.1, x :: split.2)) ++
                    rest.map (fun split => (x :: split.1, split.2))) = _
            rfl
          rw [hsplits'] at hsplits
          -- Abbreviate tail-mask filterMaps for S and T.
          set tailSel_S : List Hex.ZPoly :=
            (xs'.zip msS).filterMap (fun p => if p.2 then some p.1 else none)
            with htailSel_S_def
          set tailRest_S : List Hex.ZPoly :=
            (xs'.zip msS).filterMap (fun p => if p.2 then none else some p.1)
            with htailRest_S_def
          set tailSel_T : List Hex.ZPoly :=
            (xs'.zip msT).filterMap (fun p => if p.2 then some p.1 else none)
            with htailSel_T_def
          set tailRest_T : List Hex.ZPoly :=
            (xs'.zip msT).filterMap (fun p => if p.2 then none else some p.1)
            with htailRest_T_def
          -- The tail-induced split of xs' under msS / msT.
          have htailSplit_S_mem : (tailSel_S, tailRest_S) ∈ Hex.subsetSplits xs' :=
            subsetSplits_zip_filterMap_partition xs' msS hSlen
          have htailSplit_T_mem : (tailSel_T, tailRest_T) ∈ Hex.subsetSplits xs' :=
            subsetSplits_zip_filterMap_partition xs' msT hTlen
          -- Lemma: with `x ∉ xs'`, no L_false entry has its selected starting
          -- with `x`, and no L_true entry has its rest starting with `x`.
          -- Lemma: with `x ∉ xs'`, no L_false entry has selected starting with `x`,
          -- and no L_true entry has rest starting with `x`. Used to commit to a
          -- specific half based on the head bit of mask_S / mask_T.
          have hx_notin_split_sel :
              ∀ {a b : List Hex.ZPoly}, (a, b) ∈ Hex.subsetSplits xs' → x ∉ a := by
            intro a b hab hxa
            obtain ⟨m, hmlen, hsel_eq, _⟩ := subsetSplits_mem_exists_mask hab
            rw [hsel_eq, List.mem_filterMap] at hxa
            obtain ⟨⟨a', b'⟩, hpair_mem, hpair_eq⟩ := hxa
            have hax' : a' ∈ xs' := (List.of_mem_zip hpair_mem).1
            cases b' with
            | true =>
                simp at hpair_eq
                exact hx_notin (hpair_eq ▸ hax')
            | false => simp at hpair_eq
          have hx_notin_split_rest :
              ∀ {a b : List Hex.ZPoly}, (a, b) ∈ Hex.subsetSplits xs' → x ∉ b := by
            intro a b hab hxb
            obtain ⟨m, hmlen, _, hrest_eq⟩ := subsetSplits_mem_exists_mask hab
            rw [hrest_eq, List.mem_filterMap] at hxb
            obtain ⟨⟨a', b'⟩, hpair_mem, hpair_eq⟩ := hxb
            have hax' : a' ∈ xs' := (List.of_mem_zip hpair_mem).1
            cases b' with
            | true => simp at hpair_eq
            | false =>
                simp at hpair_eq
                exact hx_notin (hpair_eq ▸ hax')
          -- Simplification helpers for evaluating the cons step of zip + filterMap
          -- once the head bit is fixed.
          have eval_sel_false : ∀ (m : List Bool),
              ((x :: xs').zip (false :: m)).filterMap
                  (fun p => if p.2 then some p.1 else none) =
                (xs'.zip m).filterMap (fun p => if p.2 then some p.1 else none) := by
            intro m
            simp [List.zip_cons_cons]
          have eval_rest_false : ∀ (m : List Bool),
              ((x :: xs').zip (false :: m)).filterMap
                  (fun p => if p.2 then none else some p.1) =
                x :: (xs'.zip m).filterMap (fun p => if p.2 then none else some p.1) := by
            intro m
            simp [List.zip_cons_cons]
          have eval_sel_true : ∀ (m : List Bool),
              ((x :: xs').zip (true :: m)).filterMap
                  (fun p => if p.2 then some p.1 else none) =
                x :: (xs'.zip m).filterMap (fun p => if p.2 then some p.1 else none) := by
            intro m
            simp [List.zip_cons_cons]
          have eval_rest_true : ∀ (m : List Bool),
              ((x :: xs').zip (true :: m)).filterMap
                  (fun p => if p.2 then none else some p.1) =
                (xs'.zip m).filterMap (fun p => if p.2 then none else some p.1) := by
            intro m
            simp [List.zip_cons_cons]
          -- Case-split on the head bits.
          cases bS with
          | false =>
            rw [eval_sel_false, eval_rest_false] at hsplits
            -- Shape: split_S = (tailSel_S, x :: tailRest_S). Show split_S ∉ L_true.
            have hsplitS_notin_Ltrue : (tailSel_S, x :: tailRest_S) ∉ L_true := by
              intro h
              obtain ⟨⟨a, _⟩, hab, hab_eq⟩ := List.mem_map.mp h
              simp only [Prod.mk.injEq] at hab_eq
              obtain ⟨ha, _⟩ := hab_eq
              exact hx_notin_split_sel htailSplit_S_mem (ha ▸ List.mem_cons_self)
            cases bT with
            | false =>
              -- (false, false): both splits in L_false.
              rw [eval_sel_false, eval_rest_false] at hT_in_pre
              -- Decompose hsplits.
              rcases (List.append_eq_append_iff).mp hsplits with
                ⟨e, _, hLt_eq⟩ | ⟨e, hLf_eq, hsuff_eq⟩
              · -- Case 1: split_S ∈ L_true. Contradiction.
                exfalso
                have : (tailSel_S, x :: tailRest_S) ∈ L_true := by
                  rw [hLt_eq]; exact List.mem_append_right _ List.mem_cons_self
                exact hsplitS_notin_Ltrue this
              · -- Case 2: L_false = pre ++ e ∧ split_S :: suffix = e ++ L_true.
                -- Extract decomposition of subsetSplits xs' from L_false = (...).map f.
                rw [hLfalse_def] at hLf_eq
                obtain ⟨preIdx, suffIdx, hsplitsXs', hpreIdx_eq, hsuffIdx_eq⟩ :=
                  List.map_eq_append_iff.mp hLf_eq
                cases suffIdx with
                | nil =>
                  exfalso
                  simp only [List.map_nil] at hsuffIdx_eq
                  subst hsuffIdx_eq
                  simp only [List.nil_append] at hsuff_eq
                  have : (tailSel_S, x :: tailRest_S) ∈ L_true := by
                    rw [← hsuff_eq]; exact List.mem_cons_self
                  exact hsplitS_notin_Ltrue this
                | cons headIdx tailIdx =>
                  simp only [List.map_cons] at hsuffIdx_eq
                  subst hsuffIdx_eq
                  -- hsuff_eq : split_S :: suffix =
                  --   (headIdx.1, x :: headIdx.2) :: tailIdx.map f ++ L_true
                  rw [List.cons_append] at hsuff_eq
                  injection hsuff_eq with hsplit_eq _hsuffix_eq
                  -- hsplit_eq : (tailSel_S, x :: tailRest_S) = (headIdx.1, x :: headIdx.2)
                  simp only [Prod.mk.injEq, List.cons.injEq, true_and] at hsplit_eq
                  obtain ⟨hsel_S_eq, hrest_S_eq⟩ := hsplit_eq
                  -- Reconstruct: headIdx = (tailSel_S, tailRest_S).
                  obtain ⟨headSel, headRest⟩ := headIdx
                  simp only at hsel_S_eq hrest_S_eq
                  subst hsel_S_eq; subst hrest_S_eq
                  -- Now: hsplitsXs' : subsetSplits xs' = preIdx ++ (tailSel_S, tailRest_S) :: tailIdx
                  -- Need: (tailSel_T, tailRest_T) ∈ preIdx (from split_T ∈ pre).
                  have hsplitT_in_preIdx : (tailSel_T, tailRest_T) ∈ preIdx := by
                    rw [← hpreIdx_eq] at hT_in_pre
                    obtain ⟨⟨a, b⟩, hab, hab_eq⟩ := List.mem_map.mp hT_in_pre
                    simp only [Prod.mk.injEq, List.cons.injEq, true_and] at hab_eq
                    obtain ⟨ha, hb⟩ := hab_eq
                    convert hab
                    · exact ha.symm
                    · exact hb.symm
                  -- Apply IH (using simped length hypotheses).
                  have hSlen' : msS.length = xs'.length := by simpa using hSlen
                  have hTlen' : msT.length = xs'.length := by simpa using hTlen
                  obtain ⟨i', hi', hmsT_i', hmsS_i'⟩ :=
                    ih hxs'_nodup hSlen' hTlen' hsplitsXs' hsplitT_in_preIdx
                  -- Translate to mask_S = false :: msS, mask_T = false :: msT.
                  refine ⟨i' + 1, by simp; omega, ?_, ?_⟩
                  · simp only [List.getElem_cons_succ]; exact hmsT_i'
                  · simp only [List.getElem_cons_succ]; exact hmsS_i'
            | true =>
              -- (false, true): impossible with x ∉ xs'.
              rw [eval_sel_true, eval_rest_true] at hT_in_pre
              exfalso
              -- Shape facts: split_S ∉ L_true (rest starts with x; L_true rests don't).
              have hsplitS_notin_Ltrue :
                  (tailSel_S, x :: tailRest_S) ∉ L_true := by
                intro h
                obtain ⟨⟨a, b⟩, hab, hab_eq⟩ := List.mem_map.mp h
                simp only [Prod.mk.injEq] at hab_eq
                obtain ⟨_, hb⟩ := hab_eq
                have hxb : x ∈ b := hb ▸ List.mem_cons_self
                exact hx_notin_split_rest hab hxb
              have hsplitT_notin_Lfalse :
                  (x :: tailSel_T, tailRest_T) ∉ L_false := by
                intro h
                obtain ⟨⟨a, b⟩, hab, hab_eq⟩ := List.mem_map.mp h
                simp only [Prod.mk.injEq] at hab_eq
                obtain ⟨ha, _⟩ := hab_eq
                have hxa : x ∈ a := ha ▸ List.mem_cons_self
                exact hx_notin_split_sel hab hxa
              -- Decompose hsplits via List.append_eq_append_iff.
              -- For L_false ++ L_true = pre ++ split_S :: suffix, the two cases are:
              -- (1) ∃ e, pre = L_false ++ e ∧ L_true = e ++ split_S :: suffix. (pre extends past L_false)
              -- (2) ∃ e, L_false = pre ++ e ∧ split_S :: suffix = e ++ L_true. (pre is prefix of L_false)
              rcases (List.append_eq_append_iff).mp hsplits with
                ⟨e, _, hLt_eq⟩ | ⟨e, hLf_eq, _⟩
              · -- Case 1: split_S ∈ L_true. Contradiction.
                have hsplitS_in_Ltrue : (tailSel_S, x :: tailRest_S) ∈ L_true := by
                  rw [hLt_eq]
                  exact List.mem_append_right _ (List.mem_cons_self)
                exact hsplitS_notin_Ltrue hsplitS_in_Ltrue
              · -- Case 2: pre ⊆ L_false; split_T ∈ pre ⊆ L_false. Contradiction.
                have hsplitT_in_Lfalse : (x :: tailSel_T, tailRest_T) ∈ L_false := by
                  rw [hLf_eq]; exact List.mem_append_left _ hT_in_pre
                exact hsplitT_notin_Lfalse hsplitT_in_Lfalse
          | true =>
            rw [eval_sel_true, eval_rest_true] at hsplits
            cases bT with
            | false =>
              -- (true, false): i = 0 works.
              refine ⟨0, by simp, ?_, ?_⟩ <;> rfl
            | true =>
              -- (true, true): both splits in L_true. Recurse.
              rw [eval_sel_true, eval_rest_true] at hT_in_pre
              -- Shape: split_T = (x :: tailSel_T, tailRest_T). Show split_T ∉ L_false.
              have hsplitT_notin_Lfalse : (x :: tailSel_T, tailRest_T) ∉ L_false := by
                intro h
                obtain ⟨⟨a, _⟩, hab, hab_eq⟩ := List.mem_map.mp h
                simp only [Prod.mk.injEq] at hab_eq
                obtain ⟨ha, _⟩ := hab_eq
                exact hx_notin_split_sel hab (ha ▸ List.mem_cons_self)
              -- Decompose hsplits.
              rcases (List.append_eq_append_iff).mp hsplits with
                ⟨e, hpre_eq, hLt_eq⟩ | ⟨e, hLf_eq, _hsuff_eq⟩
              · -- Case 1: pre = L_false ++ e_pre, L_true = e_pre ++ split_S :: suffix.
                rw [hLtrue_def] at hLt_eq
                obtain ⟨preIdx, suffIdx, hsplitsXs', hpreIdx_eq, hsuffIdx_eq⟩ :=
                  List.map_eq_append_iff.mp hLt_eq
                cases suffIdx with
                | nil =>
                  exfalso
                  simp only [List.map_nil] at hsuffIdx_eq
                  exact List.cons_ne_nil _ _ hsuffIdx_eq.symm
                | cons headIdx tailIdx =>
                  simp only [List.map_cons] at hsuffIdx_eq
                  injection hsuffIdx_eq with hsplit_eq _hsuffix_eq
                  simp only [Prod.mk.injEq, List.cons.injEq, true_and] at hsplit_eq
                  obtain ⟨hsel_S_eq, hrest_S_eq⟩ := hsplit_eq
                  obtain ⟨headSel, headRest⟩ := headIdx
                  simp only at hsel_S_eq hrest_S_eq
                  subst hsel_S_eq; subst hrest_S_eq
                  -- Now hsplitsXs' : subsetSplits xs' = preIdx ++ (tailSel_S, tailRest_S) :: tailIdx
                  have hsplitT_in_preIdx : (tailSel_T, tailRest_T) ∈ preIdx := by
                    rw [hpre_eq] at hT_in_pre
                    rw [List.mem_append] at hT_in_pre
                    rcases hT_in_pre with hLf | hE
                    · exact (hsplitT_notin_Lfalse hLf).elim
                    · rw [← hpreIdx_eq] at hE
                      obtain ⟨⟨a, b⟩, hab, hab_eq⟩ := List.mem_map.mp hE
                      simp only [Prod.mk.injEq, List.cons.injEq, true_and] at hab_eq
                      obtain ⟨ha, hb⟩ := hab_eq
                      convert hab
                      · exact ha.symm
                      · exact hb.symm
                  have hSlen' : msS.length = xs'.length := by simpa using hSlen
                  have hTlen' : msT.length = xs'.length := by simpa using hTlen
                  obtain ⟨i', hi', hmsT_i', hmsS_i'⟩ :=
                    ih hxs'_nodup hSlen' hTlen' hsplitsXs' hsplitT_in_preIdx
                  refine ⟨i' + 1, by simp; omega, ?_, ?_⟩
                  · simp only [List.getElem_cons_succ]; exact hmsT_i'
                  · simp only [List.getElem_cons_succ]; exact hmsS_i'
              · -- Case 2: L_false = pre ++ e, split_T ∈ pre ⊆ L_false. Contradiction.
                exfalso
                have hsplitT_in_Lfalse : (x :: tailSel_T, tailRest_T) ∈ L_false := by
                  rw [hLf_eq]; exact List.mem_append_left _ hT_in_pre
                exact hsplitT_notin_Lfalse hsplitT_in_Lfalse

/-- Prefix characterization at the matched-state `subsetSplitsWithFirst`
surface: given an arbitrary executable split `split ∈ pre` appearing before a
chosen matched `S`-split in `Hex.subsetSplitsWithFirst localFactors`, there is
a proof-side lifted-factor subset `T ⊆ J` containing `J.min'` whose
order-preserving `(selected, rest)` partition equals `split`.

Combines the executable-enumeration mask converse
`subsetSplitsWithFirst_mem_exists_tail_mask` with the mask-to-subset lemma
`liftedSubsetSelectedList_eq_mask_partition_of_matches`. Used by the
prefix-none discharge in the recursive coverage proof.

The conclusion is independent of the `S`-side shape constraints (`S ⊆ J` and
`J.min' hne ∈ S`) that the caller typically has in scope: the prefix
characterization is a structural property of the executable enumeration. The
caller call site keeps those hypotheses for the suffix `(S, J \ S)` entry
itself, but does not need to thread them through this lemma. -/
theorem liftedSubsetSplit_prefix_mem_of_matches
    {d : Hex.LiftData} {J S : LiftedFactorSubset d}
    {localFactors : List Hex.ZPoly}
    {pre suffix : List (List Hex.ZPoly × List Hex.ZPoly)}
    (hmatches : LiftedFactorListMatches d J localFactors)
    (hne : J.Nonempty)
    (hsplits :
      Hex.subsetSplitsWithFirst localFactors =
        pre ++
          (liftedSubsetSelectedList d S,
           liftedSubsetSelectedList d (J \ S)) :: suffix)
    {split : List Hex.ZPoly × List Hex.ZPoly} (hsplit : split ∈ pre) :
    ∃ T : LiftedFactorSubset d,
      T ⊆ J ∧ J.min' hne ∈ T ∧
      split = (liftedSubsetSelectedList d T,
               liftedSubsetSelectedList d (J \ T)) := by
  classical
  -- Step 1: lift `hsplit ∈ pre` to membership in the full enumeration.
  have hsplit_mem_all : split ∈ Hex.subsetSplitsWithFirst localFactors := by
    rw [hsplits]
    exact List.mem_append_left _ hsplit
  -- Step 2: decompose `localFactors` as `head :: tail` via the matching predicate.
  have hhead := hmatches.head?_eq_liftedFactor_min' hne
  rcases hloc : localFactors with _ | ⟨head, tail⟩
  · rw [hloc] at hhead; simp at hhead
  rw [hloc] at hsplit_mem_all
  -- Step 3: destructure the split prod.
  obtain ⟨ssel, srest⟩ := split
  -- Step 4: pull out a Boolean tail mask via the executable converse.
  obtain ⟨mask, hmask_len, hsel_eq, hrest_eq⟩ :=
    subsetSplitsWithFirst_mem_exists_tail_mask hsplit_mem_all
  -- Step 5: convert the mask back to a proof-side `LiftedFactorSubset` `T`.
  obtain ⟨T, hTJ, hmin_in_T, hT_sel, hT_rest⟩ :=
    liftedSubsetSelectedList_eq_mask_partition_of_matches
      hmatches hne hloc mask hmask_len
  refine ⟨T, hTJ, hmin_in_T, ?_⟩
  -- Step 6: chain the cons-form equalities to identify `split` with the
  -- `T`-selected/rest pair.
  rw [hsel_eq, hrest_eq, ← hT_sel, ← hT_rest]

/-- Canonical mask decomposition of a matched-state at its head index.

Given that `localFactors` matches `J` and `J` is nonempty, `localFactors`
decomposes as `liftedFactor d (J.min' hne) :: ys.map (liftedFactor d)` for
some `ys` contained in `J`. For any `S ⊆ J` containing `J.min' hne`, the
`(S, J \ S)` partition has the canonical mask form indexed by
`ys.map (· ∈ S)`. -/
private theorem LiftedFactorListMatches.exists_tail_indices
    {d : Hex.LiftData} {J : LiftedFactorSubset d}
    {localFactors : List Hex.ZPoly}
    (hmatches : LiftedFactorListMatches d J localFactors)
    (hne : J.Nonempty) :
    ∃ (ys : List (LiftedFactorIndex d)),
      (∀ y ∈ ys, y ∈ J) ∧
      localFactors = liftedFactor d (J.min' hne) :: ys.map (liftedFactor d) ∧
      ∀ (S : LiftedFactorSubset d), S ⊆ J → J.min' hne ∈ S →
        liftedSubsetSelectedList d S =
          liftedFactor d (J.min' hne) ::
            ((ys.map (liftedFactor d)).zip
                (ys.map (fun i => decide (i ∈ S)))).filterMap
              (fun p => if p.2 then some p.1 else none) ∧
        liftedSubsetSelectedList d (J \ S) =
          ((ys.map (liftedFactor d)).zip
              (ys.map (fun i => decide (i ∈ S)))).filterMap
            (fun p => if p.2 then none else some p.1) := by
  classical
  -- Set up the J-filter index list and decompose at its head.
  set xsIdx : List (LiftedFactorIndex d) :=
    (List.finRange d.liftedFactors.size).filter (fun i => decide (i ∈ J))
    with hxsIdx_def
  have hxsIdx_head : xsIdx.head? = some (J.min' hne) :=
    finRange_filter_head?_eq_min' J hne
  obtain ⟨ys, hxsIdx_eq⟩ : ∃ ys, xsIdx = (J.min' hne) :: ys := by
    cases hxsIdx_case : xsIdx with
    | nil => rw [hxsIdx_case] at hxsIdx_head; simp at hxsIdx_head
    | cons x ys =>
        rw [hxsIdx_case] at hxsIdx_head
        simp only [List.head?_cons, Option.some.injEq] at hxsIdx_head
        exact ⟨ys, by rw [hxsIdx_head]⟩
  refine ⟨ys, ?_, ?_, ?_⟩
  · -- ∀ y ∈ ys, y ∈ J
    intro y hy
    have hy_xsIdx : y ∈ xsIdx := by rw [hxsIdx_eq]; exact List.mem_cons_of_mem _ hy
    rw [hxsIdx_def, List.mem_filter] at hy_xsIdx
    exact of_decide_eq_true hy_xsIdx.2
  · -- localFactors = head :: ys.map liftedFactor
    have : localFactors = xsIdx.map (liftedFactor d) := hmatches
    rw [hxsIdx_eq, List.map_cons] at this
    exact this
  · -- The S-partition canonical mask equations.
    intro S hSJ hmin
    -- Common computation: zip of two maps over the same list.
    have hzip :
        (ys.map (liftedFactor d)).zip (ys.map (fun i => decide (i ∈ S))) =
          ys.map (fun i => (liftedFactor d i, decide (i ∈ S))) := by
      rw [List.zip_map']
    refine ⟨?_, ?_⟩
    · -- liftedSubsetSelectedList d S = head :: filterMap selected
      rw [liftedSubsetSelectedList_eq_filter_map]
      rw [show (List.finRange d.liftedFactors.size).filter
              (fun i => decide (i ∈ S)) =
            xsIdx.filter (fun i => decide (i ∈ S)) from by
        rw [hxsIdx_def]
        exact (finRange_filter_mem_and_mem_eq_of_subset hSJ).symm]
      rw [hxsIdx_eq]
      rw [show (J.min' hne :: ys).filter (fun i => decide (i ∈ S)) =
              J.min' hne :: ys.filter (fun i => decide (i ∈ S)) from
        List.filter_cons_of_pos (by simp [hmin])]
      rw [List.map_cons]
      congr 1
      rw [hzip, List.filterMap_map]
      simp only [Function.comp_def]
      exact (List.filterMap_if_eq_map_filter ys
        (fun i => decide (i ∈ S)) (liftedFactor d)).symm
    · -- liftedSubsetSelectedList d (J \ S) = filterMap rest
      rw [liftedSubsetSelectedList_eq_filter_map]
      rw [show (List.finRange d.liftedFactors.size).filter
              (fun i => decide (i ∈ J \ S)) =
            xsIdx.filter (fun i => decide (i ∉ S)) from by
        rw [hxsIdx_def]
        exact (finRange_filter_mem_and_not_mem_eq_sdiff_of_subset
          (J := J) (S := S)).symm]
      rw [hxsIdx_eq]
      rw [show (J.min' hne :: ys).filter (fun i => decide (i ∉ S)) =
              ys.filter (fun i => decide (i ∉ S)) from
        List.filter_cons_of_neg (by simp [hmin])]
      rw [hzip, List.filterMap_map]
      simp only [Function.comp_def]
      have hrewrite :
          (fun i : LiftedFactorIndex d =>
              if decide (i ∈ S) then (none : Option Hex.ZPoly)
              else some (liftedFactor d i)) =
            fun i => if decide (i ∉ S) then some (liftedFactor d i) else none := by
        funext i
        by_cases hi : i ∈ S
        · simp [hi]
        · simp [hi]
      rw [hrewrite]
      exact (List.filterMap_if_eq_map_filter ys
        (fun i => decide (i ∉ S)) (liftedFactor d)).symm

/-- Strengthening of `liftedSubsetSplit_prefix_mem_of_matches`: when the
matched `localFactors` is `Nodup` and the boundary split is the canonical
`(S, J \ S)` partition, every prefix `split ∈ pre` admits a witness index
`i ∈ J ∩ S` that is **not** in the recovered subset `T`.

The `Nodup` hypothesis is required to lift the executable mask-level bit
difference (provided by `subsetSplits_prefix_exists_bit_diff_aux`) back to a
proof-side `LiftedFactorIndex d` difference, since `liftedFactor d` is
otherwise allowed to collide on distinct indices. Callers thread this
hypothesis from a Hensel-coprimality fact at the recombination call site
(`liftedFactor d` injective on the J-filter index list).

Used by the recursive coverage assembler for the prefix-none case: an
arbitrary executable split appearing before the `S`-split must miss at least
one of the `S`-indices, witnessing recombination-search progress. -/
theorem liftedSubsetSplit_prefix_exists_mem_sdiff_of_matches
    {d : Hex.LiftData} {J S : LiftedFactorSubset d}
    {localFactors : List Hex.ZPoly}
    {pre suffix : List (List Hex.ZPoly × List Hex.ZPoly)}
    (hlocal_nodup : localFactors.Nodup)
    (hmatches : LiftedFactorListMatches d J localFactors)
    (hSJ : S ⊆ J) (hne : J.Nonempty) (hmin : J.min' hne ∈ S)
    (hsplits :
      Hex.subsetSplitsWithFirst localFactors =
        pre ++
          (liftedSubsetSelectedList d S,
           liftedSubsetSelectedList d (J \ S)) :: suffix)
    {split : List Hex.ZPoly × List Hex.ZPoly} (hsplit : split ∈ pre) :
    ∃ (T : LiftedFactorSubset d),
      T ⊆ J ∧ J.min' hne ∈ T ∧
      split = (liftedSubsetSelectedList d T,
               liftedSubsetSelectedList d (J \ T)) ∧
      ∃ i ∈ J, i ∈ S ∧ i ∉ T := by
  classical
  -- Step 1: get T from the prefix-mem lemma.
  obtain ⟨T, hTJ, hmin_in_T, hsplit_eq⟩ :=
    liftedSubsetSplit_prefix_mem_of_matches hmatches hne hsplits hsplit
  refine ⟨T, hTJ, hmin_in_T, hsplit_eq, ?_⟩
  -- Step 2: decompose localFactors and obtain canonical mask equations.
  obtain ⟨ys, hys_in_J, hloc_eq, hS_eqs⟩ :=
    hmatches.exists_tail_indices hne
  obtain ⟨hS_sel_cons, hS_rest_eq⟩ := hS_eqs S hSJ hmin
  obtain ⟨hT_sel_cons, hT_rest_eq⟩ := hS_eqs T hTJ hmin_in_T
  -- Useful abbreviations.
  set head : Hex.ZPoly := liftedFactor d (J.min' hne)
  set tail : List Hex.ZPoly := ys.map (liftedFactor d)
  set mask_S : List Bool := ys.map (fun i => decide (i ∈ S)) with hmask_S_def
  set mask_T : List Bool := ys.map (fun i => decide (i ∈ T)) with hmask_T_def
  have hmask_S_len : mask_S.length = tail.length := by
    simp [hmask_S_def, tail]
  have hmask_T_len : mask_T.length = tail.length := by
    simp [hmask_T_def, tail]
  -- Tail Nodup (from hlocal_nodup).
  rw [hloc_eq] at hlocal_nodup
  have htail_nodup : tail.Nodup := (List.nodup_cons.mp hlocal_nodup).2
  -- Step 3: lift `hsplits` to a `subsetSplits tail` decomposition.
  have hsswf_eq :
      Hex.subsetSplitsWithFirst localFactors =
        (Hex.subsetSplits tail).map (fun s => (head :: s.1, s.2)) := by
    rw [hloc_eq]
    show (Hex.subsetSplits tail).map _ = _
    rfl
  -- The boundary split (S-sel, (J\S)-sel) in the cons-canonical form.
  have hS_boundary_eq :
      (liftedSubsetSelectedList d S, liftedSubsetSelectedList d (J \ S)) =
        (fun s : List Hex.ZPoly × List Hex.ZPoly => (head :: s.1, s.2))
          ((tail.zip mask_S).filterMap (fun p => if p.2 then some p.1 else none),
           (tail.zip mask_S).filterMap (fun p => if p.2 then none else some p.1)) := by
    simp only [Prod.mk.injEq]
    refine ⟨?_, ?_⟩
    · rw [hS_sel_cons]
    · rw [hS_rest_eq]
  rw [hsswf_eq, hS_boundary_eq] at hsplits
  -- Apply List.map_eq_append_iff to get a decomposition of subsetSplits tail.
  obtain ⟨preIdx, suffIdx, hsplitsTail, hpreIdx_eq, hsuffIdx_eq⟩ :=
    List.map_eq_append_iff.mp hsplits
  cases suffIdx with
  | nil =>
      exfalso
      simp only [List.map_nil] at hsuffIdx_eq
      exact List.cons_ne_nil _ _ hsuffIdx_eq.symm
  | cons headIdx tailIdx =>
      simp only [List.map_cons] at hsuffIdx_eq
      injection hsuffIdx_eq with hboundary_eq _hsuffix_map_eq
      -- hboundary_eq : (head :: headIdx.1, headIdx.2) =
      --   (head :: mask_S filterMap selected, mask_S filterMap rest)
      simp only [Prod.mk.injEq, List.cons.injEq, true_and] at hboundary_eq
      obtain ⟨hheadIdx_sel, hheadIdx_rest⟩ := hboundary_eq
      obtain ⟨headIdxSel, headIdxRest⟩ := headIdx
      simp only at hheadIdx_sel hheadIdx_rest
      subst hheadIdx_sel
      subst hheadIdx_rest
      -- hsplitsTail : subsetSplits tail =
      --   preIdx ++ ((tail.zip mask_S).filterMap selected,
      --              (tail.zip mask_S).filterMap rest) :: tailIdx
      -- Step 4: identify split = f((tail.zip mask_T).filterMap selected, ...).
      have hsplit_eq_canonical :
          split = (fun s : List Hex.ZPoly × List Hex.ZPoly => (head :: s.1, s.2))
            ((tail.zip mask_T).filterMap (fun p => if p.2 then some p.1 else none),
             (tail.zip mask_T).filterMap (fun p => if p.2 then none else some p.1)) := by
        rw [hsplit_eq]
        simp only [Prod.mk.injEq]
        refine ⟨?_, ?_⟩
        · rw [hT_sel_cons]
        · rw [hT_rest_eq]
      -- pre = preIdx.map f and split ∈ pre.
      rw [← hpreIdx_eq] at hsplit
      rw [hsplit_eq_canonical] at hsplit
      obtain ⟨innerT, hinnerT_mem, hinnerT_eq⟩ := List.mem_map.mp hsplit
      -- innerT ∈ preIdx and f(innerT) = f(canonical_T_inner). By injectivity, innerT =
      -- canonical_T_inner.
      simp only [Prod.mk.injEq, List.cons.injEq, true_and] at hinnerT_eq
      obtain ⟨hT_inner_sel_eq, hT_inner_rest_eq⟩ := hinnerT_eq
      obtain ⟨innerTSel, innerTRest⟩ := innerT
      simp only at hT_inner_sel_eq hT_inner_rest_eq
      subst hT_inner_sel_eq
      subst hT_inner_rest_eq
      -- innerT-canonical ∈ preIdx.
      -- Step 5: apply the mask-level helper.
      obtain ⟨i', hi', hmsT_i', hmsS_i'⟩ :=
        subsetSplits_prefix_exists_bit_diff_aux htail_nodup
          hmask_S_len hmask_T_len hsplitsTail hinnerT_mem
      -- Step 6: translate i' to ys[i'].
      have hi'_ys : i' < ys.length := by
        have : tail.length = ys.length := by simp [tail]
        rw [this] at hi'
        exact hi'
      refine ⟨ys[i'], ?_, ?_, ?_⟩
      · exact hys_in_J ys[i'] (List.getElem_mem _)
      · -- ys[i'] ∈ S, from mask_S[i'] = true.
        have h_mask_S_val : mask_S[i'] = decide (ys[i'] ∈ S) := by
          simp [hmask_S_def]
        have : decide (ys[i'] ∈ S) = true := by
          rw [← h_mask_S_val]
          exact hmsS_i'
        exact of_decide_eq_true this
      · -- ys[i'] ∉ T, from mask_T[i'] = false.
        have h_mask_T_val : mask_T[i'] = decide (ys[i'] ∈ T) := by
          simp [hmask_T_def]
        have : decide (ys[i'] ∈ T) = false := by
          rw [← h_mask_T_val]
          exact hmsT_i'
        exact of_decide_eq_false this

/-- The transported recombination candidate product equals the proof-side
lifted-factor product: both factor lists are permutations of each other in
`Polynomial ℤ`, so commutativity collapses the order difference. -/
theorem polyProduct_liftedSubsetSelectedList_eq_liftedFactorProduct
    (d : Hex.LiftData) (S : LiftedFactorSubset d) :
    Array.polyProduct (liftedSubsetSelectedList d S).toArray =
      liftedFactorProduct d S := by
  apply HexPolyZMathlib.equiv.injective
  show HexPolyZMathlib.toPolynomial _ = HexPolyZMathlib.toPolynomial _
  rw [polyProduct_toPolynomial, liftedSubsetSelectedList_eq_filter_map]
  -- LHS: ((((List.finRange n).filter (· ∈ S)).map (liftedFactor d)).map toPolynomial).prod
  rw [List.map_map]
  -- LHS: (((List.finRange n).filter (· ∈ S)).map (toPolynomial ∘ liftedFactor d)).prod
  -- Now compute RHS.
  unfold liftedFactorProduct
  rw [show (S.toList.foldl (fun acc i => acc * liftedFactor d i) (1 : Hex.ZPoly)) =
        (S.toList.map (liftedFactor d)).foldl (· * ·) 1 from by
    rw [List.foldl_map]]
  rw [toPolynomial_foldl_mul, toPolynomial_one_zpoly, ← List.prod_eq_foldl, List.map_map]
  -- Now both sides are List.prod over (... .map (toPolynomial ∘ liftedFactor d))
  apply List.Perm.prod_eq
  apply List.Perm.map
  exact finRange_filter_mem_perm_toList S

/-- When index `0` is in `S`, the lifted-factor subset partition lies in the
`subsetSplitsWithFirst` enumeration that the recombination search iterates. -/
theorem liftedSubsetSplit_mem_subsetSplitsWithFirst
    (d : Hex.LiftData) (S : LiftedFactorSubset d)
    (hpos : 0 < d.liftedFactors.size)
    (h0 : (⟨0, hpos⟩ : LiftedFactorIndex d) ∈ S) :
    (liftedSubsetSelectedList d S, liftedSubsetRejectedList d S) ∈
      Hex.subsetSplitsWithFirst d.liftedFactors.toList := by
  unfold liftedSubsetSelectedList liftedSubsetRejectedList
  -- Decompose d.liftedFactors.toList and the mask into cons forms.
  have hxs_pos : 0 < d.liftedFactors.toList.length := by simpa using hpos
  have hmask_len := liftedSubsetMask_length d S
  have hmask_head := liftedSubsetMask_head?_eq_decide d S hpos
  rcases hxs : d.liftedFactors.toList with _ | ⟨x, xs⟩
  · rw [hxs] at hxs_pos; simp at hxs_pos
  rcases hmask : liftedSubsetMask d S with _ | ⟨b, bs⟩
  · rw [hmask] at hmask_head; simp at hmask_head
  -- Head bit is determined by `h0`.
  rw [hmask] at hmask_head
  simp [h0] at hmask_head
  -- `hmask_head : b = true`
  subst hmask_head
  -- Lengths line up.
  have hbs_len : bs.length = xs.length := by
    rw [hmask, hxs] at hmask_len
    simpa using hmask_len
  exact subsetSplitsWithFirst_zip_filterMap_partition x xs bs hbs_len

end

end HexBerlekampZassenhausMathlib
