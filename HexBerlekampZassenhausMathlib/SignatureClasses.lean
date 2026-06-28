/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import HexBerlekampZassenhaus
import Mathlib.Data.Nat.Find

/-!
Partition semantics for the executable `bhksInsertSignatureClass` fold.

The executable BHKS equivalence-class identifier
`Hex.bhksEquivalenceClassIndicators` groups column indices `0, …, r-1`
by their echelon-column signatures, using a single left-fold over
`List.range r` driven by `Hex.bhksInsertSignatureClass`.  This module
characterises the output of that fold as a canonical
filter-based partition: the classes are the equivalence classes of
`j ~ k iff sig j = sig k`, emitted in order of first occurrence by
ascending column index, with each class's member list ascending.

The B7 indicator correspondence consumes this fact to match the executable
indicator output against the noncomputable, support-driven canonical
indicator array.
-/

namespace HexBerlekampZassenhausMathlib

namespace BHKS

/--
Representative columns for the `sig j = sig k` equivalence on
`{0, …, r-1}`: the columns whose signature has not been seen at any
earlier column. The list is ascending by construction.
-/
def representativeColumns (r : Nat) (sig : Nat → Array Rat) : List Nat :=
  (List.range r).filter
    (fun j => ((List.range j).filter (fun k => sig k = sig j)).isEmpty)

/--
Canonical partition of `{0, …, r-1}` by signature equivalence: one
class per representative column, listing exactly the columns with the
same signature as that representative.  Classes appear in ascending
representative order; each class's member list is ascending.
-/
def partitionByMinColumn (r : Nat) (sig : Nat → Array Rat) : List (List Nat) :=
  (representativeColumns r sig).map
    (fun rep => (List.range r).filter (fun j => sig j = sig rep))

/--
The full `(signature, members)` payload after folding
`Hex.bhksInsertSignatureClass` over `List.range r`.  Each pair pairs a
representative column's signature with the ascending list of columns
sharing that signature.
-/
def partitionAcc (r : Nat) (sig : Nat → Array Rat) :
    List (Array Rat × List Nat) :=
  (representativeColumns r sig).map
    (fun rep =>
      (sig rep, (List.range r).filter (fun j => sig j = sig rep)))

theorem partitionAcc_map_snd (r : Nat) (sig : Nat → Array Rat) :
    (partitionAcc r sig).map Prod.snd = partitionByMinColumn r sig := by
  unfold partitionAcc partitionByMinColumn
  simp [List.map_map, Function.comp]

/--
If no entry of `acc` carries signature `s`, then
`Hex.bhksInsertSignatureClass s j acc` appends `(s, [j])` at the end.
-/
theorem bhksInsertSignatureClass_eq_append
    (s : Array Rat) (j : Nat) (acc : List (Array Rat × List Nat))
    (hnotin : ∀ p ∈ acc, p.1 ≠ s) :
    Hex.bhksInsertSignatureClass s j acc = acc ++ [(s, [j])] := by
  induction acc with
  | nil => simp [Hex.bhksInsertSignatureClass]
  | cons p rest ih =>
      obtain ⟨s', members⟩ := p
      have hs' : s' ≠ s := hnotin (s', members) (List.mem_cons_self ..)
      have hrest : ∀ p ∈ rest, p.1 ≠ s := fun p hp =>
        hnotin p (List.mem_cons_of_mem _ hp)
      simp [Hex.bhksInsertSignatureClass, hs', ih hrest]

/--
If `acc = l ++ (s, members) :: r` and no entry of `l` carries
signature `s`, then `Hex.bhksInsertSignatureClass s j acc` replaces the
single matching entry's member list with `members ++ [j]`.
-/
theorem bhksInsertSignatureClass_eq_replace
    (s : Array Rat) (j : Nat)
    (l r : List (Array Rat × List Nat)) (members : List Nat)
    (hnotin : ∀ p ∈ l, p.1 ≠ s) :
    Hex.bhksInsertSignatureClass s j (l ++ (s, members) :: r) =
      l ++ (s, members ++ [j]) :: r := by
  induction l with
  | nil => simp [Hex.bhksInsertSignatureClass]
  | cons p l' ih =>
      obtain ⟨s', members'⟩ := p
      have hs' : s' ≠ s := hnotin (s', members') (List.mem_cons_self ..)
      have hl' : ∀ p ∈ l', p.1 ≠ s := fun p hp =>
        hnotin p (List.mem_cons_of_mem _ hp)
      have := ih hl'
      simp [Hex.bhksInsertSignatureClass, hs', this]

theorem representativeColumns_succ_of_fresh
    (m : Nat) (sig : Nat → Array Rat)
    (hfresh : ∀ k, k < m → sig k ≠ sig m) :
    representativeColumns (m + 1) sig =
      representativeColumns m sig ++ [m] := by
  unfold representativeColumns
  rw [List.range_succ, List.filter_append]
  -- The filter applied to [m]: m is a new rep iff no earlier k has sig k = sig m.
  have hempty : ((List.range m).filter (fun k => sig k = sig m)) = [] := by
    apply List.eq_nil_iff_forall_not_mem.mpr
    intro k hk
    rw [List.mem_filter] at hk
    rcases hk with ⟨hmem, hsig⟩
    rw [List.mem_range] at hmem
    exact (hfresh k hmem) (by simpa using hsig)
  have hsuffix : (List.filter
      (fun j => ((List.range j).filter (fun k => sig k = sig j)).isEmpty)
      [m]) = [m] := by
    simp [List.filter, hempty]
  rw [hsuffix]

theorem representativeColumns_succ_of_match
    (m : Nat) (sig : Nat → Array Rat)
    (k₀ : Nat) (hk₀ : k₀ < m) (hsig : sig k₀ = sig m) :
    representativeColumns (m + 1) sig =
      representativeColumns m sig := by
  unfold representativeColumns
  rw [List.range_succ, List.filter_append]
  -- The trailing [m] gets filtered out because some k < m has sig k = sig m.
  have hnotempty :
      ((List.range m).filter (fun k => sig k = sig m)) ≠ [] := by
    intro hnil
    have hmem : k₀ ∈ (List.range m).filter (fun k => sig k = sig m) := by
      rw [List.mem_filter]
      refine ⟨List.mem_range.mpr hk₀, ?_⟩
      simpa using hsig
    rw [hnil] at hmem
    exact List.not_mem_nil hmem
  have hisEmpty :
      ((List.range m).filter (fun k => sig k = sig m)).isEmpty = false := by
    rw [Bool.eq_false_iff]
    intro h
    apply hnotempty
    exact List.isEmpty_iff.mp h
  have hsuffix : (List.filter
      (fun j => ((List.range j).filter (fun k => sig k = sig j)).isEmpty)
      [m]) = [] := by
    simp [List.filter, hisEmpty]
  rw [hsuffix, List.append_nil]

theorem mem_representativeColumns_iff
    (m : Nat) (sig : Nat → Array Rat) (rep : Nat) :
    rep ∈ representativeColumns m sig ↔
      rep < m ∧ ∀ k, k < rep → sig k ≠ sig rep := by
  unfold representativeColumns
  rw [List.mem_filter]
  simp only [List.mem_range, List.isEmpty_iff]
  constructor
  · rintro ⟨hlt, hfilter⟩
    refine ⟨hlt, ?_⟩
    intro k hk hsigeq
    have : k ∈ (List.range rep).filter (fun k => sig k = sig rep) := by
      rw [List.mem_filter]
      refine ⟨List.mem_range.mpr hk, ?_⟩
      simpa using hsigeq
    rw [hfilter] at this
    exact List.not_mem_nil this
  · rintro ⟨hlt, hfresh⟩
    refine ⟨hlt, ?_⟩
    apply List.eq_nil_iff_forall_not_mem.mpr
    intro k hk
    rw [List.mem_filter] at hk
    rcases hk with ⟨hmem, hsig⟩
    rw [List.mem_range] at hmem
    exact hfresh k hmem (by simpa using hsig)

theorem representativeColumns_lt (m : Nat) (sig : Nat → Array Rat) (rep : Nat)
    (h : rep ∈ representativeColumns m sig) : rep < m :=
  ((mem_representativeColumns_iff m sig rep).mp h).1

theorem representativeColumns_fresh (m : Nat) (sig : Nat → Array Rat) (rep : Nat)
    (h : rep ∈ representativeColumns m sig) :
    ∀ k, k < rep → sig k ≠ sig rep :=
  ((mem_representativeColumns_iff m sig rep).mp h).2

/--
Representatives in `representativeColumns m sig` carry pairwise
distinct signatures: each rep's signature first appears at that rep.
-/
theorem representativeColumns_distinct_sig
    (m : Nat) (sig : Nat → Array Rat)
    {rep₁ rep₂ : Nat}
    (_h₁ : rep₁ ∈ representativeColumns m sig)
    (h₂ : rep₂ ∈ representativeColumns m sig)
    (hlt : rep₁ < rep₂) :
    sig rep₁ ≠ sig rep₂ :=
  representativeColumns_fresh m sig rep₂ h₂ rep₁ hlt

/-- Filtering `List.range (m + 1)` splits as filtering range `m` plus
the trailing element. -/
theorem filter_range_succ (m : Nat) (p : Nat → Bool) :
    (List.range (m + 1)).filter p =
      (List.range m).filter p ++ (if p m then [m] else []) := by
  rw [List.range_succ, List.filter_append]
  congr 1
  by_cases hpm : p m
  · simp [List.filter, hpm]
  · simp [List.filter, hpm]

/-- The members list of the entry for `rep` in `partitionAcc (m + 1) sig`
factors as the members at step `m` plus `m` itself if `sig m = sig rep`. -/
theorem filter_range_succ_sig_eq (m : Nat) (sig : Nat → Array Rat) (rep : Nat) :
    (List.range (m + 1)).filter (fun j => sig j = sig rep) =
      (List.range m).filter (fun j => sig j = sig rep) ++
        (if sig m = sig rep then [m] else []) := by
  have := filter_range_succ m (fun j => decide (sig j = sig rep))
  -- Match the shape `fun j => sig j = sig rep` and `if sig m = sig rep`.
  simpa using this

/-- If signatures are decidably distinct at `rep` and `m`, the
`partitionAcc m sig` entry for `rep` extends trivially to step `m + 1`. -/
theorem partitionAcc_entry_eq_of_ne
    (m : Nat) (sig : Nat → Array Rat) (rep : Nat)
    (hne : sig m ≠ sig rep) :
    (sig rep, (List.range (m + 1)).filter (fun j => sig j = sig rep)) =
      (sig rep, (List.range m).filter (fun j => sig j = sig rep)) := by
  rw [filter_range_succ_sig_eq]
  simp [hne]

/--
Decompose `representativeColumns m sig` around a known representative
`k₀ ∈ representativeColumns m sig`.  The list splits as the
`representativeColumns k₀ sig` prefix, then `k₀`, then a suffix of reps
in `(k₀, m)`.
-/
theorem representativeColumns_decompose_at
    (m : Nat) (sig : Nat → Array Rat)
    (k₀ : Nat) (hk₀ : k₀ ∈ representativeColumns m sig) :
    ∃ suffix : List Nat,
      representativeColumns m sig =
        representativeColumns k₀ sig ++ k₀ :: suffix ∧
      (∀ rep ∈ suffix, k₀ < rep ∧ rep ∈ representativeColumns m sig) := by
  have hk₀_lt : k₀ < m := representativeColumns_lt m sig k₀ hk₀
  have hk₀_fresh : ∀ k, k < k₀ → sig k ≠ sig k₀ :=
    representativeColumns_fresh m sig k₀ hk₀
  -- Split List.range m at k₀:
  -- List.range m = List.range k₀ ++ k₀ :: List.range' (k₀+1) (m - k₀ - 1)
  let rest : List Nat := List.range' (k₀ + 1) (m - k₀ - 1)
  have hrange_split : List.range m = List.range k₀ ++ k₀ :: rest := by
    have hk_le : k₀ ≤ m := Nat.le_of_lt hk₀_lt
    have h1 : List.range m = List.range k₀ ++ List.range' k₀ (m - k₀) := by
      rw [List.range_eq_range', List.range_eq_range']
      have hsum : (k₀ + (m - k₀)) = m := by omega
      rw [← hsum]
      rw [← List.range'_append_1]
      simp
    have hmk : List.range' k₀ (m - k₀) = k₀ :: List.range' (k₀ + 1) (m - k₀ - 1) := by
      cases hd : m - k₀ with
      | zero => omega
      | succ n =>
          show List.range' k₀ (n + 1) = k₀ :: List.range' (k₀ + 1) n
          rfl
    rw [h1, hmk]
  refine ⟨rest.filter (fun j =>
    ((List.range j).filter (fun k => sig k = sig j)).isEmpty), ?_, ?_⟩
  · unfold representativeColumns
    rw [hrange_split, List.filter_append]
    -- k₀ is a rep of itself: ((range k₀).filter (sig · = sig k₀)).isEmpty
    have hk₀_pred :
        ((List.range k₀).filter (fun k => sig k = sig k₀)).isEmpty = true := by
      rw [List.isEmpty_iff]
      apply List.eq_nil_iff_forall_not_mem.mpr
      intro k hk
      rw [List.mem_filter] at hk
      rcases hk with ⟨hmem, hsig⟩
      rw [List.mem_range] at hmem
      exact (hk₀_fresh k hmem) (by simpa using hsig)
    rw [List.filter_cons]
    rw [if_pos (by simpa using hk₀_pred)]
  · intro rep hrep
    rw [List.mem_filter] at hrep
    rcases hrep with ⟨hmem, hpred⟩
    refine ⟨?_, ?_⟩
    · -- rep > k₀ from List.range' (k₀+1) ...
      have : rep ∈ List.range' (k₀ + 1) (m - k₀ - 1) := hmem
      rw [List.mem_range'] at this
      omega
    · unfold representativeColumns
      rw [List.mem_filter]
      have hrep_lt : rep < m := by
        have : rep ∈ List.range' (k₀ + 1) (m - k₀ - 1) := hmem
        rw [List.mem_range'] at this
        omega
      exact ⟨List.mem_range.mpr hrep_lt, hpred⟩

/-- Inductive step: `partitionAcc (m + 1) sig` is obtained by feeding
`(sig m, m)` through `Hex.bhksInsertSignatureClass` on top of
`partitionAcc m sig`, assuming `sig m` has not been seen earlier. -/
private theorem partitionAcc_succ_of_fresh
    (m : Nat) (sig : Nat → Array Rat)
    (hfresh : ∀ k, k < m → sig k ≠ sig m) :
    partitionAcc (m + 1) sig =
      Hex.bhksInsertSignatureClass (sig m) m (partitionAcc m sig) := by
  -- No entry of `partitionAcc m sig` has signature `sig m`.
  have hnotin : ∀ p ∈ partitionAcc m sig, p.1 ≠ sig m := by
    intro p hp
    unfold partitionAcc at hp
    rw [List.mem_map] at hp
    obtain ⟨rep, hrep_mem, hrep_eq⟩ := hp
    subst hrep_eq
    have hrep_lt : rep < m := representativeColumns_lt m sig rep hrep_mem
    exact hfresh rep hrep_lt
  rw [bhksInsertSignatureClass_eq_append (sig m) m _ hnotin]
  -- Now show: partitionAcc (m+1) sig = partitionAcc m sig ++ [(sig m, [m])]
  unfold partitionAcc
  rw [representativeColumns_succ_of_fresh m sig hfresh, List.map_append]
  congr 1
  · -- prefix: each rep < m, so sig m ≠ sig rep, so the filter at m+1 equals filter at m.
    apply List.map_congr_left
    intro rep hrep
    have hrep_lt : rep < m := representativeColumns_lt m sig rep hrep
    have hne : sig m ≠ sig rep := (hfresh rep hrep_lt).symm
    exact partitionAcc_entry_eq_of_ne m sig rep hne
  · -- the trailing [m] entry produces (sig m, [m])
    simp only [List.map_cons, List.map_nil]
    congr 1
    rw [filter_range_succ_sig_eq]
    have hfilter : (List.range m).filter (fun j => sig j = sig m) = [] := by
      apply List.eq_nil_iff_forall_not_mem.mpr
      intro k hk
      rw [List.mem_filter] at hk
      rcases hk with ⟨hmem, hsig⟩
      rw [List.mem_range] at hmem
      exact (hfresh k hmem) (by simpa using hsig)
    simp [hfilter]

/-- Inductive step (matching case): `partitionAcc (m + 1) sig` extends
the `partitionAcc m sig` entry at the minimum matching representative
`k₀` by appending `m` to its member list. -/
private theorem partitionAcc_succ_of_match
    (m : Nat) (sig : Nat → Array Rat)
    (k₀ : Nat) (hk₀_lt : k₀ < m) (hk₀_sig : sig k₀ = sig m)
    (hk₀_min : ∀ k, k < k₀ → sig k ≠ sig m) :
    partitionAcc (m + 1) sig =
      Hex.bhksInsertSignatureClass (sig m) m (partitionAcc m sig) := by
  -- k₀ is in representativeColumns m sig, since no earlier k has the same signature.
  have hk₀_fresh : ∀ k, k < k₀ → sig k ≠ sig k₀ := by
    intro k hk hsig
    apply hk₀_min k hk
    rw [hsig, hk₀_sig]
  have hk₀_rep : k₀ ∈ representativeColumns m sig := by
    rw [mem_representativeColumns_iff]
    exact ⟨hk₀_lt, hk₀_fresh⟩
  obtain ⟨suffix, hdecomp, hsuffix_props⟩ :=
    representativeColumns_decompose_at m sig k₀ hk₀_rep
  -- Members at step m for k₀ and at step m+1.
  let p : Nat → Array Rat × List Nat :=
    fun rep => (sig rep, (List.range m).filter (fun j => sig j = sig rep))
  let p' : Nat → Array Rat × List Nat :=
    fun rep => (sig rep, (List.range (m + 1)).filter (fun j => sig j = sig rep))
  -- Sig of suffix reps differs from sig m, by representativeColumns_fresh.
  have hsuffix_sig_ne : ∀ rep ∈ suffix, sig rep ≠ sig m := by
    intro rep hrep
    rcases hsuffix_props rep hrep with ⟨hgt, hmem⟩
    intro heq
    have : sig k₀ ≠ sig rep := by
      apply representativeColumns_fresh m sig rep hmem
      exact hgt
    apply this
    rw [hk₀_sig, ← heq]
  have hsuffix_sig_ne_sig_k₀ : ∀ rep ∈ suffix, sig m ≠ sig rep := by
    intro rep hrep heq
    exact hsuffix_sig_ne rep hrep heq.symm
  have hprefix_sig_ne : ∀ rep ∈ representativeColumns k₀ sig, sig rep ≠ sig m := by
    intro rep hrep
    have hrep_lt : rep < k₀ := representativeColumns_lt k₀ sig rep hrep
    exact hk₀_min rep hrep_lt
  have hprefix_sig_ne_sig_m : ∀ rep ∈ representativeColumns k₀ sig, sig m ≠ sig rep := by
    intro rep hrep heq
    exact hprefix_sig_ne rep hrep heq.symm
  -- Set up the partitionAcc m sig decomposition.
  have hpAcc_m : partitionAcc m sig =
      (representativeColumns k₀ sig).map p ++ p k₀ :: suffix.map p := by
    unfold partitionAcc
    rw [hdecomp, List.map_append, List.map_cons]
  -- Apply bhksInsertSignatureClass_eq_replace.
  -- First, the prefix entries have signature ≠ sig m.
  have hprefix_pred :
      ∀ q ∈ (representativeColumns k₀ sig).map p, q.1 ≠ sig m := by
    intro q hq
    rw [List.mem_map] at hq
    obtain ⟨rep, hrep_mem, hrep_eq⟩ := hq
    subst hrep_eq
    exact hprefix_sig_ne rep hrep_mem
  -- The entry at k₀ has signature sig k₀ = sig m; rewrite the form needed by the lemma.
  have hp_k₀ : p k₀ =
      (sig m, (List.range m).filter (fun j => sig j = sig k₀)) := by
    simp only [p, hk₀_sig]
  -- The substituted form: prefix.map p ++ (sig m, members) :: suffix.map p
  have hpAcc_m_normalized : partitionAcc m sig =
      (representativeColumns k₀ sig).map p ++
        (sig m, (List.range m).filter (fun j => sig j = sig k₀)) :: suffix.map p := by
    rw [hpAcc_m, hp_k₀]
  -- Each prefix entry: p' rep = p rep when sig m ≠ sig rep.
  have hprefix_eq : (representativeColumns k₀ sig).map p' =
      (representativeColumns k₀ sig).map p := by
    apply List.map_congr_left
    intro rep hrep
    have hne : sig m ≠ sig rep := hprefix_sig_ne_sig_m rep hrep
    show p' rep = p rep
    exact partitionAcc_entry_eq_of_ne m sig rep hne
  -- The k₀ entry: p' k₀ = (sig m, members ++ [m])
  have hp'_k₀ : p' k₀ =
      (sig m, (List.range m).filter (fun j => sig j = sig k₀) ++ [m]) := by
    show (sig k₀, (List.range (m + 1)).filter (fun j => sig j = sig k₀)) =
         (sig m, (List.range m).filter (fun j => sig j = sig k₀) ++ [m])
    rw [filter_range_succ_sig_eq, if_pos hk₀_sig.symm, hk₀_sig]
  -- Each suffix entry: p' rep = p rep when sig m ≠ sig rep.
  have hsuffix_eq : suffix.map p' = suffix.map p := by
    apply List.map_congr_left
    intro rep hrep
    have hne : sig m ≠ sig rep := hsuffix_sig_ne_sig_k₀ rep hrep
    show p' rep = p rep
    exact partitionAcc_entry_eq_of_ne m sig rep hne
  -- Apply Lemma B.
  rw [hpAcc_m_normalized]
  rw [bhksInsertSignatureClass_eq_replace (sig m) m _ _ _ hprefix_pred]
  -- Now match the LHS via partitionAcc (m+1) sig unfolded.
  show ((representativeColumns (m + 1) sig).map p') =
       (representativeColumns k₀ sig).map p ++
         (sig m, (List.range m).filter (fun j => sig j = sig k₀) ++ [m]) :: suffix.map p
  rw [representativeColumns_succ_of_match m sig k₀ hk₀_lt hk₀_sig]
  rw [hdecomp, List.map_append, List.map_cons]
  rw [hprefix_eq, hsuffix_eq, hp'_k₀]

/-- The inductive step: `partitionAcc (m + 1) sig` is one
`bhksInsertSignatureClass` application above `partitionAcc m sig`. -/
theorem partitionAcc_succ (m : Nat) (sig : Nat → Array Rat) :
    partitionAcc (m + 1) sig =
      Hex.bhksInsertSignatureClass (sig m) m (partitionAcc m sig) := by
  classical
  by_cases hex : ∃ k, k < m ∧ sig k = sig m
  · let k₀ := Nat.find hex
    have hk₀_spec := Nat.find_spec hex
    have hk₀_min : ∀ k, k < k₀ → ¬ (k < m ∧ sig k = sig m) := fun k hk =>
      Nat.find_min hex hk
    have hk₀_min' : ∀ k, k < k₀ → sig k ≠ sig m := by
      intro k hk hsig
      apply hk₀_min k hk
      exact ⟨lt_trans hk hk₀_spec.1, hsig⟩
    exact partitionAcc_succ_of_match m sig k₀ hk₀_spec.1 hk₀_spec.2 hk₀_min'
  · have hfresh : ∀ k, k < m → sig k ≠ sig m := by
      intro k hk hsig
      exact hex ⟨k, hk, hsig⟩
    exact partitionAcc_succ_of_fresh m sig hfresh

/-- The fold over `List.range r` of `Hex.bhksInsertSignatureClass` produces
exactly the canonical partition accumulator. -/
theorem foldl_bhksInsertSignatureClass_eq_partitionAcc
    (r : Nat) (sig : Nat → Array Rat) :
    (List.range r).foldl
      (fun acc j => Hex.bhksInsertSignatureClass (sig j) j acc) [] =
      partitionAcc r sig := by
  induction r with
  | zero =>
      unfold partitionAcc representativeColumns
      simp
  | succ r ih =>
      rw [List.range_succ, List.foldl_append]
      rw [show ([r] : List Nat).foldl
            (fun acc j => Hex.bhksInsertSignatureClass (sig j) j acc)
            ((List.range r).foldl
              (fun acc j => Hex.bhksInsertSignatureClass (sig j) j acc) [])
            = Hex.bhksInsertSignatureClass (sig r) r
              ((List.range r).foldl
                (fun acc j => Hex.bhksInsertSignatureClass (sig j) j acc) [])
          from rfl]
      rw [ih]
      exact (partitionAcc_succ r sig).symm

/-- **Partition semantics of `Hex.bhksInsertSignatureClass`.**

The classes emitted by folding `Hex.bhksInsertSignatureClass` over
`List.range r` form the canonical min-column partition of `{0, …, r-1}`
by signature equality. -/
theorem bhksInsertSignatureClass_fold_eq_partitionByMinColumn
    (r : Nat) (sig : Nat → Array Rat) :
    ((List.range r).foldl
      (fun acc j => Hex.bhksInsertSignatureClass (sig j) j acc) []).map Prod.snd =
      partitionByMinColumn r sig := by
  rw [foldl_bhksInsertSignatureClass_eq_partitionAcc, partitionAcc_map_snd]

end BHKS

end HexBerlekampZassenhausMathlib
