import HexBerlekampZassenhaus

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

The B7 indicator bridge consumes this fact to match the executable
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

end BHKS

end HexBerlekampZassenhausMathlib
