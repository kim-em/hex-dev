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

end BHKS

end HexBerlekampZassenhausMathlib
