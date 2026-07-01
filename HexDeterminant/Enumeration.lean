/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import Init.Grind.Ring.Field
public import HexMatrix.Vector.Insert

public section

/-!
Permutation enumeration and inversion-parity arithmetic for the local
Leibniz determinant.

This module defines `permutationVectors`, the recursive enumeration of the
permutations of `Fin n` as length-`n` vectors, together with `inversionCount`,
which counts the inversions of a permutation written as a list. The bulk of the
file establishes how inversion count behaves under list concatenation and under
swaps: `inversionCount_append` splits a concatenation into the inversions of
each part plus the cross-inversions (`crossInversionCount`), and
`inversionCount_adjacent_swap_parity` / `inversionCount_swap_separated_parity`
show that swapping two distinct entries flips inversion parity. These parity
facts underpin the sign computations used by the determinant.

It also proves that the enumeration is a faithful listing of the symmetric
group: `permutationVectors_complete` (every duplicate-free length-`n` vector is
enumerated) and `permutationVectors_nodup` / `permutationVectors_nodup_list` (no
repeats), via the `raiseFinAbove` / `peelLastVector` last-position recursion and
a handful of determinant-agnostic list and `Fin` helpers reused downstream.
-/

namespace Hex
universe u
namespace Matrix
variable {α : Type u}

/-- Enumerate the permutations of `Fin n` as length-`n` vectors. -/
@[expose]
def permutationVectors : (n : Nat) → List (Vector (Fin n) n)
  | 0 => [#v[]]
  | n + 1 =>
      List.flatMap
        (fun v =>
          (List.finRange (n + 1)).map fun i =>
            insertAt (Fin.last n) (v.map Fin.castSucc) i)
        (permutationVectors n)

/-- Count inversions in a permutation written as a list. -/
@[expose]
def inversionCount : List (Fin n) → Nat
  | [] => 0
  | x :: xs =>
      xs.foldl (fun acc y => acc + if y < x then 1 else 0) 0 + inversionCount xs

/-- Count the cross-inversions between two lists: pairs `(x, y)` with `x` drawn
from the first list, `y` from the second, and `y < x`. -/
private def crossInversionCount {n : Nat} : List (Fin n) → List (Fin n) → Nat
  | [], _ => 0
  | x :: xs, ys =>
      ys.foldl (fun acc y => acc + if y < x then 1 else 0) 0 +
        crossInversionCount xs ys

/-- A predicate-counting left fold splits its starting accumulator off
additively. -/
private theorem foldCount_start {α : Type u} (xs : List α) (p : α → Prop)
    [DecidablePred p] (acc : Nat) :
    xs.foldl (fun acc y => acc + if p y then 1 else 0) acc =
      acc + xs.foldl (fun acc y => acc + if p y then 1 else 0) 0 := by
  induction xs generalizing acc with
  | nil => simp
  | cons y ys ih =>
      simp only [List.foldl_cons]
      rw [ih (acc + if p y then 1 else 0), ih (0 + if p y then 1 else 0)]
      omega

/-- The inversion-counting left fold splits its starting accumulator off
additively. -/
private theorem inversionFold_start {n : Nat} (xs : List (Fin n)) (x : Fin n)
    (acc : Nat) :
    xs.foldl (fun acc y => acc + if y < x then 1 else 0) acc =
      acc + xs.foldl (fun acc y => acc + if y < x then 1 else 0) 0 := by
  induction xs generalizing acc with
  | nil => simp
  | cons y ys ih =>
      simp only [List.foldl_cons]
      rw [ih (acc + if y < x then 1 else 0), ih (0 + if y < x then 1 else 0)]
      omega

/-- The inversion-counting fold over an appended list is the sum of the folds
over each part. -/
private theorem inversionFold_append {n : Nat} (xs ys : List (Fin n)) (x : Fin n) :
    (xs ++ ys).foldl (fun acc y => acc + if y < x then 1 else 0) 0 =
      xs.foldl (fun acc y => acc + if y < x then 1 else 0) 0 +
        ys.foldl (fun acc y => acc + if y < x then 1 else 0) 0 := by
  rw [List.foldl_append, inversionFold_start]

/-- Inversions of a concatenation split into the inversions within each part
plus the cross-inversions between them. -/
private theorem inversionCount_append {n : Nat} (xs ys : List (Fin n)) :
    inversionCount (xs ++ ys) =
      inversionCount xs + inversionCount ys + crossInversionCount xs ys := by
  induction xs with
  | nil =>
      change inversionCount ys =
        inversionCount ([] : List (Fin n)) + inversionCount ys +
          crossInversionCount ([] : List (Fin n)) ys
      simp [inversionCount, crossInversionCount]
  | cons x xs ih =>
      simp only [List.cons_append, inversionCount, crossInversionCount]
      rw [inversionFold_append, ih]
      omega

/-- Cross-inversion count is additive in its right argument under
concatenation. -/
private theorem crossInversionCount_append_right {n : Nat}
    (xs ys zs : List (Fin n)) :
    crossInversionCount xs (ys ++ zs) =
      crossInversionCount xs ys + crossInversionCount xs zs := by
  induction xs with
  | nil =>
      simp [crossInversionCount]
  | cons x xs ih =>
      simp only [crossInversionCount]
      rw [inversionFold_append, ih]
      omega

/-- Cross-inversions into a singleton right list count the left-list entries
above that element. -/
private theorem crossInversionCount_singleton_right {n : Nat}
    (xs : List (Fin n)) (y : Fin n) :
    crossInversionCount xs [y] =
      xs.foldl (fun acc x => acc + if y < x then 1 else 0) 0 := by
  induction xs with
  | nil =>
      simp [crossInversionCount]
  | cons x xs ih =>
      simp only [crossInversionCount, List.foldl_cons, List.foldl_nil]
      rw [ih]
      exact (foldCount_start xs (fun x => y < x) (0 + if y < x then 1 else 0)).symm

/-- Swapping the two elements of a right-hand pair leaves the cross-inversion
count unchanged. -/
private theorem crossInversionCount_pair_swap_right {n : Nat}
    (xs : List (Fin n)) (a b : Fin n) :
    crossInversionCount xs [a, b] =
      crossInversionCount xs [b, a] := by
  induction xs with
  | nil =>
      simp [crossInversionCount]
  | cons x xs ih =>
      simp [crossInversionCount]
      rw [ih]
      omega

/-- Swapping the two elements of a left-hand pair leaves the cross-inversion
count unchanged. -/
private theorem crossInversionCount_pair_swap_left {n : Nat}
    (xs : List (Fin n)) (a b : Fin n) :
    crossInversionCount [a, b] xs =
      crossInversionCount [b, a] xs := by
  simp [crossInversionCount]
  omega

/-- A two-element list has exactly one inversion precisely when its entries are
out of order. -/
private theorem inversionCount_pair {n : Nat} (a b : Fin n) :
    inversionCount [a, b] = if b < a then 1 else 0 := by
  simp [inversionCount]

/-- Swapping two distinct adjacent entries flips the parity of the inversion
count. -/
private theorem inversionCount_adjacent_swap_parity {n : Nat}
    (pre post : List (Fin n)) (a b : Fin n) (h : a ≠ b) :
    inversionCount (pre ++ a :: b :: post) % 2 =
      (inversionCount (pre ++ b :: a :: post) + 1) % 2 := by
  have horder : a < b ∨ b < a := by
    have hval : a.val ≠ b.val := by
      intro hv
      exact h (Fin.ext hv)
    cases Nat.lt_or_gt_of_ne hval with
    | inl hab => exact Or.inl hab
    | inr hba => exact Or.inr hba
  rw [show pre ++ a :: b :: post = pre ++ ([a, b] ++ post) by simp,
    show pre ++ b :: a :: post = pre ++ ([b, a] ++ post) by simp]
  have hcross :
      crossInversionCount pre ([a, b] ++ post) =
        crossInversionCount pre ([b, a] ++ post) := by
    repeat rw [crossInversionCount_append_right]
    rw [crossInversionCount_pair_swap_right]
  have htail :
      crossInversionCount [a, b] post =
        crossInversionCount [b, a] post := by
    exact crossInversionCount_pair_swap_left post a b
  rw [inversionCount_append pre ([a, b] ++ post), inversionCount_append pre ([b, a] ++ post),
    hcross, inversionCount_append [a, b] post, inversionCount_append [b, a] post, htail,
    inversionCount_pair a b, inversionCount_pair b a]
  cases horder with
  | inl hab =>
      have hba : ¬ b < a := by omega
      simp [hab, hba]
      omega
  | inr hba =>
      have hab : ¬ a < b := by omega
      simp [hab, hba]
      omega

/-- Swapping two entries separated by an arbitrary duplicate-free middle segment
flips the parity of the inversion count. -/
private theorem inversionCount_swap_separated_parity {n : Nat}
    (pre mid post : List (Fin n)) (a b : Fin n)
    (hnodup : (pre ++ a :: mid ++ b :: post).Nodup) :
    inversionCount (pre ++ b :: mid ++ a :: post) % 2 =
      (inversionCount (pre ++ a :: mid ++ b :: post) + 1) % 2 := by
  induction mid generalizing pre with
  | nil =>
      have hne : b ≠ a := by
        intro hba
        subst b
        have hsplit : ((pre ++ [a]) ++ a :: post).Nodup := by
          simpa [List.append_assoc] using hnodup
        exact ((List.nodup_append (l₁ := pre ++ [a]) (l₂ := a :: post)).mp hsplit).2.2
          a (by simp) a (by simp) rfl
      simpa [Nat.add_comm] using
        (inversionCount_adjacent_swap_parity pre post b a hne)
  | cons x xs ih =>
      have hswap₁ :
          inversionCount (pre ++ b :: x :: xs ++ a :: post) % 2 =
            (inversionCount (pre ++ x :: b :: xs ++ a :: post) + 1) % 2 := by
        simpa [List.append_assoc] using
          inversionCount_adjacent_swap_parity pre (xs ++ a :: post) b x (by
            intro hbx
            subst b
            have hsplit : ((pre ++ a :: x :: xs) ++ x :: post).Nodup := by
              simpa [List.append_assoc] using hnodup
            exact ((List.nodup_append (l₁ := pre ++ a :: x :: xs) (l₂ := x :: post)).mp hsplit).2.2
              x (by simp) x (by simp) rfl)
      have hnodup_tail : ((pre ++ [x]) ++ a :: xs ++ b :: post).Nodup := by
        have hp :
            ((pre ++ [x]) ++ a :: xs ++ b :: post).Perm
              (pre ++ a :: x :: xs ++ b :: post) := by
          simpa [List.append_assoc] using
            List.Perm.append_left pre (List.Perm.swap a x (xs ++ b :: post))
        exact hp.nodup_iff.mpr hnodup
      have hmid :
          inversionCount (pre ++ x :: b :: xs ++ a :: post) % 2 =
            (inversionCount (pre ++ x :: a :: xs ++ b :: post) + 1) % 2 := by
        simpa only [List.cons_append, List.append_assoc, List.nil_append] using
          (ih (pre ++ [x]) hnodup_tail)
      have hswap₂ :
          inversionCount (pre ++ x :: a :: xs ++ b :: post) % 2 =
            (inversionCount (pre ++ a :: x :: xs ++ b :: post) + 1) % 2 := by
        simpa [List.append_assoc] using
          inversionCount_adjacent_swap_parity pre (xs ++ b :: post) x a (by
            intro hxa
            subst x
            have hsplit : (pre ++ [a] ++ (a :: xs ++ b :: post)).Nodup := by
              simpa [List.append_assoc] using hnodup
            exact ((List.nodup_append (l₁ := pre ++ [a]) (l₂ := a :: xs ++ b :: post)).mp hsplit).2.2
              a (by simp) a (by simp) rfl)
      omega



/-! ### Generic list and `Fin` combinatorics

These determinant-agnostic helpers about folds, `Nodup`, and `insertAt`
support the enumeration completeness and duplicate-freeness proofs below,
and are reused by the Leibniz determinant layer downstream. -/

/-- Mapping a duplicate-free list by an injective function preserves
duplicate-freeness. -/
private theorem list_nodup_map_of_injective {α : Type u} {β : Type v}
    [DecidableEq β] {f : α → β} (hinj : Function.Injective f) :
    ∀ {xs : List α}, xs.Nodup → (xs.map f).Nodup
  | [], _ => by simp
  | x :: xs, hnodup => by
      simp only [List.map_cons, List.nodup_cons] at hnodup ⊢
      constructor
      · intro hmem
        simp only [List.mem_map] at hmem
        rcases hmem with ⟨y, hy, hfy⟩
        exact hnodup.1 (hinj hfy.symm ▸ hy)
      · exact list_nodup_map_of_injective hinj hnodup.2

/-- For `i ≤ r < xs.length`, element `r + 1` of `xs.insertIdx i x` is the original
`xs[r]`, since the insertion shifts later entries up by one. -/
private theorem list_getElem_insertIdx_succ {α : Type u}
    (xs : List α) (x : α) {i r : Nat} (h : i ≤ r) (hr : r < xs.length) :
    (xs.insertIdx i x)[r + 1]'(by
      have hi : i ≤ xs.length := Nat.le_trans h (Nat.le_of_lt hr)
      rw [List.length_insertIdx_of_le_length hi]
      omega) = xs[r] := by
  induction xs generalizing i r with
  | nil =>
      cases hr
  | cons y ys ih =>
      cases i with
      | zero =>
          cases r with
          | zero =>
              simp
          | succ r =>
              simp
      | succ i =>
          cases r with
          | zero =>
              omega
          | succ r =>
              simp only [List.insertIdx, List.getElem_cons_succ]
              exact ih (Nat.succ_le_succ_iff.mp h) (Nat.succ_lt_succ_iff.mp hr)

/-- Mapping a `Nodup` list through the injective `Fin.castSucc` keeps it `Nodup`. -/
private theorem list_nodup_map_castSucc {n : Nat} (xs : List (Fin n)) :
    xs.Nodup → (xs.map Fin.castSucc).Nodup := by
  induction xs with
  | nil =>
      intro _h
      simp
  | cons x xs ih =>
      intro hnodup
      rw [List.nodup_cons] at hnodup
      rw [List.map_cons, List.nodup_cons]
      constructor
      · intro hmem
        rw [List.mem_map] at hmem
        rcases hmem with ⟨y, hy, hxy⟩
        have hval : x.val = y.val := by
          simpa using (congrArg Fin.val hxy).symm
        exact hnodup.1 (Fin.ext hval ▸ hy)
      · exact ih hnodup.2

/-- `Fin.last n` never lies in the image of a list under `Fin.castSucc`. -/
private theorem finLast_not_mem_map_castSucc {n : Nat} (xs : List (Fin n)) :
    Fin.last n ∉ xs.map Fin.castSucc := by
  intro hmem
  rw [List.mem_map] at hmem
  rcases hmem with ⟨x, _hxmem, hxlast⟩
  have hval : x.val = n := by
    simpa using congrArg Fin.val hxlast
  exact Nat.ne_of_lt x.isLt hval

/-- Inserting `Fin.last n` at any position into the `castSucc`-embedded nodup vector
keeps the resulting list `Nodup`, since `Fin.last n` is new and the embedding
stays injective. -/
private theorem insertAt_last_castSucc_nodup {n : Nat}
    (v : Vector (Fin n) n) (i : Fin (n + 1))
    (hnodup : v.toList.Nodup) :
    (insertAt (Fin.last n) (v.map Fin.castSucc) i).toList.Nodup := by
  rw [insertAt_toList]
  have hmap : (v.map Fin.castSucc).toList.Nodup := by
    rw [vector_toList_map]
    exact list_nodup_map_castSucc v.toList hnodup
  have hlast : Fin.last n ∉ (v.map Fin.castSucc).toList := by
    rw [vector_toList_map]
    exact finLast_not_mem_map_castSucc v.toList
  have hcons : (Fin.last n :: (v.map Fin.castSucc).toList).Nodup := by
    rw [List.nodup_cons]
    exact ⟨hlast, hmap⟩
  have hidx : i.val ≤ (v.map Fin.castSucc).toList.length := by
    simpa using Nat.lt_succ_iff.mp i.isLt
  exact (List.perm_insertIdx (Fin.last n) (v.map Fin.castSucc).toList hidx).symm.nodup hcons

/-- A `Nodup` list of `Fin (n + 1)` with full length `n + 1` must contain
`Fin.last n`. -/
private theorem finLast_mem {n : Nat} {xs : List (Fin (n + 1))}
    (hlen : xs.length = n + 1) (hnodup : xs.Nodup) :
    Fin.last n ∈ xs := by
  by_cases hmem : Fin.last n ∈ xs
  · exact hmem
  · exfalso
    have hsubset : xs ⊆ (List.finRange (n + 1)).erase (Fin.last n) := by
      intro x hx
      refine (List.mem_erase_of_ne ?_).2 (List.mem_finRange x)
      rintro rfl
      exact hmem hx
    have hle : xs.length ≤ ((List.finRange (n + 1)).erase (Fin.last n)).length :=
      List.nodup_subset_length_le hnodup hsubset
    have herase :
        ((List.finRange (n + 1)).erase (Fin.last n)).length = n := by
      rw [List.length_erase]
      simp [List.mem_finRange, List.length_finRange]
    omega


/-! ### Completeness and duplicate-freeness of the enumeration -/

/-- `lowerFinLast x h` reinterprets an `x : Fin (n + 1)` that is not `Fin.last n`
as an element of `Fin n` carrying the same underlying value. -/
private def lowerFinLast {n : Nat} (x : Fin (n + 1)) (h : x ≠ Fin.last n) :
    Fin n :=
  ⟨x.val, by
    have hxlt : x.val < n + 1 := x.isLt
    have hxne : x.val ≠ n := by
      intro hx
      exact h (Fin.ext hx)
    omega⟩

/-- `raiseFinAbove i r` embeds `r : Fin n` into `Fin (n + 1)` while skipping the
position `i`: values below `i` are kept, values at or above `i` are shifted up by
one. -/
private def raiseFinAbove {n : Nat} (i : Fin (n + 1)) (r : Fin n) :
    Fin (n + 1) :=
  if h : r.val < i.val then
    ⟨r.val, by omega⟩
  else
    ⟨r.val + 1, by omega⟩

/-- Indexing `insertAt x v i` at the raised position `raiseFinAbove i r` recovers
the original entry `v[r]`. -/
private theorem insertAt_get_raiseFinAbove {α : Type u} {n : Nat}
    (x : α) (v : Vector α n) (i : Fin (n + 1)) (r : Fin n) :
    (insertAt x v i)[raiseFinAbove i r] = v[r] := by
  unfold insertAt raiseFinAbove
  split
  · simpa [Vector.getElem_toList] using
      List.getElem_insertIdx_of_lt (l := v.toList) (x := x) (i := i.val)
        (j := r.val) ‹r.val < i.val› (by
          have hi : i.val ≤ v.toList.length := by
            simpa [Vector.length_toList] using Nat.lt_succ_iff.mp i.isLt
          rw [List.length_insertIdx_of_le_length hi]
          simpa [Vector.length_toList] using Nat.lt_succ_of_lt r.isLt)
  · simpa using
      list_getElem_insertIdx_succ v.toList x (Nat.le_of_not_gt ‹¬r.val < i.val›)
        (by simp [Vector.length_toList])

/-- `raiseFinAbove i` is strictly monotone: `raiseFinAbove i a < raiseFinAbove i b`
holds exactly when `a < b`. -/
private theorem raiseFinAbove_lt_iff {n : Nat} (i : Fin (n + 1)) (a b : Fin n) :
    raiseFinAbove i a < raiseFinAbove i b ↔ a < b := by
  by_cases hai : a.val < i.val
  · by_cases hbi : b.val < i.val
    · simp [raiseFinAbove, hai, hbi, Fin.lt_def]
    · simp [raiseFinAbove, hai, hbi, Fin.lt_def]
      omega
  · by_cases hbi : b.val < i.val
    · simp [raiseFinAbove, hai, hbi, Fin.lt_def]
      omega
    · simp [raiseFinAbove, hai, hbi, Fin.lt_def]

/-- The inversion fold against a pivot `x` is unchanged when both the list `xs` and
the pivot are mapped through `raiseFinAbove i`. -/
private theorem inversionFold_map_raiseFinAbove {n : Nat} (i : Fin (n + 1))
    (xs : List (Fin n)) (x : Fin n) (acc : Nat) :
    (xs.map (raiseFinAbove i)).foldl
        (fun acc y => acc + if y < raiseFinAbove i x then 1 else 0) acc =
    xs.foldl (fun acc y => acc + if y < x then 1 else 0) acc := by
  induction xs generalizing acc with
  | nil => rfl
  | cons y ys ih =>
      simp only [List.map_cons, List.foldl_cons]
      have hhead :
          (if raiseFinAbove i y < raiseFinAbove i x then 1 else 0) =
            (if y < x then 1 else 0) := by
        by_cases hyx : y < x
        · have hraise : raiseFinAbove i y < raiseFinAbove i x :=
            (raiseFinAbove_lt_iff i y x).2 hyx
          simp [hyx, hraise]
        · have hraise : ¬ raiseFinAbove i y < raiseFinAbove i x := by
            intro h
            exact hyx ((raiseFinAbove_lt_iff i y x).1 h)
          simp [hyx, hraise]
      rw [hhead]
      exact ih _

/-- `inversionCount` is invariant under mapping the permutation list through
`raiseFinAbove i`. -/
private theorem inversionCount_map_raiseFinAbove {n : Nat}
    (i : Fin (n + 1)) (xs : List (Fin n)) :
    inversionCount (xs.map (raiseFinAbove i)) = inversionCount xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
      simp [inversionCount, ih, inversionFold_map_raiseFinAbove]

/-- Folding `i < y` over the `raiseFinAbove i`-mapped list counts the original
entries `x` satisfying `i ≤ x`, added onto the starting accumulator. -/
private theorem inversionFold_map_raiseFinAbove_self {n : Nat} (i : Fin (n + 1))
    (xs : List (Fin n)) (acc : Nat) :
    (xs.map (raiseFinAbove i)).foldl
        (fun acc y => acc + if i < y then 1 else 0) acc =
    acc + xs.foldl (fun acc y => acc + if i.val ≤ y.val then 1 else 0) 0 := by
  induction xs generalizing acc with
  | nil =>
      simp
  | cons x xs ih =>
      simp only [List.map_cons, List.foldl_cons]
      have hhead :
          (if i < raiseFinAbove i x then 1 else 0) =
            (if i.val ≤ x.val then 1 else 0) := by
        by_cases hxi : x.val < i.val
        · have hnle : ¬ i.val ≤ x.val := by omega
          have hnlt : ¬ i < raiseFinAbove i x := by
            simp [raiseFinAbove, hxi, Fin.lt_def]
            omega
          simp [hnle, hnlt]
        · have hle : i.val ≤ x.val := Nat.le_of_not_gt hxi
          have hlt : i < raiseFinAbove i x := by
            change i.val < (raiseFinAbove i x).val
            simp [raiseFinAbove, hxi]
            omega
          simp [hle, hlt]
      rw [hhead, ih (acc + if i.val ≤ x.val then 1 else 0)]
      rw [foldCount_start xs (fun y : Fin n => i.val ≤ y.val)
        (0 + if i.val ≤ x.val then 1 else 0)]
      omega

/-- Appending `i` after the `raiseFinAbove i`-mapped list yields `inversionCount xs`
plus the number of entries at or above `i`. -/
private theorem inversionCount_map_raiseFinAbove_append_self {n : Nat}
    (i : Fin (n + 1)) (xs : List (Fin n)) :
    inversionCount ((xs.map (raiseFinAbove i)) ++ [i]) =
      inversionCount xs +
        xs.foldl (fun acc y => acc + if i.val ≤ y.val then 1 else 0) 0 := by
  rw [inversionCount_append, inversionCount_map_raiseFinAbove]
  have hsingle : inversionCount ([i] : List (Fin (n + 1))) = 0 := by
    simp [inversionCount]
  rw [hsingle, crossInversionCount_singleton_right, inversionFold_map_raiseFinAbove_self i xs 0]
  omega

/-- The `i ≤ y` count fold is unchanged when the list is mapped through
`Fin.castSucc`. -/
private theorem foldCount_map_castSucc_ge {n : Nat} (i : Fin (n + 1))
    (xs : List (Fin n)) (acc : Nat) :
    (xs.map Fin.castSucc).foldl
        (fun acc y => acc + if i.val ≤ y.val then 1 else 0) acc =
      xs.foldl (fun acc y => acc + if i.val ≤ y.val then 1 else 0) acc := by
  induction xs generalizing acc with
  | nil => rfl
  | cons x xs ih =>
      simp only [List.map_cons, List.foldl_cons]
      exact ih _

/-- Folding a step that discards each element and returns the accumulator leaves
the accumulator unchanged. -/
private theorem foldl_ignore {α : Type u} (xs : List α) (acc : Nat) :
    xs.foldl (fun acc _x => acc) acc = acc := by
  induction xs generalizing acc with
  | nil => rfl
  | cons _ xs ih =>
      simp only [List.foldl_cons]
      exact ih acc

/-- Counting the entries `y` of `List.finRange n` with `i ≤ y` gives `n - i`. -/
private theorem foldCount_finRange_ge {n : Nat} (i : Fin (n + 1)) :
    (List.finRange n).foldl
        (fun acc y => acc + if i.val ≤ y.val then 1 else 0) 0 =
      n - i.val := by
  induction n with
  | zero =>
      simp
  | succ n ih =>
      by_cases htop : i.val = n + 1
      · have hfalse :
            ∀ acc y, y ∈ List.finRange (n + 1) →
              (fun (acc : Nat) (y : Fin (n + 1)) =>
                acc + if i.val ≤ y.val then 1 else 0) acc y =
                (fun (acc : Nat) (_y : Fin (n + 1)) => acc) acc y := by
          intro acc y _hy
          have hnle : ¬ i.val ≤ y.val := by omega
          simp [hnle]
        calc
          (List.finRange (n + 1)).foldl
              (fun acc y => acc + if i.val ≤ y.val then 1 else 0) 0 =
              (List.finRange (n + 1)).foldl
                (fun (acc : Nat) (_y : Fin (n + 1)) => acc) 0 := by
                exact List.foldl_congr (List.finRange (n + 1))
                  (fun (acc : Nat) (y : Fin (n + 1)) =>
                    acc + if i.val ≤ y.val then 1 else 0)
                  (fun (acc : Nat) (_y : Fin (n + 1)) => acc) 0 hfalse
          _ = 0 := foldl_ignore (List.finRange (n + 1)) 0
          _ = n + 1 - i.val := by omega
      · have hiLt : i.val < n + 1 := by omega
        let i' : Fin (n + 1) := ⟨i.val, hiLt⟩
        rw [List.finRange_succ_last, List.foldl_append, List.foldl_cons, List.foldl_nil,
          foldCount_map_castSucc_ge i' (List.finRange n) 0, ih i']
        have hleLast : i.val ≤ n := by omega
        simp [i', hleLast]
        omega

/-- The `foldl` count of elements satisfying `p` is invariant under permutation of
the list. -/
private theorem foldCount_perm {α : Type u} (p : α → Prop) [DecidablePred p]
    {xs ys : List α} (hperm : xs.Perm ys) :
    xs.foldl (fun acc y => acc + if p y then 1 else 0) 0 =
      ys.foldl (fun acc y => acc + if p y then 1 else 0) 0 := by
  induction hperm with
  | nil => rfl
  | cons x hperm ih =>
      rename_i l₁ l₂
      simp only [List.foldl_cons]
      let a := 0 + if p x then 1 else 0
      calc
        l₁.foldl (fun acc y => acc + if p y then 1 else 0) a =
            a + l₁.foldl (fun acc y => acc + if p y then 1 else 0) 0 := by
              exact foldCount_start l₁ p a
        _ = a + l₂.foldl (fun acc y => acc + if p y then 1 else 0) 0 := by
              rw [ih]
        _ = l₂.foldl (fun acc y => acc + if p y then 1 else 0) a := by
              exact (foldCount_start l₂ p a).symm
  | swap x y xs =>
      simp only [List.foldl_cons]
      rw [foldCount_start xs p ((0 + if p y then 1 else 0) + if p x then 1 else 0),
        foldCount_start xs p ((0 + if p x then 1 else 0) + if p y then 1 else 0)]
      omega
  | trans _ _ ih₁ ih₂ =>
      exact ih₁.trans ih₂

/-- Every `x : Fin n` is a member of a nodup list of `Fin n` whose length is `n`. -/
private theorem mem_of_full_nodup {n : Nat} {xs : List (Fin n)}
    (x : Fin n) (hlen : xs.length = n) (hnodup : xs.Nodup) :
    x ∈ xs := by
  by_cases hmem : x ∈ xs
  · exact hmem
  · exfalso
    have hsubset : xs ⊆ (List.finRange n).erase x := by
      intro y hy
      refine (List.mem_erase_of_ne ?_).2 (List.mem_finRange y)
      rintro rfl
      exact hmem hy
    have hle : xs.length ≤ ((List.finRange n).erase x).length :=
      List.nodup_subset_length_le hnodup hsubset
    have herase : ((List.finRange n).erase x).length = n - 1 := by
      rw [List.length_erase]
      simp [List.mem_finRange, List.length_finRange]
    rw [hlen, herase] at hle
    cases n with
    | zero => exact Fin.elim0 x
    | succ n => omega

/-- A nodup list of `Fin n` of length `n` is a permutation of `List.finRange n`. -/
private theorem list_perm_finRange {n : Nat} {xs : List (Fin n)}
    (hlen : xs.length = n) (hnodup : xs.Nodup) :
    xs.Perm (List.finRange n) := by
  rw [List.perm_ext_iff_of_nodup hnodup (List.nodup_finRange n)]
  intro x
  constructor
  · intro _hx
    exact List.mem_finRange x
  · intro _hx
    exact mem_of_full_nodup x hlen hnodup

/-- Counting the entries `y` with `i ≤ y` in a length-`n` nodup list of `Fin n`
gives `n - i`. -/
private theorem foldCount_full_nodup_ge {n : Nat} (i : Fin (n + 1))
    {xs : List (Fin n)} (hlen : xs.length = n) (hnodup : xs.Nodup) :
    xs.foldl (fun acc y => acc + if i.val ≤ y.val then 1 else 0) 0 =
      n - i.val := by
  rw [foldCount_perm (fun y : Fin n => i.val ≤ y.val)
    (list_perm_finRange hlen hnodup)]
  exact foldCount_finRange_ge i

/-- `Fin.castSucc` undoes `lowerFinLast`: `(lowerFinLast x h).castSucc = x`. -/
private theorem lowerFinLast_castSucc {n : Nat} (x : Fin (n + 1))
    (h : x ≠ Fin.last n) :
    (lowerFinLast x h).castSucc = x := by
  exact Fin.ext rfl

/-- In a length-`(n + 1)` nodup list the index of `Fin.last n` is within bounds. -/
private theorem finLast_idxOf_lt {n : Nat} {xs : List (Fin (n + 1))}
    (hlen : xs.length = n + 1) (hnodup : xs.Nodup) :
    xs.idxOf (Fin.last n) < xs.length := by
  exact List.idxOf_lt_length_of_mem (finLast_mem hlen hnodup)

/-- `peelLastVector perm k …` removes the entry `Fin.last n` (located at position
`k`) from a nodup permutation vector, lowering each remaining entry back to
`Fin n`. -/
private def peelLastVector {n : Nat} (perm : Vector (Fin (n + 1)) (n + 1))
    (k : Nat) (_hk : k < n + 1)
    (hidx : perm.toList.idxOf (Fin.last n) = k)
    (hnodup : perm.toList.Nodup) : Vector (Fin n) n :=
  Vector.ofFn fun r =>
    let j := if r.val < k then r.val else r.val + 1
    have hj : j < n + 1 := by
      dsimp [j]
      split
      · omega
      · have hr : r.val < n := r.isLt
        omega
    let y := perm[(⟨j, hj⟩ : Fin (n + 1))]
    lowerFinLast y (by
      intro hy
      have hjlen : j < perm.toList.length := by
        simpa [Vector.length_toList] using hj
      have hjidx :
          perm.toList.idxOf (perm.toList[j]'hjlen) = j := by
        exact hnodup.idxOf_getElem j hjlen
      have hylist : perm.toList[j]'hjlen = Fin.last n := by
        rw [Vector.getElem_toList]; exact hy
      have hkj : k = j := by
        rw [← hidx, ← hylist, hjidx]
      dsimp [j] at hkj
      split at hkj
      · omega
      · omega)

/-- Re-embedding `peelLastVector` through `Fin.castSucc` yields the original
permutation list with position `k` erased. -/
private theorem peelLastVector_castSucc_toList {n : Nat}
    (perm : Vector (Fin (n + 1)) (n + 1))
    (k : Nat) (hk : k < n + 1)
    (hidx : perm.toList.idxOf (Fin.last n) = k)
    (hnodup : perm.toList.Nodup) :
    ((peelLastVector perm k hk hidx hnodup).map Fin.castSucc).toList =
      perm.toList.eraseIdx k := by
  apply List.ext_getElem
  · have hklist : k < perm.toList.length := by
      simpa [Vector.length_toList] using hk
    rw [List.length_eraseIdx_of_lt hklist]
    simp [Vector.length_toList]
  · intro i hi₁ hi₂
    by_cases hik : i < k
    · simp [peelLastVector, hik, lowerFinLast_castSucc, List.getElem_eraseIdx]
    · have hikle : k ≤ i := Nat.le_of_not_gt hik
      have hklist : k < perm.toList.length := by
        simpa [Vector.length_toList] using hk
      have heraseLen : (perm.toList.eraseIdx k).length = n := by
        rw [List.length_eraseIdx_of_lt hklist]
        simp [Vector.length_toList]
      have hi : i < n := by
        simpa [heraseLen] using hi₂
      simp [peelLastVector, hik, lowerFinLast_castSucc, List.getElem_eraseIdx]

/-- If `xs.map f` is nodup and `f` is injective, then `xs` is nodup. -/
private theorem list_nodup_of_map_injective {α β : Type u} {f : α → β}
    (hinj : Function.Injective f) :
    ∀ {xs : List α}, (xs.map f).Nodup → xs.Nodup
  | [], _ => by simp
  | x :: xs, hnodup => by
      simp only [List.map_cons, List.nodup_cons] at hnodup ⊢
      constructor
      · intro hxmem
        exact hnodup.1 (List.mem_map.mpr ⟨x, hxmem, rfl⟩)
      · exact list_nodup_of_map_injective hinj hnodup.2

/-- `peelLastVector` produces a nodup vector. -/
private theorem peelLastVector_nodup {n : Nat}
    (perm : Vector (Fin (n + 1)) (n + 1))
    (k : Nat) (hk : k < n + 1)
    (hidx : perm.toList.idxOf (Fin.last n) = k)
    (hnodup : perm.toList.Nodup) :
    (peelLastVector perm k hk hidx hnodup).toList.Nodup := by
  apply list_nodup_of_map_injective (f := Fin.castSucc)
  · intro x y hxy
    exact Fin.ext (by simpa using congrArg Fin.val hxy)
  · rw [← vector_toList_map]
    rw [peelLastVector_castSucc_toList perm k hk hidx hnodup]
    exact hnodup.eraseIdx k

/-- Inserting the erased element `xs[i]` back at position `i` of `xs.eraseIdx i`
reconstructs the original list `xs`. -/
private theorem list_insertIdx_eraseIdx_getElem {α : Type u} {xs : List α} {i : Nat}
    (hi : i < xs.length) :
    (xs.eraseIdx i).insertIdx i (xs[i]'hi) = xs := by
  induction xs generalizing i with
  | nil =>
      cases hi
  | cons x xs ih =>
      cases i with
      | zero =>
          simp
      | succ i =>
          simp only [List.length_cons, Nat.succ_lt_succ_iff] at hi
          simp [ih hi]

/-- Inserting `Fin.last n` at position `k` into the `castSucc`-embedded
`peelLastVector` reconstructs the original permutation vector `perm`. -/
private theorem insertAt_peelLastVector {n : Nat}
    (perm : Vector (Fin (n + 1)) (n + 1))
    (k : Nat) (hk : k < n + 1)
    (hidx : perm.toList.idxOf (Fin.last n) = k)
    (hnodup : perm.toList.Nodup) :
    insertAt (Fin.last n)
        ((peelLastVector perm k hk hidx hnodup).map Fin.castSucc) ⟨k, hk⟩ =
      perm := by
  apply Vector.toArray_inj.mp
  apply Array.toList_inj.mp
  change (insertAt (Fin.last n)
        ((peelLastVector perm k hk hidx hnodup).map Fin.castSucc) ⟨k, hk⟩).toList =
      perm.toList
  rw [insertAt_toList, peelLastVector_castSucc_toList perm k hk hidx hnodup]
  have hklist : k < perm.toList.length := by
    simpa [Vector.length_toList] using hk
  have hget : perm.toList[k]'hklist = Fin.last n := by
    have hidxLt : perm.toList.idxOf (Fin.last n) < perm.toList.length := by
      simpa [hidx] using hklist
    simpa [hidx] using
      (List.getElem_idxOf (x := Fin.last n) (xs := perm.toList) hidxLt)
  simpa [hget] using
    (list_insertIdx_eraseIdx_getElem (xs := perm.toList) (i := k) hklist)

/-- Every duplicate-free length-`n` vector of `Fin n` appears in
`permutationVectors n`. This gives the completeness half of the local
permutation enumeration used by the Leibniz determinant. -/
theorem permutationVectors_complete {n : Nat} {perm : Vector (Fin n) n}
    (hnodup : perm.toList.Nodup) :
    perm ∈ permutationVectors n := by
  induction n with
  | zero =>
      have hnil : perm.toList = [] := by
        apply List.eq_nil_iff_length_eq_zero.mpr
        simp [Vector.length_toList]
      have hperm : perm = #v[] := by
        ext i hi
        omega
      simp [permutationVectors, hperm]
  | succ n ih =>
      let k := perm.toList.idxOf (Fin.last n)
      have hk : k < n + 1 := by
        simpa [k, Vector.length_toList] using
          finLast_idxOf_lt (by simp [Vector.length_toList]) hnodup
      have hidx : perm.toList.idxOf (Fin.last n) = k := rfl
      let peeled := peelLastVector perm k hk hidx hnodup
      have hpeeled : peeled ∈ permutationVectors n := by
        exact ih (peelLastVector_nodup perm k hk hidx hnodup)
      change perm ∈
        List.flatMap
          (fun v =>
            (List.finRange (n + 1)).map fun i =>
              insertAt (Fin.last n) (v.map Fin.castSucc) i)
          (permutationVectors n)
      rw [List.mem_flatMap]
      refine ⟨peeled, hpeeled, ?_⟩
      rw [List.mem_map]
      refine ⟨(⟨k, hk⟩ : Fin (n + 1)), List.mem_finRange (⟨k, hk⟩ : Fin (n + 1)), ?_⟩
      exact insertAt_peelLastVector perm k hk hidx hnodup

/-- Every vector enumerated by `permutationVectors n` is duplicate-free, so
each listed vector really represents a permutation of `Fin n`. -/
theorem permutationVectors_nodup {n : Nat} {perm : Vector (Fin n) n}
    (hmem : perm ∈ permutationVectors n) :
    perm.toList.Nodup := by
  induction n with
  | zero =>
      have hnil : perm.toList = [] := by
        apply List.eq_nil_iff_length_eq_zero.mpr
        simp [Vector.length_toList]
      rw [hnil]
      simp
  | succ n ih =>
      simp [permutationVectors, List.mem_flatMap, List.mem_map] at hmem
      rcases hmem with ⟨v, hv, i, _hi, rfl⟩
      exact insertAt_last_castSucc_nodup v i (ih hv)

private theorem insertAt_last_castSucc_idxOf {n : Nat}
    (v : Vector (Fin n) n) (i : Fin (n + 1)) (hnodup : v.toList.Nodup) :
    (insertAt (Fin.last n) (v.map Fin.castSucc) i).toList.idxOf (Fin.last n) =
      i.val := by
  have hins :
      (insertAt (Fin.last n) (v.map Fin.castSucc) i).toList.Nodup :=
    insertAt_last_castSucc_nodup v i hnodup
  have hlen :
      i.val < (insertAt (Fin.last n) (v.map Fin.castSucc) i).toList.length := by
    simp [Vector.length_toList]
  have hget :
      (insertAt (Fin.last n) (v.map Fin.castSucc) i).toList[i.val] =
        Fin.last n := by
    change (insertAt (Fin.last n) (v.map Fin.castSucc) i)[i] = Fin.last n
    exact insertAt_get_self (Fin.last n) (v.map Fin.castSucc) i
  simpa [hget] using hins.idxOf_getElem i.val hlen

/-- `insertAt_last_castSucc_injective` states that inserting `Fin.last n` into the
`castSucc`-lifted nodup vectors `v` and `w` at positions `i` and `j` yields equal
results only when `i = j` and `v = w`, the injectivity that keeps the inserted
permutation vectors distinct in the recursive enumeration. -/
private theorem insertAt_last_castSucc_injective {n : Nat}
    {v w : Vector (Fin n) n} {i j : Fin (n + 1)}
    (hv : v.toList.Nodup) (hw : w.toList.Nodup)
    (h :
      insertAt (Fin.last n) (v.map Fin.castSucc) i =
        insertAt (Fin.last n) (w.map Fin.castSucc) j) :
    i = j ∧ v = w := by
  have hidx :
      i.val = j.val := by
    rw [← insertAt_last_castSucc_idxOf v i hv, h]
    exact insertAt_last_castSucc_idxOf w j hw
  have hij : i = j := Fin.ext hidx
  subst j
  have hlist := congrArg
    (fun x : Vector (Fin (n + 1)) (n + 1) => x.toList.eraseIdx i.val) h
  change
    (insertAt (Fin.last n) (v.map Fin.castSucc) i).toList.eraseIdx i.val =
      (insertAt (Fin.last n) (w.map Fin.castSucc) i).toList.eraseIdx i.val at hlist
  rw [insertAt_toList, insertAt_toList] at hlist
  repeat rw [List.eraseIdx_insertIdx_self] at hlist
  have hmap : v.toList.map Fin.castSucc = w.toList.map Fin.castSucc := by
    simpa [vector_toList_map] using hlist
  have hvwList : v.toList = w.toList := by
    exact (List.map_inj_right
      (fun x y hxy => Fin.ext (by simpa using congrArg Fin.val hxy))).mp hmap
  refine ⟨rfl, ?_⟩
  apply Vector.toArray_inj.mp
  apply Array.toList_inj.mp
  simpa [Vector.toList] using hvwList

/-- `permutationVectorInsertions_nodup` states that, for a fixed nodup vector `v`,
the list of insertions of `Fin.last n` at each position has no duplicates, so the
size-`n+1` vectors built from a single size-`n` permutation stay distinct. -/
private theorem permutationVectorInsertions_nodup {n : Nat}
    (v : Vector (Fin n) n) (hnodup : v.toList.Nodup) :
    ((List.finRange (n + 1)).map fun i =>
        insertAt (Fin.last n) (v.map Fin.castSucc) i).Nodup := by
  exact list_nodup_map_of_injective
    (fun i j h => (insertAt_last_castSucc_injective hnodup hnodup h).1)
    (List.nodup_finRange (n + 1))

/-- `permutationVectorInsertions_disjoint` states that distinct nodup vectors `v`
and `w` produce insertion lists sharing no element, the cross-vector disjointness
that prevents collisions when the per-vector insertions are concatenated. -/
private theorem permutationVectorInsertions_disjoint {n : Nat}
    {v w : Vector (Fin n) n}
    (hv : v.toList.Nodup) (hw : w.toList.Nodup) (hvw : v ≠ w) :
    ∀ a, a ∈ ((List.finRange (n + 1)).map fun i =>
        insertAt (Fin.last n) (v.map Fin.castSucc) i) →
      ∀ b, b ∈ ((List.finRange (n + 1)).map fun i =>
        insertAt (Fin.last n) (w.map Fin.castSucc) i) →
        a ≠ b := by
  intro a ha b hb hab
  simp only [List.mem_map] at ha hb
  rcases ha with ⟨i, _hi, rfl⟩
  rcases hb with ⟨j, _hj, hb⟩
  exact hvw (insertAt_last_castSucc_injective hv hw (hab.trans hb.symm)).2

/-- `permutationVectors_flatMap_nodup` states that flat-mapping the per-vector
insertion lists over a nodup list `vs` of nodup vectors yields a nodup list,
combining the per-vector and cross-vector facts into the no-duplicates property of
the size-`n+1` permutation enumeration. -/
private theorem permutationVectors_flatMap_nodup {n : Nat}
    (vs : List (Vector (Fin n) n))
    (hvs : vs.Nodup) (hperm : ∀ v, v ∈ vs → v.toList.Nodup) :
    (vs.flatMap fun v =>
        (List.finRange (n + 1)).map fun i =>
          insertAt (Fin.last n) (v.map Fin.castSucc) i).Nodup := by
  induction vs with
  | nil =>
      simp
  | cons v vs ih =>
      simp only [List.flatMap_cons]
      rw [List.nodup_append]
      simp only [List.nodup_cons] at hvs
      refine ⟨?_, ?_, ?_⟩
      · exact permutationVectorInsertions_nodup v (hperm v (by simp))
      · exact ih hvs.2 (fun w hw => hperm w (List.mem_cons_of_mem v hw))
      · intro a ha b hb hab
        simp only [List.mem_flatMap, List.mem_map] at hb
        rcases hb with ⟨w, hw, j, _hj, rfl⟩
        exact permutationVectorInsertions_disjoint
          (hperm v (by simp)) (hperm w (List.mem_cons_of_mem v hw))
          (by
            intro hvw
            exact hvs.1 (hvw ▸ hw))
          a ha _ (List.mem_map.mpr ⟨j, List.mem_finRange j, rfl⟩) hab

/-- The permutation enumeration itself has no duplicate vectors. This lets
determinant proofs compare sums over `permutationVectors` by list
permutation rather than by quotienting repeated terms. -/
theorem permutationVectors_nodup_list {n : Nat} :
    (permutationVectors n).Nodup := by
  induction n with
  | zero =>
      simp [permutationVectors]
  | succ n ih =>
      simp only [permutationVectors]
      exact permutationVectors_flatMap_nodup
        (permutationVectors n) ih
        (fun v hv => permutationVectors_nodup hv)

end Matrix
end Hex
