/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexDeterminant.LastRow
import all HexDeterminant.LastRow

public section

/-!
Permutation-group structure on permutation vectors.

This module develops the operations on permutation vectors that the elementary
row and column operation laws are built from: `finTranspose` and
`transposePermutationValues`/`swapPermutationValues` (position and value swaps),
`inversePermutationVector`, and `composePermutationValues`. It shows these
preserve membership in `permutationVectors` and tracks their effect on inversion
parity, culminating in `detSign_swapPermutationValues` and the multiplicativity
law `detSign_composePermutationValues`. The elementary-operation determinant
laws themselves live in `HexDeterminant.RowOps`.
-/

namespace Hex
universe u
namespace Matrix
variable {α : Type u}

/-- The transposition of `Fin n` swapping `i` and `j`, sending `r` to `j` if
`r = i`, to `i` if `r = j`, and to itself otherwise. -/
@[expose]
def finTranspose {n : Nat} (i j : Fin n) (r : Fin n) : Fin n :=
  if r = i then j else if r = j then i else r

/-- `finTranspose i j` sends `i` to `j`. -/
private theorem finTranspose_left {n : Nat} (i j : Fin n) :
    finTranspose i j i = j := by
  simp [finTranspose]

/-- `finTranspose i j` sends `j` to `i`. -/
private theorem finTranspose_right {n : Nat} (i j : Fin n) :
    finTranspose i j j = i := by
  by_cases h : j = i
  · subst j
    simp [finTranspose]
  · simp [finTranspose, h]

/-- `finTranspose i j` fixes every `r` distinct from both `i` and `j`. -/
private theorem finTranspose_of_ne {n : Nat} (i j r : Fin n)
    (hi : r ≠ i) (hj : r ≠ j) :
    finTranspose i j r = r := by
  simp [finTranspose, hi, hj]

/-- `finTranspose i j` is an involution: applying it twice returns `r`. -/
private theorem finTranspose_involutive {n : Nat} (i j r : Fin n) :
    finTranspose i j (finTranspose i j r) = r := by
  by_cases hi : r = i
  · subst r
    rw [finTranspose_left, finTranspose_right]
  · by_cases hj : r = j
    · subst r
      rw [finTranspose_right, finTranspose_left]
    · rw [finTranspose_of_ne i j r hi hj]
      exact finTranspose_of_ne i j r hi hj

/-- `finTranspose i j` is injective, since it is its own inverse. -/
private theorem finTranspose_injective {n : Nat} (i j : Fin n) :
    Function.Injective (finTranspose i j) := by
  intro a b h
  have h' := congrArg (finTranspose i j) h
  simpa [finTranspose_involutive] using h'

/-- Mapping `finTranspose i j` over `List.finRange n` permutes it, since the
transposition is a bijection of `Fin n`. -/
private theorem finRange_map_finTranspose_perm {n : Nat} (i j : Fin n) :
    ((List.finRange n).map (finTranspose i j)).Perm (List.finRange n) := by
  apply (List.perm_ext_iff_of_nodup
    (list_nodup_map_of_injective (finTranspose_injective i j) (List.nodup_finRange n))
    (List.nodup_finRange n)).mpr
  intro r
  constructor
  · intro _h
    exact List.mem_finRange r
  · intro _h
    simp only [List.mem_map]
    exact ⟨finTranspose i j r, List.mem_finRange _, by
      rw [finTranspose_involutive]⟩

/-- Precompose a permutation vector `perm` with the transposition swapping rows
`i` and `j`, yielding the vector whose `r`-th entry is `perm[finTranspose i j r]`. -/
private def transposePermutationValues {n : Nat}
    (perm : Vector (Fin n) n) (i j : Fin n) : Vector (Fin n) n :=
  Vector.ofFn fun r => perm[finTranspose i j r]

/-- Entrywise read of a row swap: `(rowSwap M i j)[r][k]` reads from row `i`
when `r = j`, from row `j` when `r = i`, and from row `r` otherwise. -/
private theorem rowSwap_get {R : Type u} {n m : Nat}
    (M : Matrix R n m) (i j r : Fin n) (k : Fin m) :
    (rowSwap M i j)[r][k] =
      if r = j then M[i][k] else if r = i then M[j][k] else M[r][k] :=
  getElem_rowSwap M i j r k

/-- For distinct `i, j`, reading row `r` of `rowSwap M i j` is the same as
reading row `finTranspose i j r` of `M`, identifying the swap with the
transposition. -/
private theorem rowSwap_get_finTranspose {R : Type u} {n m : Nat}
    (M : Matrix R n m) (i j r : Fin n) (h : i ≠ j) (k : Fin m) :
    (rowSwap M i j)[r][k] = M[finTranspose i j r][k] := by
  rw [rowSwap_get]
  by_cases hrj : r = j
  · subst r
    simp [finTranspose, h.symm]
  · by_cases hri : r = i
    · subst r
      simp [finTranspose, hrj]
    · rw [if_neg hrj, if_neg hri]
      exact congrArg (fun row => M[row][k]) (finTranspose_of_ne i j r hri hrj).symm

/-- The `r`-th entry of `transposePermutationValues perm i j` is
`perm[finTranspose i j r]`, unfolding the definition. -/
private theorem transposePermutationValues_get {n : Nat}
    (perm : Vector (Fin n) n) (i j r : Fin n) :
    (transposePermutationValues perm i j)[r] = perm[finTranspose i j r] := by
  simp [transposePermutationValues]

/-- `vector_toList_eq` rewrites a vector's list view as the finite range of indices mapped through its getter. -/
private theorem vector_toList_eq {α : Type u} {n : Nat}
    (v : Vector α n) :
    v.toList = (List.finRange n).map fun i => v[i] := by
  apply List.ext_getElem
  · simp [Vector.length_toList]
  · intro k hk₁ hk₂
    simp

/-- `transposePermutationValues_toList_perm` shows that transposing two positions in a permutation vector only permutes its list of values. -/
private theorem transposePermutationValues_toList_perm {n : Nat}
    (perm : Vector (Fin n) n) (i j : Fin n) :
    (transposePermutationValues perm i j).toList.Perm perm.toList := by
  rw [vector_toList_eq (transposePermutationValues perm i j), vector_toList_eq perm]
  have hleft :
      (List.finRange n).map (fun r => (transposePermutationValues perm i j)[r]) =
        (List.finRange n).map ((fun r => perm[r]) ∘ finTranspose i j) := by
    apply List.map_congr_left
    intro r _hr
    exact transposePermutationValues_get perm i j r
  rw [hleft]
  simpa [List.map_map] using
    (finRange_map_finTranspose_perm i j).map fun r => perm[r]

/-- `transposePermutationValues_mem_permutationVectors` preserves membership in `permutationVectors n` after transposing two positions. -/
private theorem transposePermutationValues_mem_permutationVectors {n : Nat}
    {perm : Vector (Fin n) n} (i j : Fin n)
    (hmem : perm ∈ permutationVectors n) :
    transposePermutationValues perm i j ∈ permutationVectors n := by
  apply permutationVectors_complete
  exact (transposePermutationValues_toList_perm perm i j).symm.nodup
    (permutationVectors_nodup hmem)

/-- `vector_get_fin_congr` transports a vector lookup across an equality of finite indices. -/
private theorem vector_get_fin_congr {α : Type u} {n : Nat} (v : Vector α n)
    {a b : Fin n} (h : a = b) : v[a] = v[b] := by
  subst b
  rfl

/-- `vector_toList_split_two` splits a vector's list view around two strictly ordered finite indices. -/
private theorem vector_toList_split_two {α : Type u} {n : Nat}
    (v : Vector α n) {i j : Fin n} (hij : i.val < j.val) :
    v.toList =
      v.toList.take i.val ++ v[i] ::
        (v.toList.drop (i.val + 1)).take (j.val - i.val - 1) ++
          v[j] :: v.toList.drop (j.val + 1) := by
  have hi : i.val < v.toList.length := by
    simp [Vector.length_toList]
  have hjdrop : j.val - i.val - 1 < (v.toList.drop (i.val + 1)).length := by
    simp only [List.length_drop, Vector.length_toList]
    omega
  calc
    v.toList = v.toList.take i.val ++ v.toList.drop i.val := by
      exact (List.take_append_drop i.val v.toList).symm
    _ = v.toList.take i.val ++ v[i] :: v.toList.drop (i.val + 1) := by
      rw [List.drop_eq_getElem_cons hi]
      simp [Vector.getElem_toList]
    _ =
      v.toList.take i.val ++ v[i] ::
        (v.toList.drop (i.val + 1)).take (j.val - i.val - 1) ++
          (v.toList.drop (i.val + 1)).drop (j.val - i.val - 1) := by
      rw [List.append_assoc]
      congr 1
      congr 1
      exact (List.take_append_drop (j.val - i.val - 1)
        (v.toList.drop (i.val + 1))).symm
    _ =
      v.toList.take i.val ++ v[i] ::
        (v.toList.drop (i.val + 1)).take (j.val - i.val - 1) ++
          v[j] :: v.toList.drop (j.val + 1) := by
      have hmid : i.val + 1 + (j.val - i.val - 1) = j.val := by
        omega
      have hdrop : i.val + 1 + ((j.val - i.val - 1) + 1) = j.val + 1 := by
        omega
      rw [List.drop_eq_getElem_cons hjdrop]
      simp [List.drop_drop, Vector.getElem_toList, List.getElem_drop, hmid, hdrop]

/-- `transposePermutationValues_take_of_lt` identifies the unchanged prefix before the first transposed index. -/
private theorem transposePermutationValues_take_of_lt {n : Nat}
    (perm : Vector (Fin n) n) {i j : Fin n} (hij : i.val < j.val) :
    (transposePermutationValues perm i j).toList.take i.val =
      perm.toList.take i.val := by
  apply List.ext_getElem
  · simp [Vector.length_toList]
  · intro k hk₁ hk₂
    simp [Vector.length_toList] at hk₁ hk₂
    have hk : k < n := by omega
    have hki : (⟨k, hk⟩ : Fin n) ≠ i := by
      intro h
      have : k = i.val := by simpa using congrArg Fin.val h
      omega
    have hkj : (⟨k, hk⟩ : Fin n) ≠ j := by
      intro h
      have : k = j.val := by simpa using congrArg Fin.val h
      omega
    calc
      (List.take i.val (transposePermutationValues perm i j).toList)[k] =
          (transposePermutationValues perm i j)[k]'hk := by
        simp [Vector.getElem_toList]
      _ = perm[k]'hk := by
        change (transposePermutationValues perm i j)[(⟨k, hk⟩ : Fin n)] =
          perm[(⟨k, hk⟩ : Fin n)]
        rw [transposePermutationValues_get]
        exact vector_get_fin_congr perm (finTranspose_of_ne i j ⟨k, hk⟩ hki hkj)
      _ = (List.take i.val perm.toList)[k] := by
        simp [Vector.getElem_toList]

/-- `transposePermutationValues_middle_of_lt` identifies the unchanged middle segment between two transposed indices. -/
private theorem transposePermutationValues_middle_of_lt {n : Nat}
    (perm : Vector (Fin n) n) {i j : Fin n} (hij : i.val < j.val) :
    ((transposePermutationValues perm i j).toList.drop (i.val + 1)).take
        (j.val - i.val - 1) =
      (perm.toList.drop (i.val + 1)).take (j.val - i.val - 1) := by
  apply List.ext_getElem
  · simp [Vector.length_toList]
  · intro k hk₁ hk₂
    simp [Vector.length_toList] at hk₁ hk₂
    have hrlt : i.val + 1 + k < n := by
      omega
    have hri : (⟨i.val + 1 + k, hrlt⟩ : Fin n) ≠ i := by
      intro h
      have : i.val + 1 + k = i.val := by simpa using congrArg Fin.val h
      omega
    have hrj : (⟨i.val + 1 + k, hrlt⟩ : Fin n) ≠ j := by
      intro h
      have : i.val + 1 + k = j.val := by simpa using congrArg Fin.val h
      omega
    calc
      (List.take (j.val - i.val - 1)
          (List.drop (i.val + 1) (transposePermutationValues perm i j).toList))[k] =
          (transposePermutationValues perm i j)[i.val + 1 + k]'hrlt := by
        simp [Vector.getElem_toList]
      _ = perm[i.val + 1 + k]'hrlt := by
        change (transposePermutationValues perm i j)[(⟨i.val + 1 + k, hrlt⟩ : Fin n)] =
          perm[(⟨i.val + 1 + k, hrlt⟩ : Fin n)]
        rw [transposePermutationValues_get]
        exact vector_get_fin_congr perm
          (finTranspose_of_ne i j ⟨i.val + 1 + k, hrlt⟩ hri hrj)
      _ =
          (List.take (j.val - i.val - 1) (List.drop (i.val + 1) perm.toList))[k] := by
        simp [Vector.getElem_toList]

/-- `transposePermutationValues_drop_of_lt` identifies the unchanged suffix after the second transposed index. -/
private theorem transposePermutationValues_drop_of_lt {n : Nat}
    (perm : Vector (Fin n) n) {i j : Fin n} (hij : i.val < j.val) :
    (transposePermutationValues perm i j).toList.drop (j.val + 1) =
      perm.toList.drop (j.val + 1) := by
  apply List.ext_getElem
  · simp [Vector.length_toList]
  · intro k hk₁ hk₂
    simp [Vector.length_toList] at hk₁ hk₂
    have hrlt : j.val + 1 + k < n := by
      omega
    have hri : (⟨j.val + 1 + k, hrlt⟩ : Fin n) ≠ i := by
      intro h
      have : j.val + 1 + k = i.val := by simpa using congrArg Fin.val h
      omega
    have hrj : (⟨j.val + 1 + k, hrlt⟩ : Fin n) ≠ j := by
      intro h
      have : j.val + 1 + k = j.val := by simpa using congrArg Fin.val h
      omega
    calc
      (List.drop (j.val + 1) (transposePermutationValues perm i j).toList)[k] =
          (transposePermutationValues perm i j)[j.val + 1 + k]'hrlt := by
        simp [Vector.getElem_toList]
      _ = perm[j.val + 1 + k]'hrlt := by
        change (transposePermutationValues perm i j)[(⟨j.val + 1 + k, hrlt⟩ : Fin n)] =
          perm[(⟨j.val + 1 + k, hrlt⟩ : Fin n)]
        rw [transposePermutationValues_get]
        exact vector_get_fin_congr perm
          (finTranspose_of_ne i j ⟨j.val + 1 + k, hrlt⟩ hri hrj)
      _ = (List.drop (j.val + 1) perm.toList)[k] := by
        simp [Vector.getElem_toList]

/-- `transposePermutationValues_toList_of_lt` expands the list view when the left transposed index is strictly before the right one. -/
private theorem transposePermutationValues_toList_of_lt {n : Nat}
    (perm : Vector (Fin n) n) {i j : Fin n} (hij : i.val < j.val) :
    (transposePermutationValues perm i j).toList =
      perm.toList.take i.val ++ perm[j] ::
        (perm.toList.drop (i.val + 1)).take (j.val - i.val - 1) ++
          perm[i] :: perm.toList.drop (j.val + 1) := by
  rw [vector_toList_split_two (transposePermutationValues perm i j) hij,
    transposePermutationValues_take_of_lt perm hij,
    transposePermutationValues_middle_of_lt perm hij,
    transposePermutationValues_drop_of_lt perm hij]
  have hi : (transposePermutationValues perm i j)[i] = perm[j] := by
    rw [transposePermutationValues_get]
    exact vector_get_fin_congr perm (finTranspose_left i j)
  have hj : (transposePermutationValues perm i j)[j] = perm[i] := by
    rw [transposePermutationValues_get]
    exact vector_get_fin_congr perm (finTranspose_right i j)
  rw [hi, hj]

/-- `transposePermutationValues_toList_of_gt` expands the list view when the right transposed index is strictly before the left one. -/
private theorem transposePermutationValues_toList_of_gt {n : Nat}
    (perm : Vector (Fin n) n) {i j : Fin n} (hji : j.val < i.val) :
    (transposePermutationValues perm i j).toList =
      perm.toList.take j.val ++ perm[i] ::
        (perm.toList.drop (j.val + 1)).take (i.val - j.val - 1) ++
          perm[j] :: perm.toList.drop (i.val + 1) := by
  have hcomm : transposePermutationValues perm i j = transposePermutationValues perm j i := by
    ext r hr
    apply Fin.val_eq_of_eq
    change (transposePermutationValues perm i j)[(⟨r, hr⟩ : Fin n)] =
      (transposePermutationValues perm j i)[(⟨r, hr⟩ : Fin n)]
    repeat rw [transposePermutationValues_get]
    by_cases hri : (⟨r, hr⟩ : Fin n) = i
    · subst i
      exact vector_get_fin_congr perm
        ((finTranspose_left ⟨r, hr⟩ j).trans
          (finTranspose_right j ⟨r, hr⟩).symm)
    · by_cases hrj : (⟨r, hr⟩ : Fin n) = j
      · subst j
        exact vector_get_fin_congr perm
          ((finTranspose_right i ⟨r, hr⟩).trans
            (finTranspose_left ⟨r, hr⟩ i).symm)
      · exact vector_get_fin_congr perm
          ((finTranspose_of_ne i j ⟨r, hr⟩ hri hrj).trans
            (finTranspose_of_ne j i ⟨r, hr⟩ hrj hri).symm)
  rw [hcomm]
  exact
    (transposePermutationValues_toList_of_lt perm (i := j) (j := i) hji)

/-- `transposePermutationValues_involutive` states that transposing the same two vector positions twice returns the original vector. -/
private theorem transposePermutationValues_involutive {n : Nat}
    (perm : Vector (Fin n) n) (i j : Fin n) :
    transposePermutationValues (transposePermutationValues perm i j) i j = perm := by
  ext r hr
  simp [transposePermutationValues, finTranspose_involutive]

/-- `transposePermutationValues_map_permutationVectors_perm` shows that mapping a fixed value transpose permutes `permutationVectors n`. -/
private theorem transposePermutationValues_map_permutationVectors_perm {n : Nat}
    (i j : Fin n) :
    ((permutationVectors n).map fun perm => transposePermutationValues perm i j).Perm
      (permutationVectors n) := by
  have hmapNodup :
      ((permutationVectors n).map fun perm => transposePermutationValues perm i j).Nodup := by
    exact list_nodup_map_of_injective
      (f := fun perm => transposePermutationValues perm i j)
      (fun a b h => by
        have h' := congrArg (fun perm => transposePermutationValues perm i j) h
        change
          transposePermutationValues (transposePermutationValues a i j) i j =
            transposePermutationValues (transposePermutationValues b i j) i j at h'
        rw [transposePermutationValues_involutive] at h'
        rw [transposePermutationValues_involutive] at h'
        exact h')
      permutationVectors_nodup_list
  apply (List.perm_ext_iff_of_nodup hmapNodup permutationVectors_nodup_list).mpr
  intro perm
  constructor
  · intro hmem
    simp only [List.mem_map] at hmem
    rcases hmem with ⟨pre, hpre, rfl⟩
    exact transposePermutationValues_mem_permutationVectors i j hpre
  · intro hmem
    simp only [List.mem_map]
    refine ⟨transposePermutationValues perm i j,
      transposePermutationValues_mem_permutationVectors i j hmem, ?_⟩
    exact transposePermutationValues_involutive perm i j

/-- Swap the values `i` and `j` inside a permutation vector, leaving positions
fixed. This models the column permutation induced by exchanging two columns. -/
@[expose]
def swapPermutationValues {n : Nat}
    (perm : Vector (Fin n) n) (i j : Fin n) : Vector (Fin n) n :=
  perm.map (finTranspose i j)

private theorem swapPermutationValues_get {n : Nat}
    (perm : Vector (Fin n) n) (i j r : Fin n) :
    (swapPermutationValues perm i j)[r] = finTranspose i j perm[r] := by
  simp [swapPermutationValues]

/-- Entrywise characterization of `swapPermutationValues`: occurrences of
`i` become `j`, occurrences of `j` become `i`, and all other values stay put. -/
theorem swapPermutationValues_get_if {n : Nat}
    (perm : Vector (Fin n) n) (i j r : Fin n) :
    (swapPermutationValues perm i j)[r] =
      if perm[r] = i then j else if perm[r] = j then i else perm[r] := by
  rw [swapPermutationValues_get]
  rfl

private theorem swapPermutationValues_toList_nodup {n : Nat}
    (perm : Vector (Fin n) n) (i j : Fin n)
    (hnodup : perm.toList.Nodup) :
    (swapPermutationValues perm i j).toList.Nodup := by
  change (perm.map (finTranspose i j)).toList.Nodup
  rw [vector_toList_map]
  exact list_nodup_map_of_injective (finTranspose_injective i j) hnodup

private theorem swapPermutationValues_mem_permutationVectors {n : Nat}
    {perm : Vector (Fin n) n} (i j : Fin n)
    (hmem : perm ∈ permutationVectors n) :
    swapPermutationValues perm i j ∈ permutationVectors n := by
  apply permutationVectors_complete
  exact swapPermutationValues_toList_nodup perm i j (permutationVectors_nodup hmem)

private theorem swapPermutationValues_involutive {n : Nat}
    (perm : Vector (Fin n) n) (i j : Fin n) :
    swapPermutationValues (swapPermutationValues perm i j) i j = perm := by
  ext r hr
  simp [swapPermutationValues, finTranspose_involutive]

/-- `fin_mem_of_full_nodup` shows that a length-`n` nodup list of `Fin n`
values contains every `x : Fin n`, the pigeonhole fact that makes the
`inversePermutationValues` index lookup total. -/
private theorem fin_mem_of_full_nodup {n : Nat} {xs : List (Fin n)}
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

/-- `fin_idxOf_lt` bounds `xs.idxOf x` below `xs.length` for a
full nodup list, supplying the `Fin n` index proof obligation for the
`inversePermutationValues` entries. -/
private theorem fin_idxOf_lt {n : Nat} {xs : List (Fin n)}
    (x : Fin n) (hlen : xs.length = n) (hnodup : xs.Nodup) :
    xs.idxOf x < xs.length := by
  exact List.idxOf_lt_length_of_mem (fin_mem_of_full_nodup x hlen hnodup)

/-- The inverse permutation vector: at value `c`, return the position where
`c` occurs in `perm`. -/
def inversePermutationValues {n : Nat}
    (perm : Vector (Fin n) n) (hnodup : perm.toList.Nodup) :
    Vector (Fin n) n :=
  Vector.ofFn fun c =>
    ⟨perm.toList.idxOf c,
      by
        simpa [Vector.length_toList] using
          fin_idxOf_lt c (by simp [Vector.length_toList]) hnodup⟩

/-- `inversePermutationValues_get_value` is the right-inverse law
`perm[inv[c]] = c`, recovering the value `c` by reading `perm` at the position
the inverse records for it. -/
private theorem inversePermutationValues_get_value {n : Nat}
    (perm : Vector (Fin n) n) (hnodup : perm.toList.Nodup) (c : Fin n) :
    perm[(inversePermutationValues perm hnodup)[c]] = c := by
  change
    perm.toList[(inversePermutationValues perm hnodup)[c].val]'(by
      simp [Vector.length_toList]) = c
  simp [inversePermutationValues]

/-- `inversePermutationValues_get_index` is the left-inverse law
`inv[perm[i]] = i`, recovering the position `i` from the value `perm` places
there. -/
private theorem inversePermutationValues_get_index {n : Nat}
    (perm : Vector (Fin n) n) (hnodup : perm.toList.Nodup) (i : Fin n) :
    (inversePermutationValues perm hnodup)[perm[i]] = i := by
  apply Fin.ext
  simp [inversePermutationValues]
  exact hnodup.idxOf_getElem i.val (by simp [Vector.length_toList])

/-- `inversePermutationValues_nodup` shows the inverse permutation vector is
itself nodup, so it is again a valid permutation usable in the determinant
sign-tracking expansion. -/
private theorem inversePermutationValues_nodup {n : Nat}
    (perm : Vector (Fin n) n) (hnodup : perm.toList.Nodup) :
    (inversePermutationValues perm hnodup).toList.Nodup := by
  rw [vector_toList_eq]
  apply list_nodup_map_of_injective
  · intro a b h
    have hval :
        perm[(inversePermutationValues perm hnodup)[a]] =
          perm[(inversePermutationValues perm hnodup)[b]] :=
      congrArg (fun k => perm[k]) h
    rw [inversePermutationValues_get_value perm hnodup a] at hval
    rw [inversePermutationValues_get_value perm hnodup b] at hval
    exact hval
  · exact List.nodup_finRange n

/-- `inversePermutationValues_insertAt_last_castSucc` says inversion commutes
with inserting `Fin.last n`: the inverse of the extended permutation inserts the
original inverse (raised above `i`) at position `i` with value `Fin.last n`, the
recurrence step underlying the inversion-count tracking. -/
private theorem inversePermutationValues_insertAt_last_castSucc {n : Nat}
    (v : Vector (Fin n) n) (i : Fin (n + 1)) (hnodup : v.toList.Nodup) :
    inversePermutationValues
        (insertAt (Fin.last n) (v.map Fin.castSucc) i)
        (insertAt_last_castSucc_nodup v i hnodup) =
      insertAt i ((inversePermutationValues v hnodup).map (raiseFinAbove i))
        (Fin.last n) := by
  ext k hk
  apply Fin.val_eq_of_eq
  let c : Fin (n + 1) := ⟨k, hk⟩
  by_cases hlast : k = n
  · subst k
    have hleft :
        (inversePermutationValues
          (insertAt (Fin.last n) (v.map Fin.castSucc) i)
          (insertAt_last_castSucc_nodup v i hnodup))[Fin.last n] = i := by
      apply Fin.ext
      simp [inversePermutationValues]
      exact insertAt_last_castSucc_idxOf v i hnodup
    have hright :
        (insertAt i ((inversePermutationValues v hnodup).map (raiseFinAbove i))
          (Fin.last n))[Fin.last n] = i := by
      exact insertAt_get_self i ((inversePermutationValues v hnodup).map (raiseFinAbove i))
        (Fin.last n)
    exact hleft.trans hright.symm
  · have hklt : k < n := by omega
    let old : Fin n := ⟨k, hklt⟩
    have hc : c = old.castSucc := Fin.ext rfl
    have hget :
        (insertAt (Fin.last n) (v.map Fin.castSucc) i)[
            raiseFinAbove i ((inversePermutationValues v hnodup)[old])] =
          old.castSucc := by
      rw [insertAt_get_raiseFinAbove]
      simpa using congrArg Fin.castSucc (inversePermutationValues_get_value v hnodup old)
    have hleft :
        (inversePermutationValues
          (insertAt (Fin.last n) (v.map Fin.castSucc) i)
          (insertAt_last_castSucc_nodup v i hnodup))[old.castSucc] =
          raiseFinAbove i ((inversePermutationValues v hnodup)[old]) := by
      apply Fin.ext
      have hgetList :
          (insertAt (Fin.last n) (v.map Fin.castSucc) i).toList[
              (raiseFinAbove i ((inversePermutationValues v hnodup)[old])).val] =
            old.castSucc := by
        simpa [Vector.getElem_toList] using hget
      have hidxOf :=
        (insertAt_last_castSucc_nodup v i hnodup).idxOf_getElem
          (raiseFinAbove i ((inversePermutationValues v hnodup)[old])).val
          (by simp [Vector.length_toList])
      have hidx :
          (insertAt (Fin.last n) (v.map Fin.castSucc) i).toList.idxOf old.castSucc =
            (raiseFinAbove i ((inversePermutationValues v hnodup)[old])).val := by
        exact hgetList ▸ hidxOf
      have hidx' :
          (insertAt (Fin.last n) (v.map Fin.castSucc) i).toList.idxOf
              (⟨old.val, by omega⟩ : Fin (n + 1)) =
            (raiseFinAbove i ((inversePermutationValues v hnodup)[old])).val := by
        exact hidx
      simpa [inversePermutationValues] using hidx'
    have hright :
        (insertAt i ((inversePermutationValues v hnodup).map (raiseFinAbove i))
          (Fin.last n))[old.castSucc] =
          raiseFinAbove i ((inversePermutationValues v hnodup)[old]) := by
      simpa using
        insertAt_last_get_castSucc i
          ((inversePermutationValues v hnodup).map (raiseFinAbove i)) old
    simpa [c, hc] using hleft.trans hright.symm

/-- `inversionCount_inversePermutationValues_insertAt_last_castSucc` gives the
inversion-count recurrence for the inverse permutation under the `Fin.last n`
insertion, adding `n - i` to the original count and so supplying the sign change
for the determinant's column-insertion step. -/
private theorem inversionCount_inversePermutationValues_insertAt_last_castSucc {n : Nat}
    (v : Vector (Fin n) n) (i : Fin (n + 1)) (hnodup : v.toList.Nodup) :
    inversionCount
        (inversePermutationValues
          (insertAt (Fin.last n) (v.map Fin.castSucc) i)
          (insertAt_last_castSucc_nodup v i hnodup)).toList =
      inversionCount (inversePermutationValues v hnodup).toList + (n - i.val) := by
  rw [inversePermutationValues_insertAt_last_castSucc v i hnodup, insertAt_last_toList,
    vector_toList_map, inversionCount_map_raiseFinAbove_append_self, foldCount_full_nodup_ge i]
  · simp [Vector.length_toList]
  · exact inversePermutationValues_nodup v hnodup

private theorem inversionCount_inversePermutationValues_mod_two {n : Nat}
    (perm : Vector (Fin n) n) (hnodup : perm.toList.Nodup) :
    inversionCount (inversePermutationValues perm hnodup).toList % 2 =
      inversionCount perm.toList % 2 := by
  induction n with
  | zero =>
      have hperm_nil : perm.toList = [] := by
        apply List.eq_nil_iff_length_eq_zero.mpr
        simp [Vector.length_toList]
      have hinv_nil : (inversePermutationValues perm hnodup).toList = [] := by
        apply List.eq_nil_iff_length_eq_zero.mpr
        simp [Vector.length_toList]
      simp [hperm_nil, hinv_nil, inversionCount]
  | succ n ih =>
      let k := perm.toList.idxOf (Fin.last n)
      have hk : k < n + 1 := by
        simpa [k, Vector.length_toList] using
          finLast_idxOf_lt (by simp [Vector.length_toList]) hnodup
      have hidx : perm.toList.idxOf (Fin.last n) = k := rfl
      let peeled := peelLastVector perm k hk hidx hnodup
      have hpeeled_nodup : peeled.toList.Nodup :=
        peelLastVector_nodup perm k hk hidx hnodup
      let pos : Fin (n + 1) := ⟨k, hk⟩
      have hinsert :
          insertAt (Fin.last n) (peeled.map Fin.castSucc) pos = perm := by
        simpa [peeled, pos] using
          insertAt_peelLastVector perm k hk hidx hnodup
      have hinv_count :
          inversionCount (inversePermutationValues perm hnodup).toList =
            inversionCount (inversePermutationValues peeled hpeeled_nodup).toList +
              (n - pos.val) := by
        have hnodup_insert :
            (insertAt (Fin.last n) (peeled.map Fin.castSucc) pos).toList.Nodup :=
          insertAt_last_castSucc_nodup peeled pos hpeeled_nodup
        have hinv_eq :
            inversePermutationValues perm hnodup =
              inversePermutationValues
                (insertAt (Fin.last n) (peeled.map Fin.castSucc) pos)
                hnodup_insert := by
          ext c hc
          simp [inversePermutationValues, hinsert]
        rw [hinv_eq]
        simpa [peeled, pos] using
          inversionCount_inversePermutationValues_insertAt_last_castSucc
            peeled pos hpeeled_nodup
      have hperm_count :
          inversionCount perm.toList =
            inversionCount peeled.toList + (n - pos.val) := by
        rw [← hinsert, insertAt_toList, vector_toList_map]
        simpa [peeled, pos, Vector.length_toList] using
          inversionCount_insertIdx_castSucc_last_eq peeled.toList pos.val (by
            simp [Vector.length_toList, pos]
            omega)
      rw [hinv_count, hperm_count]
      have hih := ih peeled hpeeled_nodup
      omega

private theorem detSign_inversePermutationValues {R : Type u} [Lean.Grind.CommRing R] {n : Nat}
    (perm : Vector (Fin n) n) (hnodup : perm.toList.Nodup) :
    detSign (R := R) (inversePermutationValues perm hnodup) = detSign (R := R) perm := by
  unfold detSign
  rw [inversionCount_inversePermutationValues_mod_two perm hnodup]

private theorem inversePermutationValues_mem_permutationVectors {n : Nat}
    {perm : Vector (Fin n) n} (hmem : perm ∈ permutationVectors n) :
    inversePermutationValues perm (permutationVectors_nodup hmem) ∈ permutationVectors n := by
  exact permutationVectors_complete
    (inversePermutationValues_nodup perm (permutationVectors_nodup hmem))

private theorem inversePermutationValues_involutive {n : Nat}
    (perm : Vector (Fin n) n) (hnodup : perm.toList.Nodup) :
    inversePermutationValues
        (inversePermutationValues perm hnodup)
        (inversePermutationValues_nodup perm hnodup) = perm := by
  ext k hk
  apply Fin.val_eq_of_eq
  let i : Fin n := ⟨k, hk⟩
  have h :=
    inversePermutationValues_get_index
      (inversePermutationValues perm hnodup)
      (inversePermutationValues_nodup perm hnodup) (perm[i])
  have hi := inversePermutationValues_get_index perm hnodup i
  have hleft :
      (inversePermutationValues
        (inversePermutationValues perm hnodup)
        (inversePermutationValues_nodup perm hnodup))[i] =
        (inversePermutationValues
          (inversePermutationValues perm hnodup)
          (inversePermutationValues_nodup perm hnodup))[
            (inversePermutationValues perm hnodup)[perm[i]]] :=
    congrArg
      (fun x =>
        (inversePermutationValues
          (inversePermutationValues perm hnodup)
          (inversePermutationValues_nodup perm hnodup))[x])
      hi.symm
  exact hleft.trans h

@[expose]
def inversePermutationVector {n : Nat}
    (perm : Vector (Fin n) n) : Vector (Fin n) n :=
  if hnodup : perm.toList.Nodup then
    inversePermutationValues perm hnodup
  else
    perm

private theorem inversePermutationVector_eq {n : Nat}
    (perm : Vector (Fin n) n) (hnodup : perm.toList.Nodup) :
    inversePermutationVector perm = inversePermutationValues perm hnodup := by
  simp [inversePermutationVector, hnodup]

private theorem inversePermutationVector_mem_permutationVectors {n : Nat}
    {perm : Vector (Fin n) n} (hmem : perm ∈ permutationVectors n) :
    inversePermutationVector perm ∈ permutationVectors n := by
  rw [inversePermutationVector_eq perm (permutationVectors_nodup hmem)]
  exact inversePermutationValues_mem_permutationVectors hmem

private theorem inversePermutationVector_involutive_of_mem {n : Nat}
    {perm : Vector (Fin n) n} (hmem : perm ∈ permutationVectors n) :
    inversePermutationVector (inversePermutationVector perm) = perm := by
  rw [inversePermutationVector_eq perm (permutationVectors_nodup hmem)]
  rw [inversePermutationVector_eq
    (inversePermutationValues perm (permutationVectors_nodup hmem))
    (inversePermutationValues_nodup perm (permutationVectors_nodup hmem))]
  exact inversePermutationValues_involutive perm (permutationVectors_nodup hmem)

@[expose]
def composePermutationValues {n : Nat}
    (sigma tau : Vector (Fin n) n) : Vector (Fin n) n :=
  Vector.ofFn fun i => sigma[tau[i]]

private theorem composePermutationValues_get {n : Nat}
    (sigma tau : Vector (Fin n) n) (i : Fin n) :
    (composePermutationValues sigma tau)[i] = sigma[tau[i]] := by
  simp [composePermutationValues]

private theorem composePermutationValues_nodup {n : Nat}
    {sigma tau : Vector (Fin n) n}
    (hsigma : sigma.toList.Nodup) (htau : tau.toList.Nodup) :
    (composePermutationValues sigma tau).toList.Nodup := by
  rw [vector_toList_eq (composePermutationValues sigma tau)]
  apply list_nodup_map_of_injective
    (f := fun i : Fin n => (composePermutationValues sigma tau)[i])
    ?_ (List.nodup_finRange n)
  intro i j hij
  have hsigma_inj :
      Function.Injective (fun k : Fin n => sigma[k]) := by
    intro a b hab
    have ha_idx :
        sigma.toList.idxOf sigma[a] = a.val := by
      have ha_len : a.val < sigma.toList.length := by
        simp [Vector.length_toList]
      have hget : sigma.toList[a.val] = sigma[a] := by
        simp [Vector.toList]
      simpa [hget] using hsigma.idxOf_getElem a.val ha_len
    have hb_idx :
        sigma.toList.idxOf sigma[b] = b.val := by
      have hb_len : b.val < sigma.toList.length := by
        simp [Vector.length_toList]
      have hget : sigma.toList[b.val] = sigma[b] := by
        simp [Vector.toList]
      simpa [hget] using hsigma.idxOf_getElem b.val hb_len
    apply Fin.ext
    change sigma[a] = sigma[b] at hab
    rw [← ha_idx, ← hb_idx, hab]
  have htau_inj :
      Function.Injective (fun k : Fin n => tau[k]) := by
    intro a b hab
    have ha_idx :
        tau.toList.idxOf tau[a] = a.val := by
      have ha_len : a.val < tau.toList.length := by
        simp [Vector.length_toList]
      have hget : tau.toList[a.val] = tau[a] := by
        simp [Vector.toList]
      simpa [hget] using htau.idxOf_getElem a.val ha_len
    have hb_idx :
        tau.toList.idxOf tau[b] = b.val := by
      have hb_len : b.val < tau.toList.length := by
        simp [Vector.length_toList]
      have hget : tau.toList[b.val] = tau[b] := by
        simp [Vector.toList]
      simpa [hget] using htau.idxOf_getElem b.val hb_len
    apply Fin.ext
    change tau[a] = tau[b] at hab
    rw [← ha_idx, ← hb_idx, hab]
  exact htau_inj (hsigma_inj (by simpa [composePermutationValues] using hij))

private theorem composePermutationValues_mem_permutationVectors {n : Nat}
    {sigma tau : Vector (Fin n) n}
    (hsigma : sigma ∈ permutationVectors n)
    (htau : tau ∈ permutationVectors n) :
    composePermutationValues sigma tau ∈ permutationVectors n := by
  exact permutationVectors_complete
    (composePermutationValues_nodup
      (permutationVectors_nodup hsigma) (permutationVectors_nodup htau))

private theorem composePermutationValues_left_involutive {n : Nat}
    {sigma tau : Vector (Fin n) n}
    (hsigma : sigma ∈ permutationVectors n) :
    composePermutationValues
        (inversePermutationVector sigma)
        (composePermutationValues sigma tau) = tau := by
  ext k hk
  apply Fin.val_eq_of_eq
  let i : Fin n := ⟨k, hk⟩
  change
    (composePermutationValues
        (inversePermutationVector sigma)
        (composePermutationValues sigma tau))[i] = tau[i]
  have hnodup := permutationVectors_nodup hsigma
  rw [inversePermutationVector_eq sigma hnodup]
  simpa [composePermutationValues] using
    inversePermutationValues_get_index sigma hnodup tau[i]

private theorem composePermutationValues_left_inverse {n : Nat}
    {sigma tau : Vector (Fin n) n}
    (hsigma : sigma ∈ permutationVectors n) :
    composePermutationValues sigma
        (composePermutationValues (inversePermutationVector sigma) tau) = tau := by
  have h :=
    composePermutationValues_left_involutive
      (sigma := inversePermutationVector sigma) (tau := tau)
      (inversePermutationVector_mem_permutationVectors hsigma)
  rw [inversePermutationVector_involutive_of_mem hsigma] at h
  exact h

private theorem composePermutationValues_left_map_permutationVectors_perm {n : Nat}
    (sigma : Vector (Fin n) n) (hsigma : sigma ∈ permutationVectors n) :
    ((permutationVectors n).map fun tau => composePermutationValues sigma tau).Perm
      (permutationVectors n) := by
  have hmapNodup :
      ((permutationVectors n).map fun tau => composePermutationValues sigma tau).Nodup := by
    exact list_nodup_map_on permutationVectors_nodup_list (by
      intro a ha b hb hab
      have h' := congrArg
        (fun perm => composePermutationValues (inversePermutationVector sigma) perm) hab
      exact
        (composePermutationValues_left_involutive (sigma := sigma) (tau := a) hsigma).symm.trans
          (h'.trans
            (composePermutationValues_left_involutive (sigma := sigma) (tau := b) hsigma)))
  apply (List.perm_ext_iff_of_nodup hmapNodup permutationVectors_nodup_list).mpr
  intro perm
  constructor
  · intro hmem
    rcases List.mem_map.mp hmem with ⟨pre, hpre, rfl⟩
    exact composePermutationValues_mem_permutationVectors hsigma hpre
  · intro hmem
    apply List.mem_map.mpr
    refine ⟨composePermutationValues (inversePermutationVector sigma) perm,
      ?_, ?_⟩
    · exact composePermutationValues_mem_permutationVectors
        (inversePermutationVector_mem_permutationVectors hsigma) hmem
    · exact composePermutationValues_left_inverse hsigma

private theorem inversePermutationVector_map_permutationVectors_perm {n : Nat} :
    ((permutationVectors n).map inversePermutationVector).Perm
      (permutationVectors n) := by
  have hmapNodup :
      ((permutationVectors n).map inversePermutationVector).Nodup := by
    exact list_nodup_map_on permutationVectors_nodup_list (by
      intro a ha b hb hab
      have h' := congrArg inversePermutationVector hab
      rw [inversePermutationVector_involutive_of_mem ha] at h'
      rw [inversePermutationVector_involutive_of_mem hb] at h'
      exact h')
  apply (List.perm_ext_iff_of_nodup hmapNodup permutationVectors_nodup_list).mpr
  intro perm
  constructor
  · intro hmem
    rcases List.mem_map.mp hmem with ⟨pre, hpre, rfl⟩
    exact inversePermutationVector_mem_permutationVectors hpre
  · intro hmem
    exact List.mem_map.mpr ⟨inversePermutationVector perm,
      inversePermutationVector_mem_permutationVectors hmem,
      inversePermutationVector_involutive_of_mem hmem⟩

private theorem permutationVectors_inverseVector_sum {R : Type u}
    [Lean.Grind.CommRing R] {n : Nat} (f : Vector (Fin n) n → R) :
    (permutationVectors n).foldl
        (fun acc perm => acc + f (inversePermutationVector perm)) 0 =
      (permutationVectors n).foldl (fun acc perm => acc + f perm) 0 := by
  calc
    (permutationVectors n).foldl
        (fun acc perm => acc + f (inversePermutationVector perm)) 0 =
      ((permutationVectors n).map inversePermutationVector).foldl
        (fun acc perm => acc + f perm) 0 := by
        simp [List.foldl_map]
    _ = (permutationVectors n).foldl (fun acc perm => acc + f perm) 0 := by
        exact List.foldl_add_perm f inversePermutationVector_map_permutationVectors_perm 0

private theorem permutationVectors_composePermutationValues_left_sum {R : Type u}
    [Lean.Grind.CommRing R] {n : Nat}
    (sigma : Vector (Fin n) n) (hsigma : sigma ∈ permutationVectors n)
    (f : Vector (Fin n) n → R) :
    (permutationVectors n).foldl
        (fun acc perm => acc + f (composePermutationValues sigma perm)) 0 =
      (permutationVectors n).foldl (fun acc perm => acc + f perm) 0 := by
  calc
    (permutationVectors n).foldl
        (fun acc perm => acc + f (composePermutationValues sigma perm)) 0 =
      ((permutationVectors n).map fun perm => composePermutationValues sigma perm).foldl
        (fun acc perm => acc + f perm) 0 := by
        simp [List.foldl_map]
    _ = (permutationVectors n).foldl (fun acc perm => acc + f perm) 0 := by
        exact List.foldl_add_perm f
          (composePermutationValues_left_map_permutationVectors_perm sigma hsigma) 0

private theorem finRange_map_perm_get_perm {n : Nat}
    (perm : Vector (Fin n) n) (hnodup : perm.toList.Nodup) :
    ((List.finRange n).map fun i => perm[i]).Perm (List.finRange n) := by
  rw [← vector_toList_eq perm]
  apply (List.perm_ext_iff_of_nodup hnodup (List.nodup_finRange n)).mpr
  intro x
  constructor
  · intro _h
    exact List.mem_finRange x
  · intro _h
    exact fin_mem_of_full_nodup x (by simp [Vector.length_toList]) hnodup

private theorem detProduct_colPermute_vector {R : Type u} [Lean.Grind.CommRing R]
    {n : Nat} (M : Matrix R n n) (sigma tau : Vector (Fin n) n) :
    detProduct (ofFn fun r c => M[r][sigma[c]]) tau =
      detProduct M (composePermutationValues sigma tau) := by
  unfold detProduct
  simp only [Fin.foldl_eq_finRange_foldl]
  apply List.foldl_mul_congr
  intro r _hr
  simp only [getElem_pair_eq_nested, getElem_ofFn, composePermutationValues_get]

private theorem detProduct_transpose_inversePermutationValues {R : Type u}
    [Lean.Grind.CommRing R] {n : Nat}
    (M : Matrix R n n) (perm : Vector (Fin n) n) (hnodup : perm.toList.Nodup) :
    detProduct M.transpose perm =
      detProduct M (inversePermutationValues perm hnodup) := by
  unfold detProduct
  simp only [Fin.foldl_eq_finRange_foldl, getElem_pair_eq_nested]
  calc
    (List.finRange n).foldl
        (fun acc r => acc * M.transpose[r][perm[r]]) 1 =
      (List.finRange n).foldl
        (fun acc r => acc * M[perm[r]][r]) 1 := by
        apply List.foldl_mul_congr
        intro r _hmem
        rw [getElem_transpose]
    _ =
      ((List.finRange n).map fun r => perm[r]).foldl
        (fun acc c => acc * M[c][(inversePermutationValues perm hnodup)[c]]) 1 := by
        simp only [List.foldl_map]
        apply List.foldl_mul_congr
        intro r _hmem
        exact congrArg (fun c => M[perm[r]][c])
          (inversePermutationValues_get_index perm hnodup r).symm
    _ =
      (List.finRange n).foldl
        (fun acc c => acc * M[c][(inversePermutationValues perm hnodup)[c]]) 1 := by
        exact List.foldl_mul_perm
          (fun c => M[c][(inversePermutationValues perm hnodup)[c]])
          (finRange_map_perm_get_perm perm hnodup) 1

private theorem swapPermutationValues_eq {n : Nat}
    (perm : Vector (Fin n) n) (i j : Fin n)
    (hnodup : perm.toList.Nodup) :
    let pi : Fin n := ⟨perm.toList.idxOf i,
      by simpa [Vector.length_toList] using
        fin_idxOf_lt i (by simp [Vector.length_toList]) hnodup⟩
    let pj : Fin n := ⟨perm.toList.idxOf j,
      by simpa [Vector.length_toList] using
        fin_idxOf_lt j (by simp [Vector.length_toList]) hnodup⟩
    swapPermutationValues perm i j = transposePermutationValues perm pi pj := by
  dsimp
  ext r hr
  let pi : Fin n := ⟨perm.toList.idxOf i,
    by simpa [Vector.length_toList] using
      fin_idxOf_lt i (by simp [Vector.length_toList]) hnodup⟩
  let pj : Fin n := ⟨perm.toList.idxOf j,
    by simpa [Vector.length_toList] using
      fin_idxOf_lt j (by simp [Vector.length_toList]) hnodup⟩
  have hpi_get : perm[pi] = i := by
    have hlt : perm.toList.idxOf i < perm.toList.length := by
      simpa [pi, Vector.length_toList] using pi.isLt
    have hget : perm.toList[perm.toList.idxOf i]'hlt = i :=
      List.getElem_idxOf (x := i) (xs := perm.toList) hlt
    exact hget
  have hpj_get : perm[pj] = j := by
    have hlt : perm.toList.idxOf j < perm.toList.length := by
      simpa [pj, Vector.length_toList] using pj.isLt
    have hget : perm.toList[perm.toList.idxOf j]'hlt = j :=
      List.getElem_idxOf (x := j) (xs := perm.toList) hlt
    exact hget
  apply Fin.val_eq_of_eq
  change (swapPermutationValues perm i j)[(⟨r, hr⟩ : Fin n)] =
    (transposePermutationValues perm pi pj)[(⟨r, hr⟩ : Fin n)]
  rw [swapPermutationValues_get, transposePermutationValues_get]
  by_cases hri : (⟨r, hr⟩ : Fin n) = pi
  · rw [hri]
    calc
      finTranspose i j perm[pi] = finTranspose i j i := by rw [hpi_get]
      _ = j := finTranspose_left i j
      _ = perm[pj] := hpj_get.symm
      _ = perm[finTranspose pi pj pi] := by
          exact congrArg (fun x => perm[x]) (finTranspose_left pi pj).symm
  · by_cases hrj : (⟨r, hr⟩ : Fin n) = pj
    · rw [hrj]
      calc
        finTranspose i j perm[pj] = finTranspose i j j := by rw [hpj_get]
        _ = i := finTranspose_right i j
        _ = perm[pi] := hpi_get.symm
        _ = perm[finTranspose pi pj pj] := by
            exact congrArg (fun x => perm[x]) (finTranspose_right pi pj).symm
    · have hnot_i : perm[(⟨r, hr⟩ : Fin n)] ≠ i := by
        intro hv
        have hridx : perm.toList.idxOf perm[(⟨r, hr⟩ : Fin n)] = r := by
          have hrlen : r < perm.toList.length := by
            simpa [Vector.length_toList] using hr
          exact hnodup.idxOf_getElem r hrlen
        have hval : r = pi.val := by
          calc
            r = perm.toList.idxOf perm[(⟨r, hr⟩ : Fin n)] := hridx.symm
            _ = perm.toList.idxOf i := by rw [hv]
            _ = pi.val := rfl
        exact hri (Fin.ext hval)
      have hnot_j : perm[(⟨r, hr⟩ : Fin n)] ≠ j := by
        intro hv
        have hridx : perm.toList.idxOf perm[(⟨r, hr⟩ : Fin n)] = r := by
          have hrlen : r < perm.toList.length := by
            simpa [Vector.length_toList] using hr
          exact hnodup.idxOf_getElem r hrlen
        have hval : r = pj.val := by
          calc
            r = perm.toList.idxOf perm[(⟨r, hr⟩ : Fin n)] := hridx.symm
            _ = perm.toList.idxOf j := by rw [hv]
            _ = pj.val := rfl
        exact hrj (Fin.ext hval)
      rw [finTranspose_of_ne i j perm[(⟨r, hr⟩ : Fin n)] hnot_i hnot_j]
      exact vector_get_fin_congr perm (finTranspose_of_ne pi pj ⟨r, hr⟩ hri hrj).symm

private theorem inversionCount_transposePermutationValues_parity {n : Nat}
    (perm : Vector (Fin n) n) (i j : Fin n)
    (hnodup : perm.toList.Nodup) (h : i ≠ j) :
    inversionCount (transposePermutationValues perm i j).toList % 2 =
      (inversionCount perm.toList + 1) % 2 := by
  have hval : i.val ≠ j.val := by
    intro hv
    exact h (Fin.ext hv)
  cases Nat.lt_or_gt_of_ne hval with
  | inl hij =>
      have hnodup_split :
          (perm.toList.take i.val ++ perm[i] ::
              (perm.toList.drop (i.val + 1)).take (j.val - i.val - 1) ++
                perm[j] :: perm.toList.drop (j.val + 1)).Nodup := by
        rw [← vector_toList_split_two perm hij]
        exact hnodup
      have hpar :
          inversionCount
              (perm.toList.take i.val ++ perm[j] ::
                (perm.toList.drop (i.val + 1)).take (j.val - i.val - 1) ++
                  perm[i] :: perm.toList.drop (j.val + 1)) %
              2 =
            (inversionCount perm.toList + 1) % 2 := by
        have hswap :=
          inversionCount_swap_separated_parity
            (perm.toList.take i.val)
            ((perm.toList.drop (i.val + 1)).take (j.val - i.val - 1))
            (perm.toList.drop (j.val + 1)) perm[i] perm[j] hnodup_split
        rw [← vector_toList_split_two perm hij] at hswap
        exact hswap
      rw [transposePermutationValues_toList_of_lt perm hij]
      exact hpar
  | inr hji =>
      have hnodup_split :
          (perm.toList.take j.val ++ perm[j] ::
              (perm.toList.drop (j.val + 1)).take (i.val - j.val - 1) ++
                perm[i] :: perm.toList.drop (i.val + 1)).Nodup := by
        rw [← vector_toList_split_two perm hji]
        exact hnodup
      have hpar :
          inversionCount
              (perm.toList.take j.val ++ perm[i] ::
                (perm.toList.drop (j.val + 1)).take (i.val - j.val - 1) ++
                  perm[j] :: perm.toList.drop (i.val + 1)) %
              2 =
            (inversionCount perm.toList + 1) % 2 := by
        have hswap :=
          inversionCount_swap_separated_parity
            (perm.toList.take j.val)
            ((perm.toList.drop (j.val + 1)).take (i.val - j.val - 1))
            (perm.toList.drop (i.val + 1)) perm[j] perm[i] hnodup_split
        rw [← vector_toList_split_two perm hji] at hswap
        exact hswap
      rw [transposePermutationValues_toList_of_gt perm hji]
      exact hpar

private theorem detProduct_rowSwap_transposeValues {R : Type u}
    [Lean.Grind.CommRing R] {n : Nat}
    (M : Matrix R n n) (i j : Fin n) (h : i ≠ j) (perm : Vector (Fin n) n) :
    detProduct (rowSwap M i j) perm =
      detProduct M (transposePermutationValues perm i j) := by
  unfold detProduct
  simp only [Fin.foldl_eq_finRange_foldl, getElem_pair_eq_nested]
  calc
    (List.finRange n).foldl
        (fun acc r => acc * (rowSwap M i j)[r][perm[r]]) 1 =
      (List.finRange n).foldl
        (fun acc r => acc * M[finTranspose i j r][perm[r]]) 1 := by
        apply List.foldl_mul_congr
        intro r _hmem
        exact rowSwap_get_finTranspose M i j r h perm[r]
    _ =
      ((List.finRange n).map (finTranspose i j)).foldl
        (fun acc r => acc * M[r][perm[finTranspose i j r]]) 1 := by
        simp only [List.foldl_map]
        apply List.foldl_mul_congr
        intro r _hmem
        exact congrArg (fun k => M[finTranspose i j r][k])
          (vector_get_fin_congr perm (finTranspose_involutive i j r).symm)
    _ =
      (List.finRange n).foldl
        (fun acc r => acc * M[r][perm[finTranspose i j r]]) 1 := by
        exact List.foldl_mul_perm
          (fun r => M[r][perm[finTranspose i j r]])
          (finRange_map_finTranspose_perm i j) 1
    _ =
      (List.finRange n).foldl
        (fun acc r => acc * M[r][(transposePermutationValues perm i j)[r]]) 1 := by
        apply List.foldl_mul_congr
        intro r _hmem
        exact congrArg (fun k => M[r][k])
          (transposePermutationValues_get perm i j r).symm

private theorem detSign_transposeValues {R : Type u}
    [Lean.Grind.CommRing R] {n : Nat}
    (perm : Vector (Fin n) n) (i j : Fin n)
    (hnodup : perm.toList.Nodup) (h : i ≠ j) :
    detSign (R := R) perm = -detSign (R := R) (transposePermutationValues perm i j) := by
  unfold detSign
  have hpar :=
    inversionCount_transposePermutationValues_parity perm i j hnodup h
  by_cases hp : inversionCount perm.toList % 2 = 0
  · have ht : inversionCount (transposePermutationValues perm i j).toList % 2 ≠ 0 := by
      omega
    simp [hp, ht]
    grind
  · have hpone : inversionCount perm.toList % 2 = 1 := by
      have hlt : inversionCount perm.toList % 2 < 2 := Nat.mod_lt _ (by decide)
      omega
    have ht : inversionCount (transposePermutationValues perm i j).toList % 2 = 0 := by
      omega
    simp [hp, ht]

/-- Swapping two distinct values in a duplicate-free permutation vector flips
the determinant sign. This is the sign bookkeeping for column swaps. -/
theorem detSign_swapPermutationValues {R : Type u}
    [Lean.Grind.CommRing R] {n : Nat}
    (perm : Vector (Fin n) n) (i j : Fin n)
    (hnodup : perm.toList.Nodup) (h : i ≠ j) :
    detSign (R := R) perm = -detSign (R := R) (swapPermutationValues perm i j) := by
  let pi : Fin n := ⟨perm.toList.idxOf i,
    by simpa [Vector.length_toList] using
      fin_idxOf_lt i (by simp [Vector.length_toList]) hnodup⟩
  let pj : Fin n := ⟨perm.toList.idxOf j,
    by simpa [Vector.length_toList] using
      fin_idxOf_lt j (by simp [Vector.length_toList]) hnodup⟩
  have hpij : pi ≠ pj := by
    intro hp
    have hpi_get : perm[pi] = i := by
      have hlt : perm.toList.idxOf i < perm.toList.length := by
        simpa [pi, Vector.length_toList] using pi.isLt
      have hget : perm.toList[perm.toList.idxOf i]'hlt = i :=
        List.getElem_idxOf (x := i) (xs := perm.toList) hlt
      exact hget
    have hpj_get : perm[pj] = j := by
      have hlt : perm.toList.idxOf j < perm.toList.length := by
        simpa [pj, Vector.length_toList] using pj.isLt
      have hget : perm.toList[perm.toList.idxOf j]'hlt = j :=
        List.getElem_idxOf (x := j) (xs := perm.toList) hlt
      exact hget
    exact h (by rw [← hpi_get, ← hpj_get, hp])
  have hswap :
      swapPermutationValues perm i j = transposePermutationValues perm pi pj := by
    simpa [pi, pj] using swapPermutationValues_eq perm i j hnodup
  rw [hswap]
  exact detSign_transposeValues (R := R) perm pi pj hnodup hpij

/-- An adjacent swap at a descent strictly decreases inversion count by 1. -/
private theorem inversionCount_adjacent_swap_descent {n : Nat}
    (pre post : List (Fin n)) (a b : Fin n) (hba : b < a) :
    inversionCount (pre ++ a :: b :: post) =
      inversionCount (pre ++ b :: a :: post) + 1 := by
  rw [show pre ++ a :: b :: post = pre ++ ([a, b] ++ post) by simp,
    show pre ++ b :: a :: post = pre ++ ([b, a] ++ post) by simp]
  have hcross :
      crossInversionCount pre ([a, b] ++ post) =
        crossInversionCount pre ([b, a] ++ post) := by
    repeat rw [crossInversionCount_append_right]
    rw [crossInversionCount_pair_swap_right]
  have htail :
      crossInversionCount [a, b] post =
        crossInversionCount [b, a] post :=
    crossInversionCount_pair_swap_left post a b
  rw [inversionCount_append pre ([a, b] ++ post), inversionCount_append pre ([b, a] ++ post),
    hcross, inversionCount_append [a, b] post, inversionCount_append [b, a] post, htail,
    inversionCount_pair a b, inversionCount_pair b a]
  have hab' : ¬ a < b := by omega
  simp [hba, hab']
  omega

/-- For an adjacent descent pair in a permutation vector, transposing the two
positions decreases the inversion count by exactly one. -/
private theorem inversionCount_transposePermutationValues_adjacent_descent
    {n : Nat} (perm : Vector (Fin n) n)
    {i j : Fin n} (hij : i.val + 1 = j.val) (hdesc : perm[j] < perm[i]) :
    inversionCount perm.toList =
      inversionCount (transposePermutationValues perm i j).toList + 1 := by
  have hlt : i.val < j.val := by omega
  have hmid : j.val - i.val - 1 = 0 := by omega
  rw [vector_toList_split_two perm hlt, hmid,
      transposePermutationValues_toList_of_lt perm hlt, hmid]
  simp only [List.take_zero]
  -- After simplification, both lists have the form `pre ++ x :: y :: post`,
  -- and we apply the strict-decrease lemma.
  have h := inversionCount_adjacent_swap_descent
    (perm.toList.take i.val) (perm.toList.drop (j.val + 1))
    perm[i] perm[j] hdesc
  simpa using h

/-- Composition distributes over right transposition of positions. -/
private theorem composePermutationValues_transposePermutationValues_right
    {n : Nat} (sigma tau : Vector (Fin n) n) (i j : Fin n) :
    composePermutationValues sigma (transposePermutationValues tau i j) =
      transposePermutationValues (composePermutationValues sigma tau) i j := by
  ext k hk
  apply Fin.val_eq_of_eq
  let r : Fin n := ⟨k, hk⟩
  show
    (composePermutationValues sigma (transposePermutationValues tau i j))[r] =
      (transposePermutationValues (composePermutationValues sigma tau) i j)[r]
  have h1 : (composePermutationValues sigma (transposePermutationValues tau i j))[r] =
      sigma[(transposePermutationValues tau i j)[r]] :=
    composePermutationValues_get sigma (transposePermutationValues tau i j) r
  have h2 : (transposePermutationValues tau i j)[r] = tau[finTranspose i j r] :=
    transposePermutationValues_get tau i j r
  have h3 : (transposePermutationValues (composePermutationValues sigma tau) i j)[r] =
      (composePermutationValues sigma tau)[finTranspose i j r] :=
    transposePermutationValues_get (composePermutationValues sigma tau) i j r
  have h4 : (composePermutationValues sigma tau)[finTranspose i j r] =
      sigma[tau[finTranspose i j r]] :=
    composePermutationValues_get sigma tau (finTranspose i j r)
  rw [h1, h3, h4]
  exact congrArg (fun x => sigma[x]) h2

private theorem exists_adjacent_descent {n : Nat}
    (perm : Vector (Fin n) n) (hnodup : perm.toList.Nodup)
    (hpos : 0 < inversionCount perm.toList) :
    ∃ i : Fin n, ∃ hij : i.val + 1 < n,
      perm[(⟨i.val + 1, hij⟩ : Fin n)] < perm[i] := by
  induction n with
  | zero =>
      have hnil : perm.toList = [] := by
        apply List.eq_nil_iff_length_eq_zero.mpr
        simp [Vector.length_toList]
      simp [hnil, inversionCount] at hpos
  | succ n ih =>
      let k := perm.toList.idxOf (Fin.last n)
      have hk : k < n + 1 := by
        simpa [k, Vector.length_toList] using
          finLast_idxOf_lt (by simp [Vector.length_toList]) hnodup
      have hidx : perm.toList.idxOf (Fin.last n) = k := rfl
      let peeled := peelLastVector perm k hk hidx hnodup
      have hpeeled_nodup : peeled.toList.Nodup :=
        peelLastVector_nodup perm k hk hidx hnodup
      let pos : Fin (n + 1) := ⟨k, hk⟩
      have hinsert :
          insertAt (Fin.last n) (peeled.map Fin.castSucc) pos = perm := by
        simpa [peeled, pos] using
          insertAt_peelLastVector perm k hk hidx hnodup
      have hcount :
          inversionCount perm.toList =
            inversionCount peeled.toList + (n - pos.val) := by
        rw [← hinsert, insertAt_toList, vector_toList_map]
        simpa [peeled, pos, Vector.length_toList] using
          inversionCount_insertIdx_castSucc_last_eq peeled.toList pos.val (by
            simp [Vector.length_toList, pos]
            omega)
      by_cases hlast : pos.val = n
      · have hpeeled_pos : 0 < inversionCount peeled.toList := by
          rw [hcount] at hpos
          omega
        rcases ih peeled hpeeled_nodup hpeeled_pos with ⟨i, hij, hdesc⟩
        have hijSucc : i.val + 1 < n + 1 := by omega
        let iUp : Fin (n + 1) := ⟨i.val, by omega⟩
        have hijUp : iUp.val + 1 < n + 1 := by simp [iUp, hijSucc]
        refine ⟨iUp, hijUp, ?_⟩
        · have hpos_eq : pos = Fin.last n := Fin.ext hlast
          have hget_next :
              perm[(⟨i.val + 1, hijSucc⟩ : Fin (n + 1))] =
                (peeled[(⟨i.val + 1, hij⟩ : Fin n)]).castSucc := by
            have hraw :
                (insertAt (Fin.last n) (peeled.map Fin.castSucc) (Fin.last n))[
                    (⟨i.val + 1, hijSucc⟩ : Fin (n + 1))] =
                  (peeled[(⟨i.val + 1, hij⟩ : Fin n)]).castSucc := by
              have hraise :
                  raiseFinAbove (Fin.last n) (⟨i.val + 1, hij⟩ : Fin n) =
                    (⟨i.val + 1, hijSucc⟩ : Fin (n + 1)) := by
                apply Fin.ext
                simp [raiseFinAbove, hij]
              have hbase := insertAt_get_raiseFinAbove
                (Fin.last n) (peeled.map Fin.castSucc) (Fin.last n)
                (⟨i.val + 1, hij⟩ : Fin n)
              have hbase' :
                  (insertAt (Fin.last n) (peeled.map Fin.castSucc) (Fin.last n))[
                      raiseFinAbove (Fin.last n) (⟨i.val + 1, hij⟩ : Fin n)] =
                    (peeled[(⟨i.val + 1, hij⟩ : Fin n)]).castSucc := by
                simpa using hbase
              exact (vector_get_fin_congr
                (insertAt (Fin.last n) (peeled.map Fin.castSucc) (Fin.last n))
                hraise).symm.trans hbase'
            have hinsert_last :
                insertAt (Fin.last n) (peeled.map Fin.castSucc) (Fin.last n) = perm :=
              (congrArg (fun p => insertAt (Fin.last n) (peeled.map Fin.castSucc) p)
                hpos_eq).symm.trans hinsert
            have hperm :=
              congrArg
                (fun v : Vector (Fin (n + 1)) (n + 1) =>
                  v[(⟨i.val + 1, hijSucc⟩ : Fin (n + 1))])
                hinsert_last
            exact hperm.symm.trans hraw
          have hget_i :
                perm[iUp] = (peeled[i]).castSucc := by
              have hraw :
                  (insertAt (Fin.last n) (peeled.map Fin.castSucc) (Fin.last n))[iUp] =
                    (peeled[i]).castSucc := by
                have hraise : raiseFinAbove (Fin.last n) i = iUp := by
                  apply Fin.ext
                  simp [raiseFinAbove, iUp]
                have hbase := insertAt_get_raiseFinAbove
                  (Fin.last n) (peeled.map Fin.castSucc) (Fin.last n) i
                have hbase' :
                    (insertAt (Fin.last n) (peeled.map Fin.castSucc) (Fin.last n))[
                        raiseFinAbove (Fin.last n) i] = (peeled[i]).castSucc := by
                  simpa using hbase
                exact (vector_get_fin_congr
                  (insertAt (Fin.last n) (peeled.map Fin.castSucc) (Fin.last n))
                  hraise).symm.trans hbase'
              have hinsert_last :
                  insertAt (Fin.last n) (peeled.map Fin.castSucc) (Fin.last n) = perm :=
                (congrArg (fun p => insertAt (Fin.last n) (peeled.map Fin.castSucc) p)
                  hpos_eq).symm.trans hinsert
              have hperm :=
                congrArg
                  (fun v : Vector (Fin (n + 1)) (n + 1) => v[iUp])
                  hinsert_last
              exact hperm.symm.trans hraw
          have hidx_up :
              (⟨iUp.val + 1, hijUp⟩ : Fin (n + 1)) =
                (⟨i.val + 1, hijSucc⟩ : Fin (n + 1)) := by
            apply Fin.ext
            simp [iUp]
          have hget_next_up :
              perm[(⟨iUp.val + 1, hijUp⟩ : Fin (n + 1))] =
                (peeled[(⟨i.val + 1, hij⟩ : Fin n)]).castSucc :=
            (vector_get_fin_congr perm hidx_up).trans hget_next
          rw [hget_next_up, hget_i]
          simpa [Fin.lt_def] using hdesc
      · have hk_lt_n : k < n := by
          have hk_le : k ≤ n := Nat.lt_succ_iff.mp hk
          have hpos_val : pos.val = k := rfl
          omega
        have hnextK : (⟨k, hk⟩ : Fin (n + 1)).val + 1 < n + 1 := by
          simpa using Nat.succ_lt_succ hk_lt_n
        refine ⟨(⟨k, hk⟩ : Fin (n + 1)), hnextK, ?_⟩
        · have hget_left : perm[(⟨k, hk⟩ : Fin (n + 1))] = Fin.last n := by
            have hraw :
                (insertAt (Fin.last n) (peeled.map Fin.castSucc) pos)[pos] = Fin.last n :=
              insertAt_get_self (Fin.last n) (peeled.map Fin.castSucc) pos
            have hperm :=
              congrArg (fun v : Vector (Fin (n + 1)) (n + 1) => v[pos]) hinsert
            exact hperm.symm.trans hraw
          have hget_right :
              perm[(⟨k + 1, hnextK⟩ : Fin (n + 1))] =
                (peeled[(⟨k, hk_lt_n⟩ : Fin n)]).castSucc := by
            have hraise :
                raiseFinAbove pos (⟨k, hk_lt_n⟩ : Fin n) =
                  (⟨k + 1, hnextK⟩ : Fin (n + 1)) := by
              apply Fin.ext
              simp [raiseFinAbove, pos]
            have hraw :
                (insertAt (Fin.last n) (peeled.map Fin.castSucc) pos)[
                    (⟨k + 1, hnextK⟩ : Fin (n + 1))] =
                  (peeled[(⟨k, hk_lt_n⟩ : Fin n)]).castSucc := by
              have hbase := insertAt_get_raiseFinAbove
                (Fin.last n) (peeled.map Fin.castSucc) pos (⟨k, hk_lt_n⟩ : Fin n)
              have hbase' :
                  (insertAt (Fin.last n) (peeled.map Fin.castSucc) pos)[
                      raiseFinAbove pos (⟨k, hk_lt_n⟩ : Fin n)] =
                    (peeled[(⟨k, hk_lt_n⟩ : Fin n)]).castSucc := by
                simpa using hbase
              exact (vector_get_fin_congr
                (insertAt (Fin.last n) (peeled.map Fin.castSucc) pos)
                hraise).symm.trans hbase'
            have hperm :=
              congrArg
                (fun v : Vector (Fin (n + 1)) (n + 1) =>
                  v[(⟨k + 1, hnextK⟩ : Fin (n + 1))])
                hinsert
            exact hperm.symm.trans hraw
          rw [hget_right, hget_left]
          simp [Fin.lt_def]

private theorem perm_eq_identity {n : Nat}
    (perm : Vector (Fin n) n) (hmem : perm ∈ permutationVectors n)
    (hinv : inversionCount perm.toList = 0) :
    perm = Vector.ofFn fun i : Fin n => i := by
  induction n with
  | zero =>
      ext i hi
      omega
  | succ n ih =>
      have hnodup : perm.toList.Nodup := permutationVectors_nodup hmem
      let k := perm.toList.idxOf (Fin.last n)
      have hk : k < n + 1 := by
        simpa [k, Vector.length_toList] using
          finLast_idxOf_lt (by simp [Vector.length_toList]) hnodup
      have hidx : perm.toList.idxOf (Fin.last n) = k := rfl
      let peeled := peelLastVector perm k hk hidx hnodup
      have hpeeled_nodup : peeled.toList.Nodup :=
        peelLastVector_nodup perm k hk hidx hnodup
      have hpeeled_mem : peeled ∈ permutationVectors n :=
        permutationVectors_complete hpeeled_nodup
      let pos : Fin (n + 1) := ⟨k, hk⟩
      have hinsert :
          insertAt (Fin.last n) (peeled.map Fin.castSucc) pos = perm := by
        simpa [peeled, pos] using
          insertAt_peelLastVector perm k hk hidx hnodup
      have hcount :
          inversionCount perm.toList =
            inversionCount peeled.toList + (n - pos.val) := by
        rw [← hinsert, insertAt_toList, vector_toList_map]
        simpa [peeled, pos, Vector.length_toList] using
          inversionCount_insertIdx_castSucc_last_eq peeled.toList pos.val (by
            simp [Vector.length_toList, pos]
            omega)
      have hpos : pos.val = n := by
        rw [hcount] at hinv
        omega
      have hpeeled_zero : inversionCount peeled.toList = 0 := by
        rw [hcount] at hinv
        omega
      have hpeeled_id : peeled = Vector.ofFn fun i : Fin n => i :=
        ih peeled hpeeled_mem hpeeled_zero
      rw [← hinsert, hpeeled_id]
      have hpos_eq : pos = Fin.last n := Fin.ext hpos
      rw [hpos_eq]
      have hvec :
          (Vector.ofFn fun i : Fin (n + 1) => i) =
            insertAt (Fin.last n)
              ((Vector.ofFn fun i : Fin n => i).map Fin.castSucc) (Fin.last n) := by
        ext r hr
        by_cases hlast : r = n
        · subst r
          simp [insertAt, List.getElem_insertIdx_self]
        · have hr_lt : r < n := by omega
          simp [insertAt, List.getElem_insertIdx_of_lt, hr_lt]
      exact hvec.symm

/-- Multiplicativity of `detSign` under composition of permutation vectors.
The sign of a composed permutation equals the product of the component signs. -/
theorem detSign_composePermutationValues
    {R : Type u} [Lean.Grind.CommRing R] {n : Nat}
    (sigma tau : Vector (Fin n) n)
    (hsigma : sigma ∈ permutationVectors n)
    (htau : tau ∈ permutationVectors n) :
    detSign (R := R) (composePermutationValues sigma tau) =
      detSign (R := R) sigma * detSign (R := R) tau := by
  suffices h : ∀ k, ∀ tau' : Vector (Fin n) n,
      tau' ∈ permutationVectors n →
      inversionCount tau'.toList = k →
      detSign (R := R) (composePermutationValues sigma tau') =
        detSign (R := R) sigma * detSign (R := R) tau' by
    exact h _ tau htau rfl
  intro k
  induction k using Nat.strongRecOn with
  | ind k ih =>
    intro tau' htau' hcount
    by_cases hk : k = 0
    · subst hk
      have hid : tau' = Vector.ofFn fun i : Fin n => i :=
        perm_eq_identity tau' htau' hcount
      have hcompose_id :
          composePermutationValues sigma tau' = sigma := by
        rw [hid]
        ext r hr
        simp [composePermutationValues]
      rw [hcompose_id, hid, detSign_identity]
      grind
    · have hpos : 0 < inversionCount tau'.toList := by
        rw [hcount]; omega
      have hnodup_tau' := permutationVectors_nodup htau'
      obtain ⟨i, hij, hdesc⟩ := exists_adjacent_descent tau' hnodup_tau' hpos
      let j : Fin n := ⟨i.val + 1, hij⟩
      have hij_eq : i.val + 1 = j.val := rfl
      have hi_ne_j : i ≠ j := by
        intro h
        have hvals := congrArg Fin.val h
        have hjval : j.val = i.val + 1 := rfl
        omega
      have hdesc' : tau'[j] < tau'[i] := hdesc
      have hcount_dec :
          inversionCount tau'.toList =
            inversionCount (transposePermutationValues tau' i j).toList + 1 :=
        inversionCount_transposePermutationValues_adjacent_descent
          tau' hij_eq hdesc'
      have htau''_mem :
          transposePermutationValues tau' i j ∈ permutationVectors n :=
        transposePermutationValues_mem_permutationVectors i j htau'
      have hk_dec :
          inversionCount (transposePermutationValues tau' i j).toList < k := by
        omega
      have ih_eq :=
        ih _ hk_dec (transposePermutationValues tau' i j) htau''_mem rfl
      have hcompose :
          composePermutationValues sigma (transposePermutationValues tau' i j) =
            transposePermutationValues
              (composePermutationValues sigma tau') i j :=
        composePermutationValues_transposePermutationValues_right sigma tau' i j
      have hsign_tau :
          detSign (R := R) tau' =
            -detSign (R := R) (transposePermutationValues tau' i j) :=
        detSign_transposeValues (R := R) tau' i j hnodup_tau' hi_ne_j
      have hnodup_compose :
          (composePermutationValues sigma tau').toList.Nodup :=
        composePermutationValues_nodup
          (permutationVectors_nodup hsigma) hnodup_tau'
      have hsign_compose :
          detSign (R := R) (composePermutationValues sigma tau') =
            -detSign (R := R)
                (transposePermutationValues
                  (composePermutationValues sigma tau') i j) :=
        detSign_transposeValues (R := R)
          (composePermutationValues sigma tau') i j hnodup_compose hi_ne_j
      rw [hsign_compose, ← hcompose, ih_eq, hsign_tau]
      grind

/-- Inverse-orientation form of `detSign_composePermutationValues`: the sign of
`tau` is the sign of `sigma` times the sign of `composePermutationValues sigma tau`. -/
theorem detSign_eq_mul_detSign_composePermutationValues
    {R : Type u} [Lean.Grind.CommRing R] {n : Nat}
    (sigma tau : Vector (Fin n) n)
    (hsigma : sigma ∈ permutationVectors n)
    (htau : tau ∈ permutationVectors n) :
    detSign (R := R) tau =
      detSign (R := R) sigma *
        detSign (R := R) (composePermutationValues sigma tau) := by
  have hmul :=
    detSign_composePermutationValues (R := R) sigma tau hsigma htau
  have hsq : detSign (R := R) sigma * detSign (R := R) sigma = 1 := by
    unfold detSign
    by_cases hp : inversionCount sigma.toList % 2 = 0
    · simp [hp]; grind
    · simp [hp]; grind
  rw [hmul]
  grind

end Matrix
end Hex
