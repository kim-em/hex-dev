module

public import HexMatrix.Determinant.Minor
import all HexMatrix.Determinant.Minor
import all HexMatrix.Determinant.Leibniz
import all HexMatrix.Determinant.Enumeration

public section

namespace Hex
universe u
namespace Matrix
variable {α : Type u}

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
      rw [hhead]
      rw [ih (acc + if i.val ≤ x.val then 1 else 0)]
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
  rw [inversionCount_append]
  rw [inversionCount_map_raiseFinAbove]
  have hsingle : inversionCount ([i] : List (Fin (n + 1))) = 0 := by
    simp [inversionCount]
  rw [hsingle]
  rw [crossInversionCount_singleton_right]
  rw [inversionFold_map_raiseFinAbove_self i xs 0]
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
                exact foldl_acc_congr (List.finRange (n + 1))
                  (fun (acc : Nat) (y : Fin (n + 1)) =>
                    acc + if i.val ≤ y.val then 1 else 0)
                  (fun (acc : Nat) (_y : Fin (n + 1)) => acc) 0 hfalse
          _ = 0 := foldl_ignore (List.finRange (n + 1)) 0
          _ = n + 1 - i.val := by omega
      · have hiLt : i.val < n + 1 := by omega
        let i' : Fin (n + 1) := ⟨i.val, hiLt⟩
        rw [List.finRange_succ_last]
        rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
        rw [foldCount_map_castSucc_ge i' (List.finRange n) 0]
        rw [ih i']
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
      rw [foldCount_start xs p ((0 + if p y then 1 else 0) + if p x then 1 else 0)]
      rw [foldCount_start xs p ((0 + if p x then 1 else 0) + if p y then 1 else 0)]
      omega
  | trans _ _ ih₁ ih₂ =>
      exact ih₁.trans ih₂

/-- Every `x : Fin n` is a member of a nodup list of `Fin n` whose length is `n`. -/
private theorem fin_mem_of_full_nodup_for_count {n : Nat} {xs : List (Fin n)}
    (x : Fin n) (hlen : xs.length = n) (hnodup : xs.Nodup) :
    x ∈ xs := by
  by_cases hmem : x ∈ xs
  · exact hmem
  · exfalso
    have hsub : List.Subperm xs ((List.finRange n).erase x) := by
      apply List.subperm_of_subset hnodup
      intro y hy
      exact (List.mem_erase_of_ne (by
        intro hyx
        exact hmem (hyx ▸ hy))).2 (List.mem_finRange y)
    have hle : xs.length ≤ ((List.finRange n).erase x).length :=
      List.Subperm.length_le hsub
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
    exact fin_mem_of_full_nodup_for_count x hlen hnodup

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
        simpa [Vector.getElem_toList] using hy
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
  rw [insertAt_toList]
  rw [peelLastVector_castSucc_toList perm k hk hidx hnodup]
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
    rw [← insertAt_last_castSucc_idxOf v i hv]
    rw [h]
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

/-- Appending the new largest value in the last position does not change
the determinant sign, because it adds no inversions. -/
theorem detSign_insertAt_last {R : Type u} [Lean.Grind.Ring R] {n : Nat}
    (v : Vector (Fin n) n) :
    detSign (R := R)
      (insertAt (Fin.last n) (v.map Fin.castSucc) (Fin.last n)) =
    detSign (R := R) v := by
  unfold detSign
  rw [insertAt_last_toList, vector_toList_map, inversionCount_insert_last_castSucc]

private theorem detSignParity_add {R : Type u} [Lean.Grind.Ring R] (a m : Nat) :
    (if (a + m) % 2 = 0 then (1 : R) else -1) =
      (-1 : R) ^ m * if a % 2 = 0 then (1 : R) else -1 := by
  induction m with
  | zero =>
      simp [Nat.add_zero]
      grind
  | succ m ih =>
      rw [Nat.add_succ]
      rw [Lean.Grind.Semiring.pow_succ]
      rw [show (-1 : R) ^ m * -1 * (if a % 2 = 0 then (1 : R) else -1) =
          -1 * ((-1 : R) ^ m * if a % 2 = 0 then (1 : R) else -1) by
        grind]
      rw [← ih]
      have hsucc : (a + m).succ = a + (m + 1) := by omega
      rw [hsucc]
      by_cases hm : (a + m) % 2 = 0
      · have hmnot' : ¬(a + (m + 1)) % 2 = 0 := by omega
        rw [if_pos hm, if_neg hmnot']
        grind
      · have hmnext' : (a + (m + 1)) % 2 = 0 := by omega
        rw [if_neg hm, if_pos hmnext']
        grind

private theorem detSign_of_inversionCount_add {R : Type u} [Lean.Grind.Ring R]
    {n n' : Nat} (perm : Vector (Fin n) n) (perm' : Vector (Fin n') n') (m : Nat)
    (h :
      inversionCount perm'.toList =
        inversionCount perm.toList + m) :
    detSign (R := R) perm' = (-1 : R) ^ m * detSign (R := R) perm := by
  unfold detSign
  rw [h]
  exact detSignParity_add (R := R) (inversionCount perm.toList) m

private theorem detSign_insertAt_prefix {R : Type u} [Lean.Grind.Ring R] {k : Nat}
    (v : Vector (Fin (k + 1)) (k + 1)) (r : Fin k) :
    detSign (R := R)
      (insertAt (Fin.last (k + 1)) (v.map Fin.castSucc) r.castSucc.castSucc) =
      (-1 : R) ^ (k + 1 - r.val) * detSign (R := R) v := by
  apply detSign_of_inversionCount_add
  rw [insertAt_toList, vector_toList_map]
  change inversionCount ((v.toList.map Fin.castSucc).insertIdx r.val (Fin.last (k + 1))) =
    inversionCount v.toList + (k + 1 - r.val)
  simpa [Vector.length_toList] using
    inversionCount_insertIdx_castSucc_last_eq v.toList r.val (by
      simp [Vector.length_toList]
      omega)

/-- The identity permutation has positive determinant sign. -/
theorem detSign_identity {R : Type u} [Lean.Grind.Ring R] (n : Nat) :
    detSign (R := R) (Vector.ofFn fun i : Fin n => i) = 1 := by
  induction n with
  | zero =>
      have hvec : (Vector.ofFn fun i : Fin 0 => i) = #v[] := by
        ext i hi
        omega
      simp [hvec, detSign, inversionCount]
  | succ n ih =>
      have hvec :
          (Vector.ofFn fun i : Fin (n + 1) => i) =
            insertAt (Fin.last n)
              ((Vector.ofFn fun i : Fin n => i).map Fin.castSucc) (Fin.last n) := by
        ext k hk
        by_cases hlast : k = n
        · subst k
          simp [insertAt, List.getElem_insertIdx_self]
        · have hklt : k < n := by omega
          simp [insertAt, List.getElem_insertIdx_of_lt, hklt]
      rw [hvec, detSign_insertAt_last]
      exact ih

/-- Product reindexing for a permutation that fixes the final column. The
Leibniz product splits into the product on the leading prefix times the final
row/column entry. -/
theorem detProduct_insertAt_last {R : Type u} [Lean.Grind.Ring R] {n : Nat}
    (M : Matrix R (n + 1) (n + 1)) (v : Vector (Fin n) n) :
    detProduct M (insertAt (Fin.last n) (v.map Fin.castSucc) (Fin.last n)) =
      detProduct (leadingPrefix M n (Nat.le_succ n)) v * M[Fin.last n][Fin.last n] := by
  unfold detProduct
  rw [← Fin.foldl_eq_foldl_finRange, ← Fin.foldl_eq_foldl_finRange]
  rw [Fin.foldl_succ_last]
  have hfold :
      Fin.foldl n
          (fun acc i =>
            acc *
              M[i.castSucc][
                (insertAt (Fin.last n) (v.map Fin.castSucc) (Fin.last n))[i.castSucc]]) 1 =
        Fin.foldl n
          (fun acc i => acc * (leadingPrefix M n (Nat.le_succ n))[i][v[i]]) 1 := by
    congr
    funext acc i
    have hget :
        (insertAt (Fin.last n) (v.map Fin.castSucc) (Fin.last n))[i.castSucc] =
          (v[i]).castSucc := by
      simpa using insertAt_last_get_castSucc (Fin.last n) (v.map Fin.castSucc) i
    simp [leadingPrefix, ofFn, hget]
  have hlast :
      (insertAt (Fin.last n) (v.map Fin.castSucc) (Fin.last n))[Fin.last n] =
        Fin.last n := by
    exact insertAt_get_self (Fin.last n) (v.map Fin.castSucc) (Fin.last n)
  rw [hfold]
  simp [hlast]

/-- Leibniz-term reindexing for a permutation that fixes the final column. This
packages the sign and product split used by last-row/last-column expansions. -/
theorem detTerm_insertAt_last {R : Type u} [Lean.Grind.Ring R] {n : Nat}
    (M : Matrix R (n + 1) (n + 1)) (v : Vector (Fin n) n) :
    detTerm M (insertAt (Fin.last n) (v.map Fin.castSucc) (Fin.last n)) =
      detSign (R := R) v *
        (detProduct (leadingPrefix M n (Nat.le_succ n)) v * M[Fin.last n][Fin.last n]) := by
  unfold detTerm
  rw [detSign_insertAt_last, detProduct_insertAt_last]

/-- Insertion-position generalization of `detSign_insertAt_last`/`detSign_insertAt_prefix`:
inserting `Fin.last n` at any position `i` adds `n - i.val` inversions. -/
private theorem detSign_insertAt_general {R : Type u} [Lean.Grind.Ring R] {n : Nat}
    (v : Vector (Fin n) n) (i : Fin (n + 1)) :
    detSign (R := R) (insertAt (Fin.last n) (v.map Fin.castSucc) i) =
      (-1 : R) ^ (n - i.val) * detSign (R := R) v := by
  apply detSign_of_inversionCount_add
  rw [insertAt_toList, vector_toList_map]
  have hlen : i.val ≤ v.toList.length := by
    rw [Vector.length_toList]; exact Nat.le_of_lt_succ i.isLt
  simpa [Vector.length_toList] using
    inversionCount_insertIdx_castSucc_last_eq v.toList i.val hlen

/-- The cofactor sign for the last column equals `(-1)^(n - i.val)`. -/
private theorem cofactorSign_last_eq_pow {R : Type u} [Lean.Grind.Ring R] {n : Nat}
    (i : Fin (n + 1)) :
    cofactorSign (R := R) i (Fin.last n) = (-1 : R) ^ (n - i.val) := by
  unfold cofactorSign
  simp only [Fin.val_last]
  have hle : i.val ≤ n := Nat.le_of_lt_succ i.isLt
  have h := detSignParity_add (R := R) (2 * i.val) (n - i.val)
  have heven : (2 * i.val) % 2 = 0 := by omega
  rw [if_pos heven] at h
  have hsum : 2 * i.val + (n - i.val) = i.val + n := by omega
  rw [hsum] at h
  -- h : (if (i.val + n) % 2 = 0 then 1 else -1) = (-1) ^ (n - i.val) * 1
  calc (if (i.val + n) % 2 = 0 then (1 : R) else -1)
      = (-1 : R) ^ (n - i.val) * 1 := h
    _ = (-1 : R) ^ (n - i.val) := by grind

/-- Reading `insertAt x v i` at `skipIndex i r'` recovers `v[r']`: the inserted
element occupies position `i`, leaving the other positions in bijection with the
original via `skipIndex i`. -/
private theorem insertAt_get_skipIndex {α : Type u} {n : Nat}
    (x : α) (v : Vector α n) (i : Fin (n + 1)) (r' : Fin n) :
    (insertAt x v i)[skipIndex i r'] = v[r'] := by
  unfold insertAt
  by_cases hlt : r'.val < i.val
  · simp [List.getElem_insertIdx_of_lt, hlt]
  · have hge : i.val ≤ r'.val := by omega
    have hgt : i.val < r'.val + 1 := by omega
    simp [List.getElem_insertIdx_of_gt, hlt, hgt]

/-- `List.finRange (n + 1)` decomposes as the `Fin n` enumeration mapped through
`skipIndex i` with `i` inserted at position `i.val`. -/
private theorem list_finRange_succ_eq {n : Nat} (i : Fin (n + 1)) :
    List.finRange (n + 1) =
      ((List.finRange n).map (skipIndex i)).insertIdx i.val i := by
  have hilen : i.val ≤ ((List.finRange n).map (skipIndex i)).length := by
    simp [List.length_finRange]; exact Nat.le_of_lt_succ i.isLt
  apply List.ext_getElem
  · rw [List.length_finRange, List.length_insertIdx_of_le_length hilen,
        List.length_map, List.length_finRange]
  · intro k hk hk'
    rw [List.getElem_finRange]
    by_cases hki : k < i.val
    · rw [List.getElem_insertIdx_of_lt hki]
      have hkn : k < n := by
        have : k < ((List.finRange n).map (skipIndex i)).length := by
          simp [List.length_finRange]; omega
        simpa [List.length_map, List.length_finRange] using this
      rw [List.getElem_map, List.getElem_finRange]
      apply Fin.ext
      simp [skipIndex_val_of_lt, hki]
    · by_cases hkeq : k = i.val
      · subst hkeq
        rw [List.getElem_insertIdx_self]
        apply Fin.ext; rfl
      · have hkgt : i.val < k := by omega
        rw [List.getElem_insertIdx_of_gt hkgt]
        have hk1n : k - 1 < n := by
          have hklt : k < n + 1 := by simp [List.length_finRange] at hk; exact hk
          omega
        rw [List.getElem_map, List.getElem_finRange]
        apply Fin.ext
        have hgt' : ¬ (k - 1 < i.val) := by omega
        simp [skipIndex_val_of_not_lt, hgt']
        omega

/-- `List.finRange (n + 1)` is a permutation of `i :: ((List.finRange n).map (skipIndex i))`. -/
private theorem list_finRange_succ_perm_skipIndex {n : Nat} (i : Fin (n + 1)) :
    (List.finRange (n + 1)).Perm (i :: (List.finRange n).map (skipIndex i)) := by
  rw [list_finRange_succ_eq i]
  have hilen : i.val ≤ ((List.finRange n).map (skipIndex i)).length := by
    simp [List.length_finRange]; exact Nat.le_of_lt_succ i.isLt
  exact List.perm_insertIdx i ((List.finRange n).map (skipIndex i)) hilen

/-- Factorize a multiplicative `foldl` over `List.finRange (n + 1)` at index `i`,
yielding `f i` times the foldl over `List.finRange n` reindexed via `skipIndex i`. -/
private theorem foldl_finRange_succ_factor_skipIndex {R : Type u} [Lean.Grind.CommRing R]
    {n : Nat} (i : Fin (n + 1)) (f : Fin (n + 1) → R) :
    (List.finRange (n + 1)).foldl (fun acc r => acc * f r) 1 =
      f i * (List.finRange n).foldl (fun acc r' => acc * f (skipIndex i r')) 1 := by
  rw [foldl_det_product_perm f (list_finRange_succ_perm_skipIndex i) 1]
  show (i :: (List.finRange n).map (skipIndex i)).foldl (fun acc r => acc * f r) 1 = _
  simp only [List.foldl_cons]
  rw [show (1 : R) * f i = f i * 1 from by grind]
  rw [foldl_det_product_mul_left ((List.finRange n).map (skipIndex i)) (f i) f 1]
  rw [List.foldl_map]

/-- Permutation-product equation generalizing `detProduct_insertAt_last` to any
insertion position: factor the Leibniz product into the `(i, last)` entry times
the product over the `deleteRowCol` minor. -/
private theorem detProduct_insertAt_general {R : Type u} [Lean.Grind.CommRing R] {n : Nat}
    (M : Matrix R (n + 1) (n + 1)) (v : Vector (Fin n) n) (i : Fin (n + 1)) :
    detProduct M (insertAt (Fin.last n) (v.map Fin.castSucc) i) =
      M[i][Fin.last n] * detProduct (deleteRowCol M i (Fin.last n)) v := by
  unfold detProduct
  rw [foldl_finRange_succ_factor_skipIndex i
    (fun r => M[r][(insertAt (Fin.last n) (v.map Fin.castSucc) i)[r]])]
  congr 1
  · -- M[i][(insertAt ... i)[i]] = M[i][Fin.last n]
    congr 1
    exact insertAt_get_self _ _ _
  · apply foldl_det_product_congr
    intro r' _hmem
    -- Identify the column index of each side with `(v[r']).castSucc`.
    have hLHS_col :
        (insertAt (Fin.last n) (v.map Fin.castSucc) i)[skipIndex i r'] =
          (v[r']).castSucc := by
      rw [insertAt_get_skipIndex]
      simp [Vector.getElem_map]
    have hRHS_col :
        skipIndex (Fin.last n) v[r'] = (v[r']).castSucc := skipIndex_last v[r']
    simp only [deleteRowCol_entry, hLHS_col, hRHS_col]

/-- Leibniz-term equation for an arbitrary insertion position. -/
private theorem detTerm_insertAt_general {R : Type u} [Lean.Grind.CommRing R] {n : Nat}
    (M : Matrix R (n + 1) (n + 1)) (v : Vector (Fin n) n) (i : Fin (n + 1)) :
    detTerm M (insertAt (Fin.last n) (v.map Fin.castSucc) i) =
      cofactorSign (R := R) i (Fin.last n) *
        (M[i][Fin.last n] * detTerm (deleteRowCol M i (Fin.last n)) v) := by
  unfold detTerm
  rw [detSign_insertAt_general, detProduct_insertAt_general]
  rw [cofactorSign_last_eq_pow]
  grind

private theorem detProduct_insertAt_not_last_zero
    {R : Type u} [Lean.Grind.CommRing R] {n : Nat}
    (M : Matrix R (n + 1) (n + 1)) (v : Vector (Fin n) n)
    (i : Fin (n + 1)) (hi : i ≠ Fin.last n)
    (hrow : ∀ j : Fin (n + 1), j.val < n → M[Fin.last n][j] = 0) :
    detProduct M (insertAt (Fin.last n) (v.map Fin.castSucc) i) = 0 := by
  unfold detProduct
  apply foldl_det_product_zero_of_mem
    (List.finRange (n + 1)) (Fin.last n)
    (fun r => M[r][(insertAt (Fin.last n) (v.map Fin.castSucc) i)[r]]) 1
    (List.mem_finRange (Fin.last n))
  have hiVal : i.val < n := by
    have hne : i.val ≠ n := by
      intro hval
      exact hi (Fin.ext hval)
    omega
  have hcolVal :
      ((insertAt (Fin.last n) (v.map Fin.castSucc) i)[Fin.last n]).val < n := by
    unfold insertAt
    simp [List.getElem_insertIdx_of_gt, hiVal, Vector.toList]
  exact hrow ((insertAt (Fin.last n) (v.map Fin.castSucc) i)[Fin.last n]) hcolVal

private theorem detTerm_insertAt_not_last_zero
    {R : Type u} [Lean.Grind.CommRing R] {n : Nat}
    (M : Matrix R (n + 1) (n + 1)) (v : Vector (Fin n) n)
    (i : Fin (n + 1)) (hi : i ≠ Fin.last n)
    (hrow : ∀ j : Fin (n + 1), j.val < n → M[Fin.last n][j] = 0) :
    detTerm M (insertAt (Fin.last n) (v.map Fin.castSucc) i) = 0 := by
  unfold detTerm
  rw [detProduct_insertAt_not_last_zero M v i hi hrow]
  grind

private theorem foldl_detTerm_last_row_insertions
    {R : Type u} [Lean.Grind.CommRing R] {n : Nat}
    (M : Matrix R (n + 1) (n + 1)) (v : Vector (Fin n) n) (z : R)
    (hrow : ∀ j : Fin (n + 1), j.val < n → M[Fin.last n][j] = 0) :
    (List.finRange (n + 1)).foldl
        (fun acc i =>
          acc + detTerm M (insertAt (Fin.last n) (v.map Fin.castSucc) i)) z =
      z + detSign (R := R) v *
        (detProduct (leadingPrefix M n (Nat.le_succ n)) v * M[Fin.last n][Fin.last n]) := by
  rw [← Fin.foldl_eq_foldl_finRange]
  rw [Fin.foldl_succ_last]
  have hprefix :
      Fin.foldl n
          (fun acc i =>
            acc + detTerm M
              (insertAt (Fin.last n) (v.map Fin.castSucc) i.castSucc)) z = z := by
    rw [Fin.foldl_eq_foldl_finRange]
    calc
      (List.finRange n).foldl
          (fun acc i =>
            acc + detTerm M
              (insertAt (Fin.last n) (v.map Fin.castSucc) i.castSucc)) z =
        (List.finRange n).foldl (fun acc (_i : Fin n) => acc + (0 : R)) z := by
          apply foldl_det_sum_congr
          intro i _hmem
          rw [detTerm_insertAt_not_last_zero M v i.castSucc
            (by
              intro hlast
              have hval := congrArg Fin.val hlast
              simp at hval
              exact (Nat.ne_of_lt i.isLt) hval)
            hrow]
      _ = z := by
          exact foldl_det_sum_zero (List.finRange n) z
  rw [hprefix]
  rw [detTerm_insertAt_last]

/-- If the last row is zero before the diagonal entry, the determinant
factors as the leading principal determinant times the bottom-right entry.
This is the triangular-recursion step used by positivity and diagonal-product
lemmas. -/
theorem det_eq_det_leadingPrefix_mul_last_of_last_row_zero
    {R : Type u} [Lean.Grind.CommRing R] {n : Nat}
    (M : Matrix R (n + 1) (n + 1))
    (hrow : ∀ j : Fin (n + 1), j.val < n → M[Fin.last n][j] = 0) :
    det M = det (leadingPrefix M n (Nat.le_succ n)) * M[Fin.last n][Fin.last n] := by
  unfold det
  rw [show permutationVectors (n + 1) =
      List.flatMap
        (fun v =>
          (List.finRange (n + 1)).map fun i =>
            insertAt (Fin.last n) (v.map Fin.castSucc) i)
        (permutationVectors n) by rfl]
  rw [foldl_det_sum_flatMap]
  calc
    (permutationVectors n).foldl
        (fun acc v =>
          (List.map (fun i => insertAt (Fin.last n) (Vector.map Fin.castSucc v) i)
              (List.finRange (n + 1))).foldl
            (fun acc perm => acc + detTerm M perm) acc) 0 =
      (permutationVectors n).foldl
        (fun acc v =>
          (List.finRange (n + 1)).foldl
            (fun acc i =>
              acc + detTerm M (insertAt (Fin.last n) (v.map Fin.castSucc) i)) acc) 0 := by
        apply foldl_acc_congr
        intro acc v _hmem
        simp only [List.foldl_map]
    _ =
      (permutationVectors n).foldl
        (fun acc v =>
          acc + detSign (R := R) v *
            (detProduct (leadingPrefix M n (Nat.le_succ n)) v *
              M[Fin.last n][Fin.last n])) 0 := by
        apply foldl_acc_congr
        intro acc v _hmem
        exact foldl_detTerm_last_row_insertions M v acc hrow
    _ =
      (permutationVectors n).foldl
          (fun acc v => acc + detTerm (leadingPrefix M n (Nat.le_succ n)) v) 0 *
        M[Fin.last n][Fin.last n] := by
        unfold detTerm
        calc
          (permutationVectors n).foldl
              (fun acc v =>
                acc + detSign (R := R) v *
                  (detProduct (leadingPrefix M n (Nat.le_succ n)) v *
                    M[Fin.last n][Fin.last n])) 0 =
            (permutationVectors n).foldl
              (fun acc v =>
                acc + (detSign (R := R) v *
                  detProduct (leadingPrefix M n (Nat.le_succ n)) v) *
                    M[Fin.last n][Fin.last n]) 0 := by
              apply foldl_det_sum_congr
              intro v _hmem
              grind
          _ =
            (permutationVectors n).foldl
                (fun acc v =>
                  acc + detSign (R := R) v *
                    detProduct (leadingPrefix M n (Nat.le_succ n)) v) 0 *
              M[Fin.last n][Fin.last n] := by
              exact foldl_det_sum_mul_right_zero
                (permutationVectors n)
                (fun v => detSign (R := R) v *
                  detProduct (leadingPrefix M n (Nat.le_succ n)) v)
                M[Fin.last n][Fin.last n]
    _ = det (leadingPrefix M n (Nat.le_succ n)) * M[Fin.last n][Fin.last n] := by
        rfl

/-- An integer upper-triangular matrix with strictly positive diagonal has
strictly positive determinant. -/
theorem det_upperTriangular_pos_diag
    {n : Nat} (M : Matrix Int n n)
    (hzero : ∀ i j : Fin n, j.val < i.val → M[i][j] = 0)
    (hdiag : ∀ i : Fin n, 0 < M[i][i]) :
    0 < det M := by
  induction n with
  | zero =>
      simp [det, permutationVectors, detTerm, detSign, detProduct, inversionCount]
  | succ n ih =>
      have hrow : ∀ j : Fin (n + 1), j.val < n → M[Fin.last n][j] = 0 := by
        intro j hj
        exact hzero (Fin.last n) j hj
      rw [det_eq_det_leadingPrefix_mul_last_of_last_row_zero M hrow]
      have hprefixZero :
          ∀ i j : Fin n, j.val < i.val →
            (leadingPrefix M n (Nat.le_succ n))[i][j] = 0 := by
        intro i j hij
        let ii : Fin (n + 1) := ⟨i.val, by omega⟩
        let jj : Fin (n + 1) := ⟨j.val, by omega⟩
        have hentry : (leadingPrefix M n (Nat.le_succ n))[i][j] = M[ii][jj] := by
          simp [leadingPrefix, ofFn, ii, jj]
        rw [hentry]
        exact hzero ii jj hij
      have hprefixDiag :
          ∀ i : Fin n, 0 < (leadingPrefix M n (Nat.le_succ n))[i][i] := by
        intro i
        let ii : Fin (n + 1) := ⟨i.val, by omega⟩
        have hentry : (leadingPrefix M n (Nat.le_succ n))[i][i] = M[ii][ii] := by
          simp [leadingPrefix, ofFn, ii]
        rw [hentry]
        exact hdiag ii
      exact Int.mul_pos (ih (leadingPrefix M n (Nat.le_succ n)) hprefixZero hprefixDiag)
        (hdiag (Fin.last n))

/-- The determinant of an upper-triangular square matrix (entries below the
diagonal are zero) over a commutative ring is the product of its diagonal
entries, expressed via a `Fin.foldl` over the diagonal indices. -/
theorem det_upperTriangular_eq_finFoldl_diag
    {R : Type u} [Lean.Grind.CommRing R] {n : Nat} (M : Matrix R n n)
    (hzero : ∀ i j : Fin n, j.val < i.val → M[i][j] = 0) :
    det M = Fin.foldl n (fun acc i => acc * M[i][i]) 1 := by
  induction n with
  | zero =>
      simp only [Fin.foldl_zero]
      simp [det, permutationVectors, detTerm, detSign, detProduct,
        inversionCount]
      grind
  | succ n ih =>
      have hrow : ∀ j : Fin (n + 1), j.val < n → M[Fin.last n][j] = 0 := by
        intro j hj
        exact hzero (Fin.last n) j hj
      rw [det_eq_det_leadingPrefix_mul_last_of_last_row_zero M hrow]
      have hprefixZero :
          ∀ i j : Fin n, j.val < i.val →
            (leadingPrefix M n (Nat.le_succ n))[i][j] = 0 := by
        intro i j hij
        let ii : Fin (n + 1) := ⟨i.val, by omega⟩
        let jj : Fin (n + 1) := ⟨j.val, by omega⟩
        have hentry : (leadingPrefix M n (Nat.le_succ n))[i][j] = M[ii][jj] := by
          simp [leadingPrefix, ofFn, ii, jj]
        rw [hentry]
        exact hzero ii jj hij
      rw [ih (leadingPrefix M n (Nat.le_succ n)) hprefixZero]
      -- The (n+1)-length Fin.foldl over diagonals splits as the n-length foldl
      -- times the last diagonal entry.
      rw [Fin.foldl_succ_last]
      -- Rewrite the leading prefix diagonal entries as M[i.castSucc][i.castSucc].
      have hcongr :
          Fin.foldl n
              (fun acc i => acc * (leadingPrefix M n (Nat.le_succ n))[i][i]) 1 =
            Fin.foldl n (fun acc i => acc * M[i.castSucc][i.castSucc]) 1 := by
        rw [Fin.foldl_eq_foldl_finRange, Fin.foldl_eq_foldl_finRange]
        apply foldl_acc_congr
        intro acc i _hmem
        have hentry : (leadingPrefix M n (Nat.le_succ n))[i][i] = M[i.castSucc][i.castSucc] :=
          by simp [leadingPrefix, ofFn, Fin.castSucc]
        rw [hentry]
      rw [hcongr]

/-- The determinant of an upper-triangular square matrix as a `List.foldl`
product over the diagonal indices in `Fin.finRange`. -/
theorem det_upperTriangular_eq_foldl_diag
    {R : Type u} [Lean.Grind.CommRing R] {n : Nat} (M : Matrix R n n)
    (hzero : ∀ i j : Fin n, j.val < i.val → M[i][j] = 0) :
    det M = (List.finRange n).foldl (fun acc i => acc * M[i][i]) 1 := by
  rw [det_upperTriangular_eq_finFoldl_diag M hzero]
  rw [Fin.foldl_eq_foldl_finRange]

private theorem detTerm_identity_insertAt_last {R : Type u}
    [Lean.Grind.CommRing R] {n : Nat} (v : Vector (Fin n) n) :
    detTerm (1 : Matrix R (n + 1) (n + 1))
      (insertAt (Fin.last n) (v.map Fin.castSucc) (Fin.last n)) =
    detTerm (1 : Matrix R n n) v := by
  unfold detTerm
  rw [detSign_insertAt_last, detProduct_identity_insertAt_last]

private theorem foldl_detTerm_identity_insertions {R : Type u}
    [Lean.Grind.CommRing R] {n : Nat} (v : Vector (Fin n) n) (z : R) :
    (List.finRange (n + 1)).foldl
        (fun acc i =>
          acc + detTerm (1 : Matrix R (n + 1) (n + 1))
            (insertAt (Fin.last n) (v.map Fin.castSucc) i)) z =
      z + detTerm (1 : Matrix R n n) v := by
  rw [← Fin.foldl_eq_foldl_finRange]
  rw [Fin.foldl_succ_last]
  have hprefix :
      Fin.foldl n
          (fun acc i =>
            acc + detTerm (1 : Matrix R (n + 1) (n + 1))
              (insertAt (Fin.last n) (v.map Fin.castSucc) i.castSucc)) z = z := by
    rw [Fin.foldl_eq_foldl_finRange]
    calc
      (List.finRange n).foldl
          (fun acc i =>
            acc + detTerm (1 : Matrix R (n + 1) (n + 1))
              (insertAt (Fin.last n) (v.map Fin.castSucc) i.castSucc)) z =
        (List.finRange n).foldl (fun acc (_i : Fin n) => acc + (0 : R)) z := by
          apply foldl_det_sum_congr
          intro i _hmem
          unfold detTerm
          rw [detProduct_identity_insertAt_not_last_zero (R := R) v i.castSucc (by
            intro hlast
            have hval := congrArg Fin.val hlast
            simp at hval
            exact (Nat.ne_of_lt i.isLt) hval)]
          grind
      _ = z := by
          exact foldl_det_sum_zero (List.finRange n) z
  rw [hprefix]
  rw [detTerm_identity_insertAt_last]

private theorem rowScale_get {R : Type u} [Mul R] {n m : Nat}
    (M : Matrix R n m) (i r : Fin n) (c : R) (k : Fin m) :
    (rowScale M i c)[r][k] = if r = i then c * M[i][k] else M[r][k] := by
  by_cases h : r = i
  · subst r
    simp [rowScale]
  · simp [rowScale, h]
    have hval : i.val ≠ r.val := by
      intro hval
      exact h (Fin.ext hval.symm)
    have hrow :
        (M.set i (Vector.ofFn fun k => c * M[i][k]))[r] = M[r] := by
      exact
        (Vector.getElem_set_ne (xs := M) (x := Vector.ofFn fun k => c * M[i][k])
          i.isLt r.isLt hval)
    simpa [rowScale] using congrArg (fun row => row[k]) hrow

private theorem detProduct_rowScale {R : Type u} [Lean.Grind.CommRing R] {n : Nat}
    (M : Matrix R n n) (i : Fin n) (c : R) (perm : Vector (Fin n) n) :
    detProduct (rowScale M i c) perm = c * detProduct M perm := by
  unfold detProduct
  calc
    (List.finRange n).foldl
        (fun acc r => acc * (rowScale M i c)[r][perm[r]]) 1 =
      (List.finRange n).foldl
        (fun acc r => acc * if r = i then c * M[r][perm[r]] else M[r][perm[r]]) 1 := by
        apply foldl_det_product_congr
        intro r _hmem
        by_cases h : r = i
        · subst r
          simpa using (rowScale_get M i i c perm[i])
        · simpa [h] using (rowScale_get M i r c perm[r])
    _ = c * (List.finRange n).foldl (fun acc r => acc * M[r][perm[r]]) 1 := by
        exact foldl_det_product_single_scale
          (List.finRange n) i c (fun r => M[r][perm[r]]) 1
          (List.mem_finRange i) (List.nodup_finRange n)


end Matrix
end Hex
