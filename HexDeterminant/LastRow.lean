/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexDeterminant.Minor
import all HexDeterminant.Minor
import all HexDeterminant.Leibniz
import all HexDeterminant.Enumeration

public section

/-!
The last-row determinant recursion.

This module derives how the Leibniz determinant recurses on the final row and
column. Inserting `Fin.last n` at the end of a permutation vector splits the
sign and the product (`detSign_insertAt_last`, `detProduct_insertAt_last`,
`detTerm_insertAt_last`), and the general insertion position is handled by
`detSign_insertAt_general` / `detTerm_insertAt_general`. The payoff is the
last-row factorisation `det_eq_principalSubmatrix_mul_last`: when the final row
vanishes off the diagonal, the determinant is the determinant of the leading
principal submatrix times the corner entry. Laplace expansion and the triangular
diagonal-product formulas (`HexDeterminant.Triangular`) build on it. The
enumeration combinatorics this recursion rides on (`permutationVectors`
completeness and duplicate-freeness, `raiseFinAbove` / `peelLastVector`) live in
`HexDeterminant.Enumeration`.
-/

namespace Hex
universe u
namespace Matrix
variable {α : Type u}

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
      rw [Nat.add_succ, Lean.Grind.Semiring.pow_succ]
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
      detProduct (principalSubmatrix M n (Nat.le_succ n)) v * M[Fin.last n][Fin.last n] := by
  unfold detProduct
  simp only [getElem_pair_eq_nested]
  rw [← Fin.foldl_eq_finRange_foldl, ← Fin.foldl_eq_finRange_foldl, Fin.foldl_succ_last]
  have hfold :
      Fin.foldl n
          (fun acc i =>
            acc *
              M[i.castSucc][
                (insertAt (Fin.last n) (v.map Fin.castSucc) (Fin.last n))[i.castSucc]]) 1 =
        Fin.foldl n
          (fun acc i => acc * (principalSubmatrix M n (Nat.le_succ n))[i][v[i]]) 1 := by
    congr
    funext acc i
    have hget :
        (insertAt (Fin.last n) (v.map Fin.castSucc) (Fin.last n))[i.castSucc] =
          (v[i]).castSucc := by
      simpa using insertAt_last_get_castSucc (Fin.last n) (v.map Fin.castSucc) i
    simp [principalSubmatrix, ofFn, hget, getRow, Fin.getElem_fin]
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
        (detProduct (principalSubmatrix M n (Nat.le_succ n)) v * M[Fin.last n][Fin.last n]) := by
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
  rw [List.foldl_mul_perm f (list_finRange_succ_perm_skipIndex i) 1]
  show (i :: (List.finRange n).map (skipIndex i)).foldl (fun acc r => acc * f r) 1 = _
  simp only [List.foldl_cons]
  rw [show (1 : R) * f i = f i * 1 from by grind,
    foldl_det_product_mul_left ((List.finRange n).map (skipIndex i)) (f i) f 1, List.foldl_map]

/-- Permutation-product equation generalizing `detProduct_insertAt_last` to any
insertion position: factor the Leibniz product into the `(i, last)` entry times
the product over the `deleteRowCol` minor. -/
private theorem detProduct_insertAt_general {R : Type u} [Lean.Grind.CommRing R] {n : Nat}
    (M : Matrix R (n + 1) (n + 1)) (v : Vector (Fin n) n) (i : Fin (n + 1)) :
    detProduct M (insertAt (Fin.last n) (v.map Fin.castSucc) i) =
      M[i][Fin.last n] * detProduct (deleteRowCol M i (Fin.last n)) v := by
  unfold detProduct
  simp only [getElem_pair_eq_nested]
  rw [foldl_finRange_succ_factor_skipIndex i
    (fun r => M[r][(insertAt (Fin.last n) (v.map Fin.castSucc) i)[r]])]
  congr 1
  · -- M[i][(insertAt ... i)[i]] = M[i][Fin.last n]
    congr 1
    exact insertAt_get_self _ _ _
  · apply List.foldl_mul_congr
    intro r' _hmem
    -- Identify the column index of each side with `(v[r']).castSucc`.
    have hLHS_col :
        (insertAt (Fin.last n) (v.map Fin.castSucc) i)[skipIndex i r'] =
          (v[r']).castSucc := by
      rw [insertAt_get_skipIndex]
      simp [Vector.getElem_map]
    have hRHS_col :
        skipIndex (Fin.last n) v[r'] = (v[r']).castSucc := skipIndex_last v[r']
    simp only [getElem_deleteRowCol, hLHS_col, hRHS_col]

/-- Leibniz-term equation for an arbitrary insertion position. -/
private theorem detTerm_insertAt_general {R : Type u} [Lean.Grind.CommRing R] {n : Nat}
    (M : Matrix R (n + 1) (n + 1)) (v : Vector (Fin n) n) (i : Fin (n + 1)) :
    detTerm M (insertAt (Fin.last n) (v.map Fin.castSucc) i) =
      cofactorSign (R := R) i (Fin.last n) *
        (M[i][Fin.last n] * detTerm (deleteRowCol M i (Fin.last n)) v) := by
  unfold detTerm
  rw [detSign_insertAt_general, detProduct_insertAt_general, cofactorSign_last_eq_pow]
  grind

private theorem detProduct_insertAt_not_last_zero
    {R : Type u} [Lean.Grind.CommRing R] {n : Nat}
    (M : Matrix R (n + 1) (n + 1)) (v : Vector (Fin n) n)
    (i : Fin (n + 1)) (hi : i ≠ Fin.last n)
    (hrow : ∀ j : Fin (n + 1), j.val < n → M[Fin.last n][j] = 0) :
    detProduct M (insertAt (Fin.last n) (v.map Fin.castSucc) i) = 0 := by
  unfold detProduct
  simp only [getElem_pair_eq_nested]
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
        (detProduct (principalSubmatrix M n (Nat.le_succ n)) v * M[Fin.last n][Fin.last n]) := by
  rw [← Fin.foldl_eq_finRange_foldl, Fin.foldl_succ_last]
  have hprefix :
      Fin.foldl n
          (fun acc i =>
            acc + detTerm M
              (insertAt (Fin.last n) (v.map Fin.castSucc) i.castSucc)) z = z := by
    rw [Fin.foldl_eq_finRange_foldl]
    calc
      (List.finRange n).foldl
          (fun acc i =>
            acc + detTerm M
              (insertAt (Fin.last n) (v.map Fin.castSucc) i.castSucc)) z =
        (List.finRange n).foldl (fun acc (_i : Fin n) => acc + (0 : R)) z := by
          apply List.foldl_add_congr
          intro i _hmem
          rw [detTerm_insertAt_not_last_zero M v i.castSucc
            (by
              intro hlast
              have hval := congrArg Fin.val hlast
              simp at hval
              exact (Nat.ne_of_lt i.isLt) hval)
            hrow]
      _ = z := by
          exact List.foldl_add_zero (List.finRange n) z
  rw [hprefix, detTerm_insertAt_last]

/-- If the last row is zero before the diagonal entry, the determinant
factors as the leading principal determinant times the bottom-right entry.
This is the triangular-recursion step used by positivity and diagonal-product
lemmas. -/
theorem det_eq_principalSubmatrix_mul_last
    {R : Type u} [Lean.Grind.CommRing R] {n : Nat}
    (M : Matrix R (n + 1) (n + 1))
    (hrow : ∀ j : Fin (n + 1), j.val < n → M[Fin.last n][j] = 0) :
    det M = det (principalSubmatrix M n (Nat.le_succ n)) * M[Fin.last n][Fin.last n] := by
  unfold det
  rw [show permutationVectors (n + 1) =
      List.flatMap
        (fun v =>
          (List.finRange (n + 1)).map fun i =>
            insertAt (Fin.last n) (v.map Fin.castSucc) i)
        (permutationVectors n) by rfl]
  rw [List.foldl_add_flatMap]
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
        apply List.foldl_congr
        intro acc v _hmem
        simp only [List.foldl_map]
    _ =
      (permutationVectors n).foldl
        (fun acc v =>
          acc + detSign (R := R) v *
            (detProduct (principalSubmatrix M n (Nat.le_succ n)) v *
              M[Fin.last n][Fin.last n])) 0 := by
        apply List.foldl_congr
        intro acc v _hmem
        exact foldl_detTerm_last_row_insertions M v acc hrow
    _ =
      (permutationVectors n).foldl
          (fun acc v => acc + detTerm (principalSubmatrix M n (Nat.le_succ n)) v) 0 *
        M[Fin.last n][Fin.last n] := by
        unfold detTerm
        calc
          (permutationVectors n).foldl
              (fun acc v =>
                acc + detSign (R := R) v *
                  (detProduct (principalSubmatrix M n (Nat.le_succ n)) v *
                    M[Fin.last n][Fin.last n])) 0 =
            (permutationVectors n).foldl
              (fun acc v =>
                acc + (detSign (R := R) v *
                  detProduct (principalSubmatrix M n (Nat.le_succ n)) v) *
                    M[Fin.last n][Fin.last n]) 0 := by
              apply List.foldl_add_congr
              intro v _hmem
              grind
          _ =
            (permutationVectors n).foldl
                (fun acc v =>
                  acc + detSign (R := R) v *
                    detProduct (principalSubmatrix M n (Nat.le_succ n)) v) 0 *
              M[Fin.last n][Fin.last n] := by
              exact List.foldl_add_mul_right_zero
                (permutationVectors n)
                (fun v => detSign (R := R) v *
                  detProduct (principalSubmatrix M n (Nat.le_succ n)) v)
                M[Fin.last n][Fin.last n]
    _ = det (principalSubmatrix M n (Nat.le_succ n)) * M[Fin.last n][Fin.last n] := by
        rfl

end Matrix
end Hex
