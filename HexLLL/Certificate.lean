/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexBasic
public import HexLLL.Lattice

public section

/-!
The packed same-lattice certificate: decide `M * A = C` and hence
`sameLatticeCert` over integer arithmetic by comparing rows packed as
single big integers in balanced base `2 ^ K`, never forming the matrix
product.
-/

namespace Hex

namespace Internal

open Hex.Matrix

/-- Horner evaluation of an integer digit list at base `P`. -/
@[expose]
def packDigits (P : Int) : List Int → Int
  | [] => 0
  | x :: xs => x + P * packDigits P xs

/-- Pack the entries of a row as one integer in balanced base `2^K`. -/
@[expose]
def packRow (K : Nat) (v : Vector Int m) : Int :=
  packDigits ((2 : Int) ^ K) v.toList

/-- Maximum absolute value of the entries of an integer matrix. -/
@[expose]
def maxAbs (M : Matrix Int n m) : Nat :=
  M.rows.toList.foldl
    (fun acc row => Nat.max acc (row.toList.foldl (fun a x => Nat.max a x.natAbs) 0))
    0

/-- Digit width at which every entry of `M * A` and of `C` packs injectively:
`2 · |entry| < 2^K` for all entries, since each is bounded by
`n · maxAbs M · maxAbs A + maxAbs C`. -/
@[expose]
def packWidth (M : Matrix Int n n) (A C : Matrix Int n m) : Nat :=
  (n * maxAbs M * maxAbs A + maxAbs C).log2 + 2

/-- Packed product-equality certificate: decides `M * A = C` without forming
the product. Each row of `A` and of `C` is packed into one integer in
balanced base `2^K` at the width `packWidth M A C`, and row `i` of the
(unformed) product is compared via the single packed dot product
`Σ_l M[i][l] · packA[l]`: `n` big-integer dot products in place of the
`n · m` entry dot products of a materialized `Matrix.mul`.

When the entries are word-scale the multiplications are big-by-small and the
same-lattice clause costs `O(n²)` big-by-small multiplications; on wide
entries the packed dot products cost the same bit operations as the
materialized product. Either way the single packed comparison decides exactly
`M * A = C` (`mulEqCert_iff`). -/
@[expose]
def mulEqCert (M : Matrix Int n n) (A C : Matrix Int n m) : Bool :=
  let K := packWidth M A C
  let packs : Vector Int n := Vector.ofFn fun l => packRow K (row A l)
  (List.finRange n).all fun i =>
    (row M i).dotProduct packs == packRow K (row C i)


/-- Every entry of an integer matrix is bounded by the `maxAbs` scan. -/
theorem natAbs_le_maxAbs (M : Matrix Int n m) (i : Fin n) (j : Fin m) :
    M[i][j].natAbs ≤ maxAbs M := by
  have hrow : M[i] ∈ M.rows.toList := by
    have h : M.rows.toList[i.val]'(by simp) = M[i] := by
      simp [Hex.Matrix.getRow, Fin.getElem_fin]
    rw [← h]
    exact List.getElem_mem _
  have hentry : M[i][j] ∈ M[i].toList := by
    have h : M[i].toList[j.val]'(by simp) = M[i][j] := by simp
    rw [← h]
    exact List.getElem_mem _
  have hinner : M[i][j].natAbs ≤
      M[i].toList.foldl (fun a x => Nat.max a x.natAbs) 0 :=
    List.le_foldl_max_of_mem _ (fun x => x.natAbs) (init := 0) hentry
  have houter :=
    List.le_foldl_max_of_mem
      M.rows.toList
      (fun row : Vector Int m => row.toList.foldl (fun a x => Nat.max a x.natAbs) 0)
      (init := 0) hrow
  exact Nat.le_trans hinner houter

/-- Packing is linear over a coefficient-times-row update. -/
theorem packDigits_zipWith_muladd (P c : Int) (r s : List Int)
    (h : r.length = s.length) :
    packDigits P (List.zipWith (fun a b => c * a + b) r s) =
      c * packDigits P r + packDigits P s := by
  induction r generalizing s with
  | nil =>
      cases s with
      | nil => simp [packDigits]
      | cons y ys => simp at h
  | cons x xs ih =>
      cases s with
      | nil => simp at h
      | cons y ys =>
          simp only [List.zipWith_cons_cons, packDigits]
          rw [ih ys (by simpa using h)]
          grind

/-- Row-level form of `packDigits_zipWith_muladd`. -/
theorem packRow_zipWith_muladd (K : Nat) (c : Int) (r s : Vector Int m) :
    packRow K (Vector.zipWith (fun a b => c * a + b) r s) =
      c * packRow K r + packRow K s := by
  unfold packRow
  rw [Vector.toList_zipWith]
  exact packDigits_zipWith_muladd _ c _ _ (by simp)

/-- `packDigits_replicate_zero` says that packing an all-zero digit list gives
zero, providing the base packed row for folded dot products. -/
private theorem packDigits_replicate_zero (P : Int) (m : Nat) :
    packDigits P (List.replicate m 0) = 0 := by
  induction m with
  | zero => rfl
  | succ m ih => simp [List.replicate_succ, packDigits, ih]

/-- `packRow_replicate_zero` lifts zero-list packing to rows, supplying the
zero packed row used to start product row folds. -/
private theorem packRow_replicate_zero (K m : Nat) :
    packRow K (Vector.replicate m (0 : Int)) = 0 := by
  unfold packRow
  rw [Vector.toList_replicate]
  exact packDigits_replicate_zero _ m

/-- `foldl_dot_pack` commutes a folded dot product with packing the folded
coefficient-times-row update. -/
private theorem foldl_dot_pack (K : Nat) (c : Vector Int n) (A : Matrix Int n m)
    (ls : List (Fin n)) (w : Vector Int m) :
    ls.foldl (fun acc l => acc + c[l] * packRow K (row A l)) (packRow K w) =
      packRow K (ls.foldl
        (fun w l => Vector.zipWith (fun a b => c[l] * a + b) (row A l) w) w) := by
  induction ls generalizing w with
  | nil => rfl
  | cons l ls ih =>
      simp only [List.foldl_cons]
      rw [← ih (Vector.zipWith (fun a b => c[l] * a + b) (row A l) w),
        packRow_zipWith_muladd]
      grind

/-- `foldl_zipWith_getElem` identifies each entry of a folded `zipWith` row
update with the matching folded scalar dot update. -/
private theorem foldl_zipWith_getElem (c : Vector Int n) (A : Matrix Int n m)
    (ls : List (Fin n)) (w : Vector Int m) (j : Fin m) :
    (ls.foldl
        (fun w l => Vector.zipWith (fun a b => c[l] * a + b) (row A l) w) w)[j] =
      ls.foldl (fun acc l => acc + c[l] * A[l][j]) w[j] := by
  induction ls generalizing w with
  | nil => rfl
  | cons l ls ih =>
      simp only [List.foldl_cons]
      rw [ih]
      have hentry : (Vector.zipWith (fun a b => c[l] * a + b) (row A l) w)[j] =
          w[j] + c[l] * A[l][j] := by
        simp only [row]
        grind
      rw [hentry]

/-- The packed dot product evaluates to the pack of the corresponding row of
the (unformed) product `M * A`. -/
theorem dotProduct_packRow (K : Nat) (M : Matrix Int n n) (A : Matrix Int n m)
    (i : Fin n) :
    (row M i).dotProduct (Vector.ofFn fun l => packRow K (row A l)) =
      packRow K (row (M * A) i) := by
  have hstart :
      (row M i).dotProduct (Vector.ofFn fun l => packRow K (row A l)) =
        (List.finRange n).foldl
          (fun acc l => acc + (row M i)[l] * packRow K (row A l))
          (packRow K (Vector.replicate m (0 : Int))) := by
    rw [packRow_replicate_zero]
    unfold Vector.dotProduct
    simp only [Fin.getElem_fin, Vector.getElem_ofFn]
  rw [hstart, foldl_dot_pack]
  congr 1
  apply Vector.ext
  intro j hj
  have hentry := foldl_zipWith_getElem (row M i) A (List.finRange n)
    (Vector.replicate m (0 : Int)) ⟨j, hj⟩
  have htarget : (row (M * A) i)[(⟨j, hj⟩ : Fin m)] =
      (List.finRange n).foldl
        (fun acc l => acc + (row M i)[l] * A[l][(⟨j, hj⟩ : Fin m)])
        ((Vector.replicate m (0 : Int))[(⟨j, hj⟩ : Fin m)]) := by
    simp only [getElem_row, getElem_mul]
    unfold Vector.dotProduct
    simp only [getElem_col, getElem_row]
    simp only [Fin.getElem_fin, Vector.getElem_replicate]
  exact hentry.trans htarget.symm

/-- Uniqueness of the balanced base-`2^K` representation: digit lists of equal
length whose digits all satisfy `2 · |digit| < 2^K` pack injectively. -/
theorem packDigits_inj (K : Nat) {xs ys : List Int}
    (hlen : xs.length = ys.length)
    (hxs : ∀ x ∈ xs, 2 * x.natAbs < 2 ^ K)
    (hys : ∀ y ∈ ys, 2 * y.natAbs < 2 ^ K)
    (h : packDigits ((2 : Int) ^ K) xs = packDigits ((2 : Int) ^ K) ys) :
    xs = ys := by
  induction xs generalizing ys hys with
  | nil =>
      cases ys with
      | nil => rfl
      | cons y ys => simp at hlen
  | cons x xs ih =>
      cases ys with
      | nil => simp at hlen
      | cons y ys =>
          have hx : 2 * x.natAbs < 2 ^ K := hxs x (by simp)
          have hy : 2 * y.natAbs < 2 ^ K := hys y (by simp)
          have hPabs : ((2 : Int) ^ K).natAbs = 2 ^ K := by
            rw [Int.natAbs_pow]
            rfl
          simp only [packDigits] at h
          have hdiff : x - y =
              (2 : Int) ^ K *
                (packDigits ((2 : Int) ^ K) ys - packDigits ((2 : Int) ^ K) xs) := by
            grind
          have habs : (x - y).natAbs =
              2 ^ K *
                (packDigits ((2 : Int) ^ K) ys -
                  packDigits ((2 : Int) ^ K) xs).natAbs := by
            rw [hdiff, Int.natAbs_mul, hPabs]
          by_cases hts :
              packDigits ((2 : Int) ^ K) ys - packDigits ((2 : Int) ^ K) xs = 0
          · have hxy : x = y := by
              rw [hts, Int.mul_zero] at hdiff
              omega
            have htail : xs = ys :=
              ih (by simpa using hlen)
                (fun a ha => hxs a (List.mem_cons_of_mem _ ha))
                (fun b hb => hys b (List.mem_cons_of_mem _ hb))
                (by omega)
            rw [hxy, htail]
          · exfalso
            have h1 : 1 ≤ (packDigits ((2 : Int) ^ K) ys -
                packDigits ((2 : Int) ^ K) xs).natAbs := by
              omega
            have h2 : 2 ^ K ≤ (x - y).natAbs := by
              rw [habs]
              exact Nat.le_mul_of_pos_right _ (by omega)
            omega

/-- `foldl_dot_natAbs_le` bounds the absolute value of a folded integer dot sum
from per-entry bounds and the length of the folded index list. -/
private theorem foldl_dot_natAbs_le (u v : Vector Int k) (Bu Bv : Nat)
    (hu : ∀ l : Fin k, u[l].natAbs ≤ Bu) (hv : ∀ l : Fin k, v[l].natAbs ≤ Bv)
    (ls : List (Fin k)) (acc : Int) :
    (ls.foldl (fun acc l => acc + u[l] * v[l]) acc).natAbs ≤
      acc.natAbs + ls.length * (Bu * Bv) := by
  induction ls generalizing acc with
  | nil => simp
  | cons l ls ih =>
      simp only [List.foldl_cons, List.length_cons]
      have hstep : (acc + u[l] * v[l]).natAbs ≤ acc.natAbs + Bu * Bv := by
        have hmul : (u[l] * v[l]).natAbs ≤ Bu * Bv := by
          rw [Int.natAbs_mul]
          exact Nat.mul_le_mul (hu l) (hv l)
        have htri := Int.natAbs_add_le acc (u[l] * v[l])
        omega
      have := ih (acc + u[l] * v[l])
      have hgoal : acc.natAbs + Bu * Bv + ls.length * (Bu * Bv) =
          acc.natAbs + (ls.length + 1) * (Bu * Bv) := by
        rw [Nat.succ_mul]
        omega
      omega

/-- Entrywise bound on an integer dot product. -/
theorem natAbs_dotProduct_le (u v : Vector Int k) (Bu Bv : Nat)
    (hu : ∀ l : Fin k, u[l].natAbs ≤ Bu) (hv : ∀ l : Fin k, v[l].natAbs ≤ Bv) :
    (u.dotProduct v).natAbs ≤ k * (Bu * Bv) := by
  have h := foldl_dot_natAbs_le u v Bu Bv hu hv (List.finRange k) 0
  simpa [Vector.dotProduct, Fin.foldl_eq_finRange_foldl] using h

/-- `two_mul_lt_width` turns a bound `x ≤ B` into the base-width inequality
needed for balanced packing injectivity. -/
private theorem two_mul_lt_width {x B : Nat} (hx : x ≤ B) :
    2 * x < 2 ^ (B.log2 + 2) := by
  have h1 : B < 2 ^ (B.log2 + 1) := Nat.lt_log2_self
  have h2 : 2 ^ (B.log2 + 2) = 2 * 2 ^ (B.log2 + 1) := by
    rw [Nat.pow_succ, Nat.mul_comm]
  omega

/-- Every entry of the product `M * A` is bounded by the `maxAbs` scans. -/
theorem natAbs_mul_entry_le (M : Matrix Int n n) (A : Matrix Int n m)
    (i : Fin n) (j : Fin m) :
    (M * A)[i][j].natAbs ≤ n * (maxAbs M * maxAbs A) := by
  rw [getElem_mul]
  exact natAbs_dotProduct_le _ _ _ _
    (fun l => natAbs_le_maxAbs M i l)
    (fun l => by rw [getElem_col]; exact natAbs_le_maxAbs A l j)

/-- The packed certificate decides product equality: sound (`= true` implies
`M * A = C`, by balanced-digit uniqueness at width `packWidth M A C`) and
complete (`M * A = C` implies `= true`, by congruence through
`dotProduct_packRow`). -/
theorem mulEqCert_iff {M : Matrix Int n n} {A C : Matrix Int n m} :
    mulEqCert M A C = true ↔ M * A = C := by
  unfold mulEqCert
  simp only [packWidth, List.all_eq_true, beq_iff_eq, dotProduct_packRow]
  constructor
  · intro h
    apply Hex.Matrix.ext
    apply Vector.ext
    intro i hi
    have hi' := h ⟨i, hi⟩ (List.mem_finRange _)
    simp only [packRow] at hi'
    have hB : ∀ j : Fin m,
        (M * A)[(⟨i, hi⟩ : Fin n)][j].natAbs ≤
          n * maxAbs M * maxAbs A + maxAbs C := by
      intro j
      have hassoc : n * (maxAbs M * maxAbs A) = n * maxAbs M * maxAbs A :=
        (Nat.mul_assoc _ _ _).symm
      have := natAbs_mul_entry_le M A ⟨i, hi⟩ j
      omega
    have hrow := packDigits_inj ((n * maxAbs M * maxAbs A + maxAbs C).log2 + 2)
      (xs := (row (M * A) ⟨i, hi⟩).toList) (ys := (row C ⟨i, hi⟩).toList)
      (by simp) ?_ ?_ hi'
    · exact Vector.toList_inj.mp hrow
    · intro x hx
      obtain ⟨j, hj, hxe⟩ := List.mem_iff_getElem.mp hx
      have hjm : j < m := by simpa using hj
      have hxv : x = (M * A)[(⟨i, hi⟩ : Fin n)][(⟨j, hjm⟩ : Fin m)] := by
        rw [← hxe]
        simp [row]
      rw [hxv]
      exact two_mul_lt_width (hB ⟨j, hjm⟩)
    · intro x hx
      obtain ⟨j, hj, hxe⟩ := List.mem_iff_getElem.mp hx
      have hjm : j < m := by simpa using hj
      have hxv : x = C[(⟨i, hi⟩ : Fin n)][(⟨j, hjm⟩ : Fin m)] := by
        rw [← hxe]
        simp [row]
      rw [hxv]
      exact two_mul_lt_width
        (Nat.le_trans (natAbs_le_maxAbs C ⟨i, hi⟩ ⟨j, hjm⟩) (by omega))
  · intro h i _
    rw [h]

end Internal

namespace Matrix

open Hex.Internal

/-- Executable same-lattice certificate: two integer transforms that multiply
the bases into each other. Each product equality is verified by the packed
certificate `mulEqCert`, so neither product matrix is ever formed. -/
@[expose]
def sameLatticeCert (B B' : Matrix Int n m) (U V : Matrix Int n n) : Bool :=
  mulEqCert U B B' && mulEqCert V B' B

/-- Soundness of `sameLatticeCert`: accepted certificates prove identical
integer row lattices. -/
theorem sameLatticeCert_sound {B B' : Matrix Int n m} {U V : Matrix Int n n} :
    sameLatticeCert B B' U V = true →
      ∀ v, B.memLattice v ↔ B'.memLattice v := by
  intro h v
  unfold sameLatticeCert at h
  simp only [Bool.and_eq_true, mulEqCert_iff] at h
  exact memLattice_iff_of_mul_eq h.1 h.2 v

end Matrix

end Hex
