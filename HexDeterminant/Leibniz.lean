/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import Std
public import Init.Grind.Ring.Field
public import HexDeterminant.Enumeration
public import HexMatrix.Elementary
public import HexMatrix.DotProduct
public import HexMatrix.MatrixAlgebra
public import HexMatrix.Submatrix

public section

/-!
Core Leibniz-formula definitions for the dense determinant.

This module defines the determinant `det` of a dense square matrix as the
`permutationVectors`-indexed sum of signed Leibniz terms, built from `detSign`
(the inversion-parity sign of a permutation vector), `detProduct` (the unsigned
diagonal product), and `detTerm` (their product). It records the small base
cases `det_one_by_one`, `det_two_by_two`, and `det_principalSubmatrix_zero`, and
provides the reusable `foldl`-arithmetic toolkit (scalar factoring, additive
splitting, permutation invariance, single-index scaling) plus the
`Fin.castSucc`/`Fin.last` inversion-count lemmas used by the recursive
determinant proofs in the sibling modules.
-/

namespace Hex
universe u
namespace Matrix
variable {α : Type u}

/-- The sign of a permutation vector, computed from inversion parity. -/
@[expose]
def detSign {R : Type u} [Lean.Grind.Ring R] {n : Nat} (perm : Vector (Fin n) n) : R :=
  if inversionCount perm.toList % 2 = 0 then 1 else -1

/-- The unsigned product associated to a permutation vector. -/
@[expose]
def detProduct {R : Type u} [Lean.Grind.Ring R] {n : Nat}
    (M : Matrix R n n) (perm : Vector (Fin n) n) : R :=
  Fin.foldl n (fun acc i => acc * M[(i, perm[i])]) 1

/-- The Leibniz summand associated to a permutation vector. -/
@[expose]
def detTerm {R : Type u} [Lean.Grind.Ring R] {n : Nat}
    (M : Matrix R n n) (perm : Vector (Fin n) n) : R :=
  detSign perm * detProduct M perm

/-- The determinant of a dense square matrix, defined by the Leibniz formula. -/
@[expose]
def det {R : Type u} [Lean.Grind.Ring R] {n : Nat} (M : Matrix R n n) : R :=
  (permutationVectors n).foldl (fun acc perm => acc + detTerm M perm) 0

/-- The determinant of the empty leading prefix is the Bareiss previous-pivot
convention `1`. -/
@[simp, grind =] theorem det_principalSubmatrix_zero {R : Type u} [Lean.Grind.Ring R]
    (M : Matrix R n n) :
    det (principalSubmatrix M 0 (Nat.zero_le n)) = (1 : R) := by
  simp [det, detTerm, detSign, detProduct, permutationVectors, inversionCount]
  grind

/-- The determinant of a `1 × 1` matrix is its only entry.
This is the smallest non-empty determinant base case. -/
@[simp, grind =] theorem det_one_by_one {R : Type u} [Lean.Grind.Ring R]
    (M : Matrix R 1 1) :
    det M = M[0][0] := by
  simp [det, detTerm, detSign, detProduct, Fin.foldl_eq_finRange_foldl,
    permutationVectors, insertAt, inversionCount, List.finRange]
  grind

/-- The determinant of a `2 × 2` matrix has the usual diagonal-minus-off-diagonal
closed form used by small cofactor expansions. -/
@[simp, grind =] theorem det_two_by_two {R : Type u} [Lean.Grind.CommRing R]
    (M : Matrix R 2 2) :
    det M = M[0][0] * M[1][1] - M[1][0] * M[0][1] := by
  simp [det, detTerm, detSign, detProduct, Fin.foldl_eq_finRange_foldl,
    permutationVectors, insertAt, inversionCount, List.finRange]
  grind


/-- Mapping a duplicate-free list preserves duplicate-freeness when the function
is injective on that list's elements. -/
private theorem list_nodup_map_on {α : Type u} {β : Type v}
    [DecidableEq β] {f : α → β} :
    ∀ {xs : List α}, xs.Nodup →
      (∀ a, a ∈ xs → ∀ b, b ∈ xs → f a = f b → a = b) →
      (xs.map f).Nodup
  | [], _hnodup, _hinj => by simp
  | x :: xs, hnodup, hinj => by
      simp only [List.nodup_cons] at hnodup
      simp only [List.map_cons, List.nodup_cons]
      constructor
      · intro hmem
        rcases List.mem_map.mp hmem with ⟨y, hy, hfy⟩
        have hxy := hinj x (by simp) y (List.mem_cons_of_mem x hy) hfy.symm
        subst y
        exact hnodup.1 hy
      · exact list_nodup_map_on hnodup.2 (by
          intro a ha b hb hab
          exact hinj a (List.mem_cons_of_mem x ha) b (List.mem_cons_of_mem x hb) hab)

/-- If `a - b + c = 0` and `f x - g x + h x = 0` for every `x ∈ xs`, then the same
combination of the three summing folds from `a`, `b`, `c` is `0`. -/
private theorem foldl_det_sum_sub_add_zero
    {R : Type u} [Lean.Grind.CommRing R] {β : Type v}
    (xs : List β) (f g h : β → R) (a b c : R)
    (hacc : a - b + c = 0)
    (hall : ∀ x, x ∈ xs → f x - g x + h x = 0) :
    xs.foldl (fun acc x => acc + f x) a -
      xs.foldl (fun acc x => acc + g x) b +
      xs.foldl (fun acc x => acc + h x) c = 0 := by
  induction xs generalizing a b c with
  | nil => exact hacc
  | cons x xs ih =>
      simp only [List.foldl_cons]
      apply ih
      · have hx : f x - g x + h x = 0 := hall x List.mem_cons_self
        grind
      · intro y hy
        exact hall y (List.mem_cons_of_mem x hy)

/-- A multiplying left fold from `c * z` equals `c` times the same fold from `z`,
factoring the scalar out to the left. -/
private theorem foldl_det_product_mul_left {R : Type u} [Lean.Grind.CommRing R]
    {β : Type v} (xs : List β) (c : R) (f : β → R) (z : R) :
    xs.foldl (fun acc x => acc * f x) (c * z) =
      c * xs.foldl (fun acc x => acc * f x) z := by
  induction xs generalizing z with
  | nil => rfl
  | cons x xs ih =>
      simp only [List.foldl_cons]
      rw [← show c * (z * f x) = (c * z) * f x by grind]
      exact ih (z * f x)

/-- When `i ∉ xs`, scaling the factor at index `i` by `c` leaves the multiplying
fold unchanged, since no element of `xs` equals `i`. -/
private theorem foldl_det_product_no_scale {R : Type u}
    [Lean.Grind.CommRing R] {β : Type v} [DecidableEq β]
    (xs : List β) (i : β) (c : R) (f : β → R) (z : R) (hnot : i ∉ xs) :
    xs.foldl (fun acc x => acc * if x = i then c * f x else f x) z =
      xs.foldl (fun acc x => acc * f x) z := by
  induction xs generalizing z with
  | nil => rfl
  | cons x xs ih =>
      simp only [List.mem_cons, not_or] at hnot
      simp only [List.foldl_cons]
      have hx : x ≠ i := by
        intro hxi
        exact hnot.1 hxi.symm
      rw [if_neg hx]
      exact ih (z * f x) hnot.2

/-- For a `Nodup` list `xs` containing `i`, scaling only the factor at `i` by `c`
multiplies the entire multiplying fold by `c`. -/
private theorem foldl_det_product_single_scale {R : Type u}
    [Lean.Grind.CommRing R] {β : Type v} [DecidableEq β]
    (xs : List β) (i : β) (c : R) (f : β → R) (z : R)
    (hmem : i ∈ xs) (hnodup : xs.Nodup) :
    xs.foldl (fun acc x => acc * if x = i then c * f x else f x) z =
      c * xs.foldl (fun acc x => acc * f x) z := by
  induction xs generalizing z with
  | nil =>
      cases hmem
  | cons x xs ih =>
      simp only [List.mem_cons] at hmem
      simp only [List.nodup_cons] at hnodup
      simp only [List.foldl_cons]
      by_cases hx : x = i
      · subst x
        rw [if_pos rfl]
        calc
          xs.foldl (fun acc x => acc * if x = i then c * f x else f x) (z * (c * f i)) =
              xs.foldl (fun acc x => acc * f x) (z * (c * f i)) := by
                exact foldl_det_product_no_scale xs i c f (z * (c * f i)) hnodup.1
          _ = xs.foldl (fun acc x => acc * f x) (c * (z * f i)) := by
                congr 1
                grind
          _ = c * xs.foldl (fun acc x => acc * f x) (z * f i) := by
                exact foldl_det_product_mul_left xs c f (z * f i)
      · rw [if_neg hx]
        have hmemTail : i ∈ xs := by
          cases hmem with
          | inl hxi => exact False.elim (hx hxi.symm)
          | inr htail => exact htail
        exact ih (z * f x) hmemTail hnodup.2

/-- A multiplying left fold from a sum `a + b` of starting accumulators equals the
sum of the folds from `a` and from `b`. -/
private theorem foldl_det_product_add_start {R : Type u} [Lean.Grind.CommRing R]
    {β : Type v} (xs : List β) (f : β → R) (a b : R) :
    xs.foldl (fun acc x => acc * f x) (a + b) =
      xs.foldl (fun acc x => acc * f x) a +
        xs.foldl (fun acc x => acc * f x) b := by
  induction xs generalizing a b with
  | nil => rfl
  | cons x xs ih =>
      simp only [List.foldl_cons]
      calc
        xs.foldl (fun acc x => acc * f x) ((a + b) * f x) =
          xs.foldl (fun acc x => acc * f x) (a * f x + b * f x) := by
            congr 1
            grind
        _ =
          xs.foldl (fun acc x => acc * f x) (a * f x) +
            xs.foldl (fun acc x => acc * f x) (b * f x) := by
            exact ih (a * f x) (b * f x)

/-- For a `Nodup` list containing `i` with `g` agreeing with `f` away from `i`,
replacing the factor at `i` by `f i + c * g i` splits the fold into the `f`-product
plus `c` times the `g`-product. -/
private theorem foldl_det_product_single_add {R : Type u}
    [Lean.Grind.CommRing R] {β : Type v} [DecidableEq β]
    (xs : List β) (i : β) (c : R) (f g : β → R) (z : R)
    (hmem : i ∈ xs) (hnodup : xs.Nodup)
    (hagree : ∀ x, x ∈ xs → x ≠ i → g x = f x) :
    xs.foldl (fun acc x => acc * if x = i then f x + c * g x else f x) z =
      xs.foldl (fun acc x => acc * f x) z +
        c * xs.foldl (fun acc x => acc * g x) z := by
  induction xs generalizing z with
  | nil =>
      cases hmem
  | cons x xs ih =>
      simp only [List.mem_cons] at hmem
      simp only [List.nodup_cons] at hnodup
      simp only [List.foldl_cons]
      by_cases hx : x = i
      · subst x
        rw [if_pos rfl]
        have hnot : i ∉ xs := hnodup.1
        calc
          xs.foldl (fun acc x => acc * if x = i then f x + c * g x else f x)
              (z * (f i + c * g i)) =
            xs.foldl (fun acc x => acc * f x) (z * (f i + c * g i)) := by
              apply List.foldl_mul_congr
              intro y hy
              have hyi : y ≠ i := by
                intro h
                exact hnot (h ▸ hy)
              rw [if_neg hyi]
          _ = xs.foldl (fun acc x => acc * f x) (z * f i + c * (z * g i)) := by
              congr 1
              grind
          _ =
            xs.foldl (fun acc x => acc * f x) (z * f i) +
              xs.foldl (fun acc x => acc * f x) (c * (z * g i)) := by
              exact foldl_det_product_add_start xs f (z * f i) (c * (z * g i))
          _ =
            xs.foldl (fun acc x => acc * f x) (z * f i) +
              c * xs.foldl (fun acc x => acc * f x) (z * g i) := by
              rw [show
                xs.foldl (fun acc x => acc * f x) (c * (z * g i)) =
                  c * xs.foldl (fun acc x => acc * f x) (z * g i) from
                    foldl_det_product_mul_left xs c f (z * g i)]
          _ =
            xs.foldl (fun acc x => acc * f x) (z * f i) +
              c * xs.foldl (fun acc x => acc * g x) (z * g i) := by
              congr 2
              apply List.foldl_mul_congr
              intro y hy
              exact (hagree y (List.mem_cons.mpr (Or.inr hy)) (by
                intro h
                exact hnot (h ▸ hy))).symm
      · rw [if_neg hx]
        have hmemTail : i ∈ xs := by
          cases hmem with
          | inl hxi => exact False.elim (hx hxi.symm)
          | inr htail => exact htail
        have hgx : g x = f x := hagree x (List.mem_cons.mpr (Or.inl rfl)) hx
        calc
          xs.foldl (fun acc x => acc * if x = i then f x + c * g x else f x)
              (z * f x) =
            xs.foldl (fun acc x => acc * f x) (z * f x) +
              c * xs.foldl (fun acc x => acc * g x) (z * f x) := by
              exact ih (z * f x) hmemTail hnodup.2
                (fun y hy hyi => hagree y (List.mem_cons.mpr (Or.inr hy)) hyi)
          _ =
            xs.foldl (fun acc x => acc * f x) (z * f x) +
              c * xs.foldl (fun acc x => acc * g x) (z * g x) := by
              rw [hgx]

/-- A multiplying left fold from starting accumulator `0` is `0`. -/
private theorem foldl_det_product_zero_start {R : Type u}
    [Lean.Grind.CommRing R] {β : Type v} (xs : List β) (f : β → R) :
    xs.foldl (fun acc x => acc * f x) 0 = 0 := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
      simp only [List.foldl_cons]
      have hzero : (0 : R) * f x = 0 := by grind
      simpa [hzero] using ih

/-- A multiplying left fold is `0` whenever some factor vanishes, that is `i ∈ xs`
and `f i = 0`. -/
private theorem foldl_det_product_zero_of_mem {R : Type u}
    [Lean.Grind.CommRing R] {β : Type v} [DecidableEq β]
    (xs : List β) (i : β) (f : β → R) (z : R)
    (hmem : i ∈ xs) (hzero : f i = 0) :
    xs.foldl (fun acc x => acc * f x) z = 0 := by
  induction xs generalizing z with
  | nil =>
      cases hmem
  | cons x xs ih =>
      simp only [List.mem_cons] at hmem
      simp only [List.foldl_cons]
      by_cases hx : x = i
      · subst x
        rw [hzero]
        have hz : z * (0 : R) = 0 := by grind
        simpa [hz] using foldl_det_product_zero_start xs f
      · have htail : i ∈ xs := by
          cases hmem with
          | inl hxi => exact False.elim (hx hxi.symm)
          | inr htail => exact htail
        exact ih (z * f x) htail

/-- Entry `(i, j)` of the identity matrix `(Matrix.identity (R := R) n)` is `1` when `i = j`
and `0` otherwise. -/
private theorem identity_get {R : Type u} [OfNat R 0] [OfNat R 1] {n : Nat}
    (i j : Fin n) :
    (Matrix.identity (R := R) n)[i][j] = if i = j then 1 else 0 := by
  simp only [Matrix.identity, getElem_ofFn]

/-- `detProduct` of the identity matrix along `perm` is `0` whenever `perm` moves
some index, that is `perm[i] ≠ i`. -/
private theorem detProduct_identity_zero {R : Type u}
    [Lean.Grind.CommRing R] {n : Nat} (perm : Vector (Fin n) n)
    (i : Fin n) (h : perm[i] ≠ i) :
    detProduct (Matrix.identity (R := R) n) perm = 0 := by
  unfold detProduct
  simp only [getElem_pair_eq_nested]
  rw [Fin.foldl_eq_finRange_foldl]
  have hsymm : i ≠ perm[i] := by
    intro hi
    exact h hi.symm
  exact foldl_det_product_zero_of_mem
    (List.finRange n) i (fun r => (Matrix.identity (R := R) n)[r][perm[r]]) 1
    (List.mem_finRange i) (by
      change (Matrix.identity (R := R) n)[i][perm[i]] = 0
      rw [identity_get]
      rw [if_neg hsymm])


/-- `detProduct` of the identity matrix along `insertAt (Fin.last n) (v.map
Fin.castSucc) i` is `0` when `i ≠ Fin.last n`, since the inserted index is then
moved. -/
private theorem detProduct_identity_insertAt_not_last_zero {R : Type u}
    [Lean.Grind.CommRing R] {n : Nat} (v : Vector (Fin n) n)
    (i : Fin (n + 1)) (h : i ≠ Fin.last n) :
    detProduct (Matrix.identity (R := R) (n + 1))
      (insertAt (Fin.last n) (v.map Fin.castSucc) i) = 0 := by
  apply detProduct_identity_zero
  exact by
    rw [insertAt_get_self]
    exact h.symm

/-- Inserting `Fin.last n` at the last position equates `detProduct` of the
`(n + 1)`-identity along the extended permutation with `detProduct` of the
`n`-identity along `v`. -/
private theorem detProduct_identity_insertAt_last {R : Type u}
    [Lean.Grind.CommRing R] {n : Nat} (v : Vector (Fin n) n) :
    detProduct (Matrix.identity (R := R) (n + 1))
      (insertAt (Fin.last n) (v.map Fin.castSucc) (Fin.last n)) =
    detProduct (Matrix.identity (R := R) n) v := by
  unfold detProduct
  simp only [getElem_pair_eq_nested]
  rw [Fin.foldl_succ_last]
  have hfold :
      Fin.foldl n
          (fun acc i =>
            acc *
              (Matrix.identity (R := R) (n + 1))[i.castSucc][
                (insertAt (Fin.last n) (v.map Fin.castSucc) (Fin.last n))[i.castSucc]]) 1 =
      Fin.foldl n (fun acc i => acc * (Matrix.identity (R := R) n)[i][v[i]]) 1 := by
    congr
    funext acc i
    rw [identity_get, identity_get]
    have hget :
        (insertAt (Fin.last n) (v.map Fin.castSucc) (Fin.last n))[i.castSucc] =
          (v[i]).castSucc := by
      simpa using insertAt_last_get_castSucc (Fin.last n) (v.map Fin.castSucc) i
    rw [hget]
    simp [Fin.ext_iff]
  have hlast :
      (Matrix.identity (R := R) (n + 1))[Fin.last n][
        (insertAt (Fin.last n) (v.map Fin.castSucc) (Fin.last n))[Fin.last n]] = 1 := by
    rw [identity_get]
    have hself :
        (insertAt (Fin.last n) (v.map Fin.castSucc) (Fin.last n))[Fin.last n] =
          Fin.last n := by
      exact insertAt_get_self (Fin.last n) (v.map Fin.castSucc) (Fin.last n)
    simp [hself]
  rw [hfold, hlast]
  have hmul_one : ∀ x : R, x * (1 : R) = x := by
    intro x
    exact Lean.Grind.Semiring.mul_one x
  exact hmul_one _

/-- Folding the inversion count against a pivot is unchanged when both the list
`xs` and the pivot `x` are mapped through `Fin.castSucc`. -/
private theorem inversionFold_map_castSucc {n : Nat} (xs : List (Fin n)) (x : Fin n)
    (acc : Nat) :
    (xs.map Fin.castSucc).foldl
        (fun acc y => acc + if y < x.castSucc then 1 else 0) acc =
    xs.foldl (fun acc y => acc + if y < x then 1 else 0) acc := by
  induction xs generalizing acc with
  | nil => rfl
  | cons y ys ih =>
      simp only [List.map_cons, List.foldl_cons]
      have hhead :
          (if y.castSucc < x.castSucc then 1 else 0) =
            (if y < x then 1 else 0) := by
        simp [Fin.lt_def]
      rw [hhead]
      exact ih _

/-- `inversionCount` is invariant under mapping the permutation list through
`Fin.castSucc`. -/
private theorem inversionCount_map_castSucc {n : Nat} (xs : List (Fin n)) :
    inversionCount (xs.map Fin.castSucc) = inversionCount xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
      simp [inversionCount, ih, inversionFold_map_castSucc]

/-- Appending `Fin.last n` after the `castSucc`-embedded list adds no inversions,
so the count equals `inversionCount xs`. -/
private theorem inversionCount_insert_last_castSucc {n : Nat} (xs : List (Fin n)) :
    inversionCount ((xs.map Fin.castSucc) ++ [Fin.last n]) = inversionCount xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
      simp only [List.map_cons, List.cons_append, inversionCount]
      rw [ih, List.foldl_append, List.foldl_cons, List.foldl_nil, inversionFold_map_castSucc]
      simp [Fin.lt_def]

/-- Inserting `Fin.last n` at any position into the `castSucc`-embedded list leaves
the inversion fold against `x.castSucc` unchanged, since the new last element is
never below `x.castSucc`. -/
private theorem foldl_insertIdx_last_castSucc_not_lt {n : Nat} (xs : List (Fin n))
    (x : Fin n) (p acc : Nat) :
    ((xs.map Fin.castSucc).insertIdx p (Fin.last n)).foldl
        (fun acc y => acc + if y < x.castSucc then 1 else 0) acc =
      (xs.map Fin.castSucc).foldl
        (fun acc y => acc + if y < x.castSucc then 1 else 0) acc := by
  induction xs generalizing p acc with
  | nil =>
      cases p <;> simp [List.insertIdx, Fin.lt_def]
  | cons y ys ih =>
      cases p with
      | zero =>
          have hnlt : ¬ n < x.val := by omega
          simp [List.insertIdx, Fin.lt_def, hnlt]
      | succ p =>
          simp only [List.map_cons]
          rw [List.insertIdx, List.modifyTailIdx_succ_cons]
          simp only [List.foldl_cons]
          change
            ((ys.map Fin.castSucc).insertIdx p (Fin.last n)).foldl
                (fun acc y => acc + if y < x.castSucc then 1 else 0)
                (acc + if y.castSucc < x.castSucc then 1 else 0) =
              (ys.map Fin.castSucc).foldl
                (fun acc y => acc + if y < x.castSucc then 1 else 0)
                (acc + if y.castSucc < x.castSucc then 1 else 0)
          rw [ih p (acc + if y.castSucc < x.castSucc then 1 else 0)]

/-- Every `castSucc`-embedded element is below `Fin.last n`, so folding the
`< Fin.last n` count over the embedded list adds exactly its length. -/
private theorem foldl_all_lt_last_castSucc {n : Nat} (xs : List (Fin n)) (acc : Nat) :
    (xs.map Fin.castSucc).foldl
        (fun acc y => acc + if y < Fin.last n then 1 else 0) acc =
      acc + xs.length := by
  induction xs generalizing acc with
  | nil => simp
  | cons x xs ih =>
      simp only [List.map_cons, List.foldl_cons, List.length_cons]
      rw [ih (acc + if x.castSucc < Fin.last n then 1 else 0)]
      simp [Fin.lt_def]
      omega

/-- Inserting `Fin.last n` at position `p ≤ xs.length` into the `castSucc`-embedded
list raises the inversion count by the `xs.length - p` elements it jumps over. -/
private theorem inversionCount_insertIdx_castSucc_last_eq {n : Nat}
    (xs : List (Fin n)) (p : Nat) (hp : p ≤ xs.length) :
    inversionCount ((xs.map Fin.castSucc).insertIdx p (Fin.last n)) =
      inversionCount xs + (xs.length - p) := by
  induction xs generalizing p with
  | nil =>
      cases p with
      | zero => rfl
      | succ p => cases hp
  | cons x xs ih =>
      cases p with
      | zero =>
          simp only [List.map_cons]
          rw [List.insertIdx, List.modifyTailIdx_zero]
          simp only [inversionCount, List.foldl_cons]
          rw [foldl_all_lt_last_castSucc xs
            (0 + if x.castSucc < Fin.last n then 1 else 0)]
          rw [inversionFold_map_castSucc, inversionCount_map_castSucc]
          simp [Fin.lt_def]
          omega
      | succ p =>
          have hp' : p ≤ xs.length := Nat.succ_le_succ_iff.mp hp
          have hlen : (x :: xs).length - (p + 1) = xs.length - p := by
            simp
          simp only [List.map_cons]
          rw [List.insertIdx, List.modifyTailIdx_succ_cons]
          simp only [inversionCount]
          change
            ((xs.map Fin.castSucc).insertIdx p (Fin.last n)).foldl
                (fun acc y => acc + if y < x.castSucc then 1 else 0) 0 +
                inversionCount ((xs.map Fin.castSucc).insertIdx p (Fin.last n)) =
              xs.foldl (fun acc y => acc + if y < x then 1 else 0) 0 +
                inversionCount xs + ((x :: xs).length - (p + 1))
          rw [foldl_insertIdx_last_castSucc_not_lt xs x p, inversionFold_map_castSucc, ih p hp',
            hlen]
          grind


end Matrix
end Hex
