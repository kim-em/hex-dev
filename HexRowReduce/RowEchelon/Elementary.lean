/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexMatrix.Elementary
public import HexMatrix.DotProduct
public import HexMatrix.MatrixAlgebra

public section

/-!
Algebraic properties of elementary row/column operations.

The primitive executable operations live in `HexMatrix.Elementary`. This module
adds the multiplication- and inverse-preservation facts (`rowSwap_mul`,
`rowScale_mul`, `rowAdd_mul`, the `*_transform_mul_preserve` and
`*_inverse_preserve` families, and the column-operation analogues) on which the
row-reduction, span/nullspace, and determinant routines rely.
-/

namespace Hex

universe u

namespace Matrix


/-- Two fold-sums over `xs` agree when their summand functions `f` and `g` agree
pointwise on `xs`; congruence for the fold-sum under the integrand, used to rewrite
the summand in the row-echelon sum manipulations. -/
private theorem foldl_sum_congr_aux {R : Type u} [Add R] {α : Type v}
    (xs : List α) (f g : α → R) (acc : R)
    (h : ∀ x ∈ xs, f x = g x) :
    xs.foldl (fun acc x => acc + f x) acc =
    xs.foldl (fun acc x => acc + g x) acc := by
  induction xs generalizing acc with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.foldl_cons]
    have hx : f x = g x := h x (by simp)
    have hxs : ∀ y ∈ xs, f y = g y := fun y hy => h y (List.mem_cons_of_mem _ hy)
    rw [hx]
    exact ih (acc + g x) hxs

/-- Left multiplication by `c` distributes through a fold-sum, scaling each summand
`f x` to `c * f x` and the initial accumulator to `c * acc`; pulls a left scalar
factor through the accumulating sum in the row-echelon rewrites. -/
private theorem foldl_sum_mul_left_aux {R : Type u} [Lean.Grind.Ring R]
    {α : Type v} (xs : List α) (f : α → R) (c acc : R) :
    c * xs.foldl (fun acc x => acc + f x) acc =
    xs.foldl (fun acc x => acc + c * f x) (c * acc) := by
  induction xs generalizing acc with
  | nil => simp
  | cons x xs ih =>
    simp only [List.foldl_cons]
    rw [ih (acc := acc + f x)]
    have hdist : c * (acc + f x) = c * acc + c * f x := by grind
    rw [hdist]

/-- Right multiplication by `c` distributes through a fold-sum, scaling each summand
`f x` to `f x * c` and the initial accumulator to `acc * c`; pulls a right scalar
factor through the accumulating sum in the row-echelon rewrites. -/
private theorem foldl_sum_mul_right_aux {R : Type u} [Lean.Grind.Ring R]
    {α : Type v} (xs : List α) (f : α → R) (c acc : R) :
    xs.foldl (fun acc x => acc + f x) acc * c =
    xs.foldl (fun acc x => acc + f x * c) (acc * c) := by
  induction xs generalizing acc with
  | nil => simp
  | cons x xs ih =>
    simp only [List.foldl_cons]
    rw [ih (acc := acc + f x)]
    have hdist : (acc + f x) * c = acc * c + f x * c := by grind
    rw [hdist]

/-- The fold-sum of a pointwise sum `f x + g x` splits into the two separate
fold-sums, provided the starting accumulator splits as `acc = accF + accG`;
additivity of the fold-sum over its summand in the row-echelon rewrites. -/
private theorem foldl_sum_add_aux {R : Type u} [Lean.Grind.Ring R]
    {α : Type v} (xs : List α) (f g : α → R) (acc accF accG : R)
    (h : acc = accF + accG) :
    xs.foldl (fun acc x => acc + (f x + g x)) acc =
    xs.foldl (fun acc x => acc + f x) accF +
    xs.foldl (fun acc x => acc + g x) accG := by
  induction xs generalizing acc accF accG with
  | nil =>
    simp only [List.foldl_nil]
    exact h
  | cons x xs ih =>
    simp only [List.foldl_cons]
    apply ih (acc := acc + (f x + g x)) (accF := accF + f x) (accG := accG + g x)
    rw [h]; grind

/-- Pull a scalar multiple out of the left argument of a dot product when the
left vector is given by `Vector.ofFn (fun k => s * v[k])`. -/
private theorem dotProduct_smul_ofFn_left [Lean.Grind.Ring R]
    (s : R) (v w : Vector R m) :
    (Vector.ofFn fun k => s * v[k]).dotProduct w =
    s * v.dotProduct w := by
  unfold Vector.dotProduct
  rw [foldl_sum_mul_left_aux (xs := List.finRange m)
        (f := fun i => v[i] * w[i]) (c := s) (acc := 0)]
  have hzero : s * (0 : R) = 0 := by grind
  rw [hzero]
  apply foldl_sum_congr_aux
  intro i _
  have hofFn : (Vector.ofFn (fun k : Fin m => s * v[k]))[i] = s * v[i] := by
    simp
  rw [hofFn]
  exact Lean.Grind.Semiring.mul_assoc s v[i] w[i]

/-- Distribute the left argument of a dot product over a sum of the form
`Vector.ofFn (fun k => v[k] + s * w[k])`. -/
private theorem dotProduct_add_smul_ofFn_left [Lean.Grind.Ring R]
    (u v w : Vector R m) (s : R) :
    (Vector.ofFn fun k => u[k] + s * v[k]).dotProduct w =
    u.dotProduct w + s * v.dotProduct w := by
  unfold Vector.dotProduct
  -- LHS body: (u[k] + s * v[k]) * w[k] = u[k] * w[k] + s * (v[k] * w[k])
  rw [show (List.finRange m).foldl
        (fun acc i => acc + (Vector.ofFn fun k => u[k] + s * v[k])[i] * w[i]) 0 =
      (List.finRange m).foldl
        (fun acc i => acc + (u[i] * w[i] + s * (v[i] * w[i]))) 0 from ?_]
  · -- Now split the sum
    have hzero : (0 : R) = 0 + s * 0 := by grind
    rw [foldl_sum_add_aux (xs := List.finRange m)
          (f := fun i => u[i] * w[i])
          (g := fun i => s * (v[i] * w[i]))
          (acc := 0) (accF := 0) (accG := s * 0) (h := by grind)]
    -- Pull s out of the second sum
    rw [← foldl_sum_mul_left_aux (xs := List.finRange m)
          (f := fun i => v[i] * w[i]) (c := s) (acc := 0)]
  · apply foldl_sum_congr_aux
    intro i _
    have hofFn : (Vector.ofFn (fun k : Fin m => u[k] + s * v[k]))[i] =
        u[i] + s * v[i] := by
      simp
    rw [hofFn]
    grind

/-- Distribute the right argument of a dot product over a sum of the form
`Vector.ofFn (fun k => v[k] + s * w[k])`. -/
private theorem dotProduct_add_smul_ofFn_right [Lean.Grind.CommRing R]
    (u v w : Vector R m) (s : R) :
    u.dotProduct (Vector.ofFn fun k => v[k] + s * w[k]) =
    u.dotProduct v + s * u.dotProduct w := by
  unfold Vector.dotProduct
  rw [show (List.finRange m).foldl
        (fun acc i => acc + u[i] * (Vector.ofFn fun k => v[k] + s * w[k])[i]) 0 =
      (List.finRange m).foldl
        (fun acc i => acc + (u[i] * v[i] + s * (u[i] * w[i]))) 0 from ?_]
  · rw [foldl_sum_add_aux (xs := List.finRange m)
        (f := fun i => u[i] * v[i])
        (g := fun i => s * (u[i] * w[i]))
        (acc := 0) (accF := 0) (accG := s * 0) (h := by grind)]
    rw [← foldl_sum_mul_left_aux (xs := List.finRange m)
        (f := fun i => u[i] * w[i]) (c := s) (acc := 0)]
  · apply foldl_sum_congr_aux
    intro i _
    have hofFn : (Vector.ofFn (fun k : Fin m => v[k] + s * w[k]))[i] =
        v[i] + s * w[i] := by
      simp
    rw [hofFn]
    grind

/-- Distribute the right argument of a dot product over a sum of the form
`Vector.ofFn (fun k => v[k] + w[k] * s)`. -/
private theorem dotProduct_add_smulRight_ofFn_right [Lean.Grind.Ring R]
    (u v w : Vector R m) (s : R) :
    u.dotProduct (Vector.ofFn fun k => v[k] + w[k] * s) =
    u.dotProduct v + u.dotProduct w * s := by
  unfold Vector.dotProduct
  rw [show (List.finRange m).foldl
        (fun acc i => acc + u[i] * (Vector.ofFn fun k => v[k] + w[k] * s)[i]) 0 =
      (List.finRange m).foldl
        (fun acc i => acc + (u[i] * v[i] + (u[i] * w[i]) * s)) 0 from ?_]
  · rw [foldl_sum_add_aux (xs := List.finRange m)
          (f := fun i => u[i] * v[i])
          (g := fun i => (u[i] * w[i]) * s)
          (acc := 0) (accF := 0) (accG := 0 * s) (h := by grind)]
    rw [← foldl_sum_mul_right_aux (xs := List.finRange m)
          (f := fun i => u[i] * w[i]) (c := s) (acc := 0)]
  · apply foldl_sum_congr_aux
    intro i _
    have hofFn : (Vector.ofFn (fun k : Fin m => v[k] + w[k] * s))[i] =
        v[i] + w[i] * s := by
      simp
    rw [hofFn]
    grind

/-- Multiplication by `B` commutes with row swap on the left factor. -/
theorem rowSwap_mul [Lean.Grind.Ring R]
    (A : Matrix R n m) (B : Matrix R m k) (i j : Fin n) :
    rowSwap A i j * B = rowSwap (A * B) i j := by
  ext r hr l hl
  let rr : Fin n := ⟨r, hr⟩
  let ll : Fin k := ⟨l, hl⟩
  show ((rowSwap A i j) * B)[rr][ll] = (rowSwap (A * B) i j)[rr][ll]
  rw [getElem_mul (rowSwap A i j) B rr ll, getElem_rowSwap (A * B) i j rr ll]
  by_cases hrj : rr = j
  · rw [if_pos hrj]
    rw [getElem_mul A B i ll]
    have hrow : (rowSwap A i j)[rr] = A[i] := by
      ext k' hk
      let kk : Fin m := ⟨k', hk⟩
      show (rowSwap A i j)[rr][kk] = A[i][kk]
      rw [getElem_rowSwap]; rw [if_pos hrj]
    rw [show row (rowSwap A i j) rr = row A i by simpa [row] using hrow]
  · rw [if_neg hrj]
    by_cases hri : rr = i
    · rw [if_pos hri]
      rw [getElem_mul A B j ll]
      have hrow : (rowSwap A i j)[rr] = A[j] := by
        ext k' hk
        let kk : Fin m := ⟨k', hk⟩
        show (rowSwap A i j)[rr][kk] = A[j][kk]
        rw [getElem_rowSwap]; rw [if_neg hrj, if_pos hri]
      rw [show row (rowSwap A i j) rr = row A j by simpa [row] using hrow]
    · rw [if_neg hri]
      rw [getElem_mul A B rr ll]
      have hrow : (rowSwap A i j)[rr] = A[rr] := by
        ext k' hk
        let kk : Fin m := ⟨k', hk⟩
        show (rowSwap A i j)[rr][kk] = A[rr][kk]
        rw [getElem_rowSwap]; rw [if_neg hrj, if_neg hri]
      rw [show row (rowSwap A i j) rr = row A rr by simpa [row] using hrow]

/-- Multiplication by `B` commutes with row scaling on the left factor. -/
theorem rowScale_mul [Lean.Grind.Ring R]
    (A : Matrix R n m) (B : Matrix R m k) (i : Fin n) (s : R) :
    rowScale A i s * B = rowScale (A * B) i s := by
  ext r hr l hl
  let rr : Fin n := ⟨r, hr⟩
  let ll : Fin k := ⟨l, hl⟩
  show ((rowScale A i s) * B)[rr][ll] = (rowScale (A * B) i s)[rr][ll]
  rw [getElem_mul (rowScale A i s) B rr ll, getElem_rowScale (A * B) i rr s ll]
  by_cases hri : rr = i
  · rw [if_pos hri]
    rw [getElem_mul A B i ll]
    rw [show row (rowScale A i s) rr = Vector.ofFn (fun k' => s * A[i][k']) by
      rw [hri]
      exact row_rowScale_self A i s]
    exact dotProduct_smul_ofFn_left s A[i] (col B ll)
  · rw [if_neg hri]
    rw [getElem_mul A B rr ll]
    rw [show row (rowScale A i s) rr = row A rr by
      exact row_rowScale_of_ne A s hri]

/-- Multiplication by `B` commutes with the row-add operation on the left
factor. -/
theorem rowAdd_mul [Lean.Grind.Ring R]
    (A : Matrix R n m) (B : Matrix R m k) (src dst : Fin n) (s : R) :
    rowAdd A src dst s * B = rowAdd (A * B) src dst s := by
  ext r hr l hl
  let rr : Fin n := ⟨r, hr⟩
  let ll : Fin k := ⟨l, hl⟩
  show ((rowAdd A src dst s) * B)[rr][ll] = (rowAdd (A * B) src dst s)[rr][ll]
  rw [getElem_mul (rowAdd A src dst s) B rr ll, getElem_rowAdd (A * B) src dst rr s ll]
  by_cases hrd : rr = dst
  · rw [if_pos hrd]
    rw [getElem_mul A B dst ll, getElem_mul A B src ll]
    rw [show row (rowAdd A src dst s) rr =
        Vector.ofFn (fun k' => A[dst][k'] + s * A[src][k']) by
      rw [hrd]
      exact row_rowAdd_dst A src dst s]
    exact dotProduct_add_smul_ofFn_left A[dst] A[src] (col B ll) s
  · rw [if_neg hrd]
    rw [getElem_mul A B rr ll]
    rw [show row (rowAdd A src dst s) rr = row A rr by
      exact row_rowAdd_of_ne A src s hrd]

/-- Entrywise action of row swap on matrix-vector multiplication. -/
theorem rowSwap_mulVec_getElem [Mul R] [Add R] [OfNat R 0]
    (M : Matrix R n m) (v : Vector R m) (i j r : Fin n) :
    (rowSwap M i j * v)[r] =
      if r = j then (M * v)[i] else if r = i then (M * v)[j] else (M * v)[r] := by
  rw [getElem_mulVec (rowSwap M i j) v r]
  by_cases hrj : r = j
  · rw [if_pos hrj, getElem_mulVec M v i]
    rw [show row (rowSwap M i j) r = row M i by
      rw [hrj]
      exact row_rowSwap_right M i j]
  · rw [if_neg hrj]
    by_cases hri : r = i
    · rw [if_pos hri, getElem_mulVec M v j]
      rw [show row (rowSwap M i j) r = row M j by
        rw [hri]
        exact row_rowSwap_left M i j]
    · rw [if_neg hri, getElem_mulVec M v r]
      rw [show row (rowSwap M i j) r = row M r by
        exact row_rowSwap_of_ne M hri hrj]

/-- Entrywise action of row scaling on matrix-vector multiplication. -/
theorem rowScale_mulVec_getElem [Lean.Grind.Ring R]
    (M : Matrix R n m) (v : Vector R m) (i r : Fin n) (s : R) :
    (rowScale M i s * v)[r] =
      if r = i then s * (M * v)[i] else (M * v)[r] := by
  rw [getElem_mulVec (rowScale M i s) v r]
  by_cases hri : r = i
  · subst r
    rw [if_pos rfl, getElem_mulVec M v i]
    rw [show row (rowScale M i s) i = Vector.ofFn (fun k => s * M[i][k]) by
      exact row_rowScale_self M i s]
    exact dotProduct_smul_ofFn_left s M[i] v
  · rw [if_neg hri, getElem_mulVec M v r]
    rw [show row (rowScale M i s) r = row M r by
      exact row_rowScale_of_ne M s hri]

/-- Entrywise action of row addition on matrix-vector multiplication. -/
theorem rowAdd_mulVec_getElem [Lean.Grind.Ring R]
    (M : Matrix R n m) (v : Vector R m) (src dst r : Fin n) (s : R) :
    (rowAdd M src dst s * v)[r] =
      if r = dst then (M * v)[dst] + s * (M * v)[src] else (M * v)[r] := by
  rw [getElem_mulVec (rowAdd M src dst s) v r]
  by_cases hrd : r = dst
  · subst r
    rw [if_pos rfl, getElem_mulVec M v dst, getElem_mulVec M v src]
    rw [show row (rowAdd M src dst s) dst =
        Vector.ofFn (fun k => M[dst][k] + s * M[src][k]) by
      exact row_rowAdd_dst M src dst s]
    exact dotProduct_add_smul_ofFn_left M[dst] M[src] v s
  · rw [if_neg hrd, getElem_mulVec M v r]
    rw [show row (rowAdd M src dst s) r = row M r by
      exact row_rowAdd_of_ne M src s hrd]

/-- If `T * M = E`, then `rowSwap T i j * M = rowSwap E i j`: row swap on the
transform side preserves the equation `T * M = E` when applied to both `T` and
`E`. -/
theorem rowSwap_transform_mul_preserve [Lean.Grind.Ring R]
    {T : Matrix R n n} {M : Matrix R n m} {E : Matrix R n m} (i j : Fin n)
    (h : T * M = E) :
    rowSwap T i j * M = rowSwap E i j := by
  rw [rowSwap_mul, h]

/-- If `T * M = E`, then `rowScale T i s * M = rowScale E i s`: row scale on the
transform side preserves the equation `T * M = E` when applied to both `T` and
`E`. -/
theorem rowScale_transform_mul_preserve [Lean.Grind.Ring R]
    {T : Matrix R n n} {M : Matrix R n m} {E : Matrix R n m} (i : Fin n) (s : R)
    (h : T * M = E) :
    rowScale T i s * M = rowScale E i s := by
  rw [rowScale_mul, h]

/-- If `T * M = E`, then `rowAdd T src dst s * M = rowAdd E src dst s`: row
add on the transform side preserves the equation `T * M = E` when applied to
both `T` and `E`. -/
theorem rowAdd_transform_mul_preserve [Lean.Grind.Ring R]
    {T : Matrix R n n} {M : Matrix R n m} {E : Matrix R n m}
    (src dst : Fin n) (s : R)
    (h : T * M = E) :
    rowAdd T src dst s * M = rowAdd E src dst s := by
  rw [rowAdd_mul, h]

/-- Swapping the same two rows twice restores the original matrix. -/
theorem rowSwap_rowSwap (M : Matrix R n m) (i j : Fin n) :
    rowSwap (rowSwap M i j) i j = M := by
  ext r hr k hk
  let rr : Fin n := ⟨r, hr⟩
  let kk : Fin m := ⟨k, hk⟩
  show (rowSwap (rowSwap M i j) i j)[rr][kk] = M[rr][kk]
  rw [getElem_rowSwap]
  by_cases hrj : rr = j
  · rw [if_pos hrj]
    rw [getElem_rowSwap]
    by_cases hji : i = j
    · simp [hrj, hji]
    · simp [hrj, hji]
  · rw [if_neg hrj]
    by_cases hri : rr = i
    · rw [if_pos hri]
      rw [getElem_rowSwap]
      simp [hri]
    · rw [if_neg hri]
      rw [getElem_rowSwap, if_neg hrj, if_neg hri]

/-- Swapping a row with itself leaves the matrix unchanged. -/
@[simp, grind =] theorem rowSwap_self (M : Matrix R n m) (i : Fin n) :
    rowSwap M i i = M := by
  ext r hr k hk
  let rr : Fin n := ⟨r, hr⟩
  let kk : Fin m := ⟨k, hk⟩
  show (rowSwap M i i)[rr][kk] = M[rr][kk]
  rw [getElem_rowSwap]
  by_cases hri : rr = i
  · simp [hri]
  · simp [hri]

/-- Scaling a row by one leaves the matrix unchanged. -/
@[simp, grind =] theorem rowScale_one [Lean.Grind.Semiring R]
    (M : Matrix R n m) (i : Fin n) :
    rowScale M i 1 = M := by
  ext r hr k hk
  let rr : Fin n := ⟨r, hr⟩
  let kk : Fin m := ⟨k, hk⟩
  show (rowScale M i 1)[rr][kk] = M[rr][kk]
  rw [getElem_rowScale]
  by_cases hri : rr = i
  · rw [if_pos hri]
    grind
  · rw [if_neg hri]

/-- Adding zero times one row to another leaves the matrix unchanged. -/
@[simp, grind =] theorem rowAdd_zero [Lean.Grind.Semiring R]
    (M : Matrix R n m) (src dst : Fin n) :
    rowAdd M src dst 0 = M := by
  ext r hr k hk
  let rr : Fin n := ⟨r, hr⟩
  let kk : Fin m := ⟨k, hk⟩
  show (rowAdd M src dst 0)[rr][kk] = M[rr][kk]
  rw [getElem_rowAdd]
  by_cases hrd : rr = dst
  · rw [if_pos hrd]
    grind
  · rw [if_neg hrd]

/-- Scaling a row by `s` and then by `s⁻¹` restores the original matrix when
`s` is nonzero. -/
theorem rowScale_rowScale_inv_left [Lean.Grind.Field R]
    (M : Matrix R n m) (i : Fin n) {s : R} (hs : s ≠ 0) :
    rowScale (rowScale M i s) i s⁻¹ = M := by
  ext r hr k hk
  let rr : Fin n := ⟨r, hr⟩
  let kk : Fin m := ⟨k, hk⟩
  show (rowScale (rowScale M i s) i s⁻¹)[rr][kk] = M[rr][kk]
  rw [getElem_rowScale]
  by_cases hri : rr = i
  · rw [if_pos hri]
    rw [getElem_rowScale, if_pos rfl]
    grind
  · rw [if_neg hri]
    rw [getElem_rowScale, if_neg hri]

/-- Scaling a row by `s⁻¹` and then by `s` restores the original matrix when
`s` is nonzero. -/
theorem rowScale_rowScale_inv_right [Lean.Grind.Field R]
    (M : Matrix R n m) (i : Fin n) {s : R} (hs : s ≠ 0) :
    rowScale (rowScale M i s⁻¹) i s = M := by
  ext r hr k hk
  let rr : Fin n := ⟨r, hr⟩
  let kk : Fin m := ⟨k, hk⟩
  show (rowScale (rowScale M i s⁻¹) i s)[rr][kk] = M[rr][kk]
  rw [getElem_rowScale]
  by_cases hri : rr = i
  · rw [if_pos hri]
    rw [getElem_rowScale, if_pos rfl]
    grind
  · rw [if_neg hri]
    rw [getElem_rowScale, if_neg hri]

/-- Adding `s` times a distinct source row to a destination row and then
adding `-s` times that source row restores the original matrix. -/
theorem rowAdd_rowAdd_neg [Lean.Grind.Ring R]
    (M : Matrix R n m) {src dst : Fin n} (s : R) (hsrcdst : src ≠ dst) :
    rowAdd (rowAdd M src dst s) src dst (-s) = M := by
  ext r hr k hk
  let rr : Fin n := ⟨r, hr⟩
  let kk : Fin m := ⟨k, hk⟩
  show (rowAdd (rowAdd M src dst s) src dst (-s))[rr][kk] = M[rr][kk]
  rw [getElem_rowAdd]
  by_cases hrd : rr = dst
  · rw [if_pos hrd]
    rw [getElem_rowAdd, if_pos rfl]
    have hsrc_ne_dst : src ≠ dst := hsrcdst
    rw [getElem_rowAdd, if_neg hsrc_ne_dst]
    grind
  · rw [if_neg hrd]
    rw [getElem_rowAdd, if_neg hrd]

/-- Adding `-s` times a distinct source row to a destination row and then
adding `s` times that source row restores the original matrix. -/
theorem rowAdd_rowAdd_neg_left [Lean.Grind.Ring R]
    (M : Matrix R n m) {src dst : Fin n} (s : R) (hsrcdst : src ≠ dst) :
    rowAdd (rowAdd M src dst (-s)) src dst s = M := by
  ext r hr k hk
  let rr : Fin n := ⟨r, hr⟩
  let kk : Fin m := ⟨k, hk⟩
  show (rowAdd (rowAdd M src dst (-s)) src dst s)[rr][kk] = M[rr][kk]
  rw [getElem_rowAdd]
  by_cases hrd : rr = dst
  · rw [if_pos hrd]
    rw [getElem_rowAdd, if_pos rfl]
    have hsrc_ne_dst : src ≠ dst := hsrcdst
    rw [getElem_rowAdd, if_neg hsrc_ne_dst]
    grind
  · rw [if_neg hrd]
    rw [getElem_rowAdd, if_neg hrd]

private theorem leftMul_left_inverse_preserve [Lean.Grind.Ring R]
    {S Sinv T : Matrix R n n} (hSinvS : Sinv * S = 1)
    (hT : ∃ Tinv : Matrix R n n, Tinv * T = 1) :
    ∃ Tinv' : Matrix R n n, Tinv' * (S * T) = 1 := by
  rcases hT with ⟨Tinv, hTinv⟩
  refine ⟨Tinv * Sinv, ?_⟩
  calc
    (Tinv * Sinv) * (S * T) = ((Tinv * Sinv) * S) * T := by
      exact (mul_assoc (Tinv * Sinv) S T).symm
    _ = (Tinv * (Sinv * S)) * T := by
      rw [mul_assoc Tinv Sinv S]
    _ = (Tinv * 1) * T := by
      rw [hSinvS]
    _ = Tinv * T := by
      rw [mul_one]
    _ = 1 := hTinv

private theorem leftMul_right_inverse_preserve [Lean.Grind.Ring R]
    {S Sinv T : Matrix R n n} (hSSinv : S * Sinv = 1)
    (hT : ∃ Tinv : Matrix R n n, T * Tinv = 1) :
    ∃ Tinv' : Matrix R n n, (S * T) * Tinv' = 1 := by
  rcases hT with ⟨Tinv, hTinv⟩
  refine ⟨Tinv * Sinv, ?_⟩
  calc
    (S * T) * (Tinv * Sinv) = S * (T * (Tinv * Sinv)) := by
      exact mul_assoc S T (Tinv * Sinv)
    _ = S * ((T * Tinv) * Sinv) := by
      rw [mul_assoc]
    _ = S * (1 * Sinv) := by
      rw [hTinv]
    _ = S * Sinv := by
      rw [one_mul]
    _ = 1 := hSSinv

/-- A row swap preserves existence of a left inverse for a row transform. -/
theorem rowSwap_left_inverse_preserve [Lean.Grind.Ring R]
    (T : Matrix R n n) (i j : Fin n)
    (hT : ∃ Tinv : Matrix R n n, Tinv * T = 1) :
    ∃ Tinv' : Matrix R n n, Tinv' * rowSwap T i j = 1 := by
  let S : Matrix R n n := rowSwap (1 : Matrix R n n) i j
  have hS : S * T = rowSwap T i j := by
    simp [S, rowSwap_mul, one_mul]
  have hSS : S * S = 1 := by
    simp [S, rowSwap_mul, one_mul, rowSwap_rowSwap]
  simpa [hS] using leftMul_left_inverse_preserve (S := S) (Sinv := S) (T := T) hSS hT

/-- A row swap preserves existence of a right inverse for a row transform. -/
theorem rowSwap_right_inverse_preserve [Lean.Grind.Ring R]
    (T : Matrix R n n) (i j : Fin n)
    (hT : ∃ Tinv : Matrix R n n, T * Tinv = 1) :
    ∃ Tinv' : Matrix R n n, rowSwap T i j * Tinv' = 1 := by
  let S : Matrix R n n := rowSwap (1 : Matrix R n n) i j
  have hS : S * T = rowSwap T i j := by
    simp [S, rowSwap_mul, one_mul]
  have hSS : S * S = 1 := by
    simp [S, rowSwap_mul, one_mul, rowSwap_rowSwap]
  simpa [hS] using leftMul_right_inverse_preserve (S := S) (Sinv := S) (T := T) hSS hT

/-- Scaling a row by a nonzero scalar preserves existence of a left inverse for
a row transform. -/
theorem rowScale_left_inverse_preserve [Lean.Grind.Field R]
    (T : Matrix R n n) (i : Fin n) {s : R} (hs : s ≠ 0)
    (hT : ∃ Tinv : Matrix R n n, Tinv * T = 1) :
    ∃ Tinv' : Matrix R n n, Tinv' * rowScale T i s = 1 := by
  let S : Matrix R n n := rowScale (1 : Matrix R n n) i s
  let Sinv : Matrix R n n := rowScale (1 : Matrix R n n) i s⁻¹
  have hS : S * T = rowScale T i s := by
    simp [S, rowScale_mul, one_mul]
  have hSinvS : Sinv * S = 1 := by
    simp [Sinv, S, rowScale_mul, one_mul, rowScale_rowScale_inv_left _ _ hs]
  simpa [hS] using leftMul_left_inverse_preserve (S := S) (Sinv := Sinv) (T := T) hSinvS hT

/-- Scaling a row by a nonzero scalar preserves existence of a right inverse for
a row transform. -/
theorem rowScale_right_inverse_preserve [Lean.Grind.Field R]
    (T : Matrix R n n) (i : Fin n) {s : R} (hs : s ≠ 0)
    (hT : ∃ Tinv : Matrix R n n, T * Tinv = 1) :
    ∃ Tinv' : Matrix R n n, rowScale T i s * Tinv' = 1 := by
  let S : Matrix R n n := rowScale (1 : Matrix R n n) i s
  let Sinv : Matrix R n n := rowScale (1 : Matrix R n n) i s⁻¹
  have hS : S * T = rowScale T i s := by
    simp [S, rowScale_mul, one_mul]
  have hSSinv : S * Sinv = 1 := by
    simp [S, Sinv, rowScale_mul, one_mul, rowScale_rowScale_inv_right _ _ hs]
  simpa [hS] using leftMul_right_inverse_preserve (S := S) (Sinv := Sinv) (T := T) hSSinv hT

/-- Adding a multiple of a distinct source row preserves existence of a left
inverse for a row transform. -/
theorem rowAdd_left_inverse_preserve [Lean.Grind.Ring R]
    (T : Matrix R n n) {src dst : Fin n} (s : R) (hsrcdst : src ≠ dst)
    (hT : ∃ Tinv : Matrix R n n, Tinv * T = 1) :
    ∃ Tinv' : Matrix R n n, Tinv' * rowAdd T src dst s = 1 := by
  let S : Matrix R n n := rowAdd (1 : Matrix R n n) src dst s
  let Sinv : Matrix R n n := rowAdd (1 : Matrix R n n) src dst (-s)
  have hS : S * T = rowAdd T src dst s := by
    simp [S, rowAdd_mul, one_mul]
  have hSinvS : Sinv * S = 1 := by
    simp [Sinv, S, rowAdd_mul, one_mul, rowAdd_rowAdd_neg _ _ hsrcdst]
  simpa [hS] using leftMul_left_inverse_preserve (S := S) (Sinv := Sinv) (T := T) hSinvS hT

/-- Adding a multiple of a distinct source row preserves existence of a right
inverse for a row transform. -/
theorem rowAdd_right_inverse_preserve [Lean.Grind.Ring R]
    (T : Matrix R n n) {src dst : Fin n} (s : R) (hsrcdst : src ≠ dst)
    (hT : ∃ Tinv : Matrix R n n, T * Tinv = 1) :
    ∃ Tinv' : Matrix R n n, rowAdd T src dst s * Tinv' = 1 := by
  let S : Matrix R n n := rowAdd (1 : Matrix R n n) src dst s
  let Sinv : Matrix R n n := rowAdd (1 : Matrix R n n) src dst (-s)
  have hS : S * T = rowAdd T src dst s := by
    simp [S, rowAdd_mul, one_mul]
  have hSSinv : S * Sinv = 1 := by
    simp [S, Sinv, rowAdd_mul, one_mul]
    exact rowAdd_rowAdd_neg_left (1 : Matrix R n n) s hsrcdst
  simpa [hS] using leftMul_right_inverse_preserve (S := S) (Sinv := Sinv) (T := T) hSSinv hT

/-- Multiplication by `A` commutes with the column-add operation on the right
factor over commutative rings. -/
theorem mul_colAdd [Lean.Grind.CommRing R]
    (A : Matrix R n m) (B : Matrix R m k) (src dst : Fin k) (s : R) :
    A * colAdd B src dst s = colAdd (A * B) src dst s := by
  ext r hr l hl
  let rr : Fin n := ⟨r, hr⟩
  let ll : Fin k := ⟨l, hl⟩
  show (A * colAdd B src dst s)[rr][ll] = (colAdd (A * B) src dst s)[rr][ll]
  rw [getElem_mul A (colAdd B src dst s) rr ll, getElem_colAdd (A * B) src dst s rr ll]
  by_cases hld : ll = dst
  · rw [if_pos hld]
    rw [hld, getElem_mul A B rr dst, getElem_mul A B rr src]
    rw [show col (colAdd B src dst s) dst =
        Vector.ofFn (fun i => B[i][dst] + s * B[i][src]) by
      exact col_colAdd_dst B src dst s]
    simpa [col] using
      dotProduct_add_smul_ofFn_right (row A rr)
        (Vector.ofFn fun i => B[i][dst]) (Vector.ofFn fun i => B[i][src]) s
  · rw [if_neg hld]
    rw [getElem_mul A B rr ll]
    rw [show col (colAdd B src dst s) ll = col B ll by
      exact col_colAdd_of_ne B src s hld]


/-- Right multiplication by a right-scalar column addition commutes with the
column-add operation over a possibly noncommutative ring. -/
theorem mul_colAddRight [Lean.Grind.Ring R]
    (A : Matrix R n m) (B : Matrix R m k) (src dst : Fin k) (s : R) :
    A * colAddRight B src dst s = colAddRight (A * B) src dst s := by
  ext r hr l hl
  let rr : Fin n := ⟨r, hr⟩
  let ll : Fin k := ⟨l, hl⟩
  show (A * colAddRight B src dst s)[rr][ll] =
    (colAddRight (A * B) src dst s)[rr][ll]
  rw [getElem_mul A (colAddRight B src dst s) rr ll, getElem_colAddRight (A * B) src dst s rr ll]
  by_cases hld : ll = dst
  · rw [if_pos hld]
    rw [hld, getElem_mul A B rr dst, getElem_mul A B rr src]
    rw [show col (colAddRight B src dst s) dst =
        Vector.ofFn (fun i => B[i][dst] + B[i][src] * s) by
      exact col_colAddRight_dst B src dst s]
    simpa [col] using
      dotProduct_add_smulRight_ofFn_right (row A rr) (col B dst) (col B src) s
  · rw [if_neg hld]
    rw [getElem_mul A B rr ll]
    rw [show col (colAddRight B src dst s) ll = col B ll by
      exact col_colAddRight_of_ne B src s hld]

/-- Adding zero times one column to another leaves the matrix unchanged. -/
@[simp, grind =] theorem colAdd_zero [Lean.Grind.Semiring R]
    (M : Matrix R n m) (src dst : Fin m) :
    colAdd M src dst 0 = M := by
  ext i hi j hj
  let ii : Fin n := ⟨i, hi⟩
  let jj : Fin m := ⟨j, hj⟩
  show (colAdd M src dst 0)[ii][jj] = M[ii][jj]
  rw [getElem_colAdd]
  by_cases hjd : jj = dst
  · rw [if_pos hjd]
    grind
  · rw [if_neg hjd]

/-- Adding one column times zero to another leaves the matrix unchanged. -/
@[simp, grind =] theorem colAddRight_zero [Lean.Grind.Semiring R]
    (M : Matrix R n m) (src dst : Fin m) :
    colAddRight M src dst 0 = M := by
  ext i hi j hj
  let ii : Fin n := ⟨i, hi⟩
  let jj : Fin m := ⟨j, hj⟩
  show (colAddRight M src dst 0)[ii][jj] = M[ii][jj]
  rw [getElem_colAddRight]
  by_cases hjd : jj = dst
  · rw [if_pos hjd]
    grind
  · rw [if_neg hjd]
end Matrix
end Hex
