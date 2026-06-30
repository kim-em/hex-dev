/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexMatrix.Basic

public section

/-!
Algebraic laws for dense matrix multiplication.
-/

namespace Hex

universe u v w

namespace Matrix

/-- Folding the indicator-weighted terms `(if i = l then 1 else 0) * f l` over a
duplicate-free list containing `i` picks out exactly `f i`, adding it to the accumulator;
the selection step behind reading a single matrix entry out of a sum. -/
private theorem foldl_indicator_mul_unique {R : Type u} [Lean.Grind.Ring R]
    {n : Nat} (xs : List (Fin n)) (i : Fin n) (f : Fin n → R)
    (hi : i ∈ xs) (hnodup : xs.Nodup) (acc : R) :
    xs.foldl (fun acc l => acc + (if i = l then (1 : R) else 0) * f l) acc =
      acc + f i := by
  induction xs generalizing acc with
  | nil =>
      exact absurd hi List.not_mem_nil
  | cons x xs ih =>
      simp only [List.foldl_cons]
      rcases List.mem_cons.mp hi with hieq | hitail
      · subst i
        have hxs_zero :
            ∀ y ∈ xs, (if x = y then (1 : R) else 0) * f y = 0 := by
          intro y hy
          have hxy : x ≠ y := fun heq => (List.nodup_cons.mp hnodup).1 (heq ▸ hy)
          rw [if_neg hxy]
          grind
        rw [if_pos rfl, List.foldl_add_eq_self xs _ _ hxs_zero]
        grind
      · have hxi : i ≠ x := by
          intro heq
          rw [← heq] at hnodup
          exact (List.nodup_cons.mp hnodup).1 hitail
        rw [if_neg hxi]
        have hzero : (0 : R) * f x = 0 := by grind
        rw [hzero]
        have hac : acc + (0 : R) = acc := by grind
        rw [hac]
        exact ih hitail (List.nodup_cons.mp hnodup).2 acc

/-- Matrix multiplication associates with matrix-vector multiplication. -/
theorem mul_assoc_vec [Lean.Grind.Ring R]
    (A : Matrix R n m) (B : Matrix R m k) (v : Vector R k) :
    (A * B) * v = A * (B * v) := by
  ext i hi
  let ii : Fin n := ⟨i, hi⟩
  simp [HMul.hMul, mulVec, mul, row, col, Vector.dotProduct, ofFn]
  change
    (List.finRange k).foldl
        (fun acc l =>
          acc + (List.finRange m).foldl (fun acc j => acc + A[ii][j] * B[j][l]) 0 *
            v[l]) 0 =
      (List.finRange m).foldl
        (fun acc j =>
          acc + A[ii][j] *
            (List.finRange k).foldl (fun acc l => acc + B[j][l] * v[l]) 0) 0
  calc
    (List.finRange k).foldl
        (fun acc l =>
          acc + (List.finRange m).foldl (fun acc j => acc + A[ii][j] * B[j][l]) 0 *
            v[l]) 0 =
        (List.finRange k).foldl
          (fun acc l =>
            acc + (List.finRange m).foldl
              (fun acc j => acc + A[ii][j] * B[j][l] * v[l]) 0) 0 := by
          apply List.foldl_add_congr
          intro l _hl
          rw [List.foldl_add_mul_right]
          grind
    _ = (List.finRange m).foldl
        (fun acc j =>
          acc + A[ii][j] *
            (List.finRange k).foldl (fun acc l => acc + B[j][l] * v[l]) 0) 0 := by
          rw [List.foldl_add_comm]
          apply List.foldl_add_congr
          intro j _hj
          rw [← List.foldl_add_mul_left]
          have hzero : A[ii][j] * (0 : R) = 0 := by grind
          rw [hzero]
          apply List.foldl_add_congr
          intro l _hl
          grind

/-- Transpose reverses matrix multiplication over a commutative coefficient type. -/
theorem transpose_mul_of_mul_comm [Lean.Grind.CommRing R]
    (A : Matrix R n m) (B : Matrix R m k) :
    Matrix.transpose (A * B) = Matrix.transpose B * Matrix.transpose A := by
  ext i hi j hj
  let ii : Fin k := ⟨i, hi⟩
  let jj : Fin n := ⟨j, hj⟩
  change (Matrix.transpose (A * B))[ii][jj] = (Matrix.transpose B * Matrix.transpose A)[ii][jj]
  rw [getElem_transpose]
  change (A * B)[jj][ii] = (Matrix.transpose B * Matrix.transpose A)[ii][jj]
  simp [HMul.hMul, mul, row, col, transpose, Vector.dotProduct, ofFn]
  change
    (List.finRange m).foldl (fun acc l => acc + A[jj][l] * B[l][ii]) 0 =
      (List.finRange m).foldl (fun acc l => acc + B[l][ii] * A[jj][l]) 0
  apply List.foldl_add_congr
  intro l _hl
  rw [Lean.Grind.CommSemiring.mul_comm]

/-- Left-multiplication by the identity matrix leaves a vector unchanged. -/
@[simp, grind =] theorem identity_mulVec [Lean.Grind.Ring R] (v : Vector R n) :
    (Matrix.identity (R := R) n) * v = v := by
  ext i hi
  let ii : Fin n := ⟨i, hi⟩
  simp [HMul.hMul, mulVec, row, Vector.dotProduct]
  change (List.finRange n).foldl
      (fun acc j => acc + (Matrix.identity (R := R) n)[ii][j] * v[j]) 0 =
    v[ii]
  calc
    (List.finRange n).foldl
        (fun acc j => acc + (Matrix.identity (R := R) n)[ii][j] * v[j]) 0 =
        (List.finRange n).foldl
          (fun acc j => acc + (if ii = j then (1 : R) else 0) * v[j]) 0 := by
          apply List.foldl_add_congr
          intro j _hj
          rw [getElem_identity]
    _ = v[ii] := by
          rw [foldl_indicator_mul_unique (List.finRange n) ii (fun j => v[j])
            (List.mem_finRange _) (List.nodup_finRange n) 0]
          grind

/-- Left-multiplication by the identity matrix leaves a matrix unchanged. -/
@[simp, grind =] theorem identity_mul [Lean.Grind.Ring R] (M : Matrix R n m) :
    (Matrix.identity (R := R) n) * M = M := by
  ext i hi j hj
  let ii : Fin n := ⟨i, hi⟩
  let jj : Fin m := ⟨j, hj⟩
  change ((Matrix.identity (R := R) n) * M)[ii][jj] = M[ii][jj]
  simp [HMul.hMul, mul, row, col, Vector.dotProduct]
  simp [ofFn]
  change
    (List.finRange n).foldl
        (fun acc l => acc + (Matrix.identity (R := R) n)[ii][l] * M[l][jj]) 0 =
      M[ii][jj]
  calc
    (List.finRange n).foldl
        (fun acc l => acc + (Matrix.identity (R := R) n)[ii][l] * M[l][jj]) 0 =
        (List.finRange n).foldl
          (fun acc l => acc + (if ii = l then (1 : R) else 0) * M[l][jj]) 0 := by
          apply List.foldl_add_congr
          intro l _hl
          rw [getElem_identity]
    _ = M[ii][jj] := by
          rw [foldl_indicator_mul_unique (List.finRange n) ii (fun l => M[l][jj])
            (List.mem_finRange _) (List.nodup_finRange n) 0]
          grind

/-- Right-multiplication by the identity matrix leaves a matrix unchanged. -/
@[simp, grind =] theorem mul_identity [Lean.Grind.Ring R] (M : Matrix R n m) :
    M * (Matrix.identity (R := R) m) = M := by
  ext i hi j hj
  let ii : Fin n := ⟨i, hi⟩
  let jj : Fin m := ⟨j, hj⟩
  change (M * (Matrix.identity (R := R) m))[ii][jj] = M[ii][jj]
  simp [HMul.hMul, mul, row, col, Vector.dotProduct]
  simp [ofFn]
  change
    (List.finRange m).foldl
        (fun acc l => acc + M[ii][l] * (Matrix.identity (R := R) m)[l][jj]) 0 =
      M[ii][jj]
  calc
    (List.finRange m).foldl
        (fun acc l => acc + M[ii][l] * (Matrix.identity (R := R) m)[l][jj]) 0 =
        (List.finRange m).foldl
          (fun acc l => acc + (if jj = l then (1 : R) else 0) * M[ii][l]) 0 := by
          apply List.foldl_add_congr
          intro l _hl
          rw [getElem_identity]
          split <;> grind
    _ = M[ii][jj] := by
          rw [foldl_indicator_mul_unique (List.finRange m) jj (fun l => M[ii][l])
            (List.mem_finRange _) (List.nodup_finRange m) 0]
          grind

/-- Matrix multiplication is associative. -/
theorem mul_assoc [Lean.Grind.Ring R]
    (A : Matrix R n m) (B : Matrix R m k) (C : Matrix R k l) :
    (A * B) * C = A * (B * C) := by
  ext i hi j hj
  let ii : Fin n := ⟨i, hi⟩
  let jj : Fin l := ⟨j, hj⟩
  change ((A * B) * C)[ii][jj] = (A * (B * C))[ii][jj]
  simpa [HMul.hMul, mulVec, mul, row, col, Vector.dotProduct, ofFn] using
    congrArg (fun v => v[ii]) (mul_assoc_vec A B (col C jj))

/-- Matrix-vector multiplication sends the zero vector to the zero vector. -/
@[simp, grind =] theorem mulVec_zero [Lean.Grind.Ring R] (A : Matrix R n m) :
    A * (0 : Vector R m) = 0 := by
  ext i hi
  let ii : Fin n := ⟨i, hi⟩
  simp [HMul.hMul, mulVec, row, Vector.dotProduct]
  change (List.finRange m).foldl (fun acc j => acc + A[ii][j] * (0 : R)) 0 = 0
  apply List.foldl_add_eq_self
  intro j _hj
  grind

/-- The zero matrix sends every vector to the zero vector. -/
@[simp, grind =] theorem zero_mulVec [Lean.Grind.Ring R] (v : Vector R m) :
    (0 : Matrix R n m) * v = 0 := by
  ext i hi
  let ii : Fin n := ⟨i, hi⟩
  simp [HMul.hMul, mulVec, row, Vector.dotProduct]
  change (List.finRange m).foldl (fun acc j => acc + (0 : Matrix R n m)[ii][j] * v[j]) 0 = 0
  apply List.foldl_add_eq_self
  intro j _hj
  change (Matrix.zero n m : Matrix R n m)[ii][j] * v[j] = 0
  simpa [Matrix.zero, ofFn] using Lean.Grind.Semiring.zero_mul v[j]

/-- Matrix-vector multiplication distributes over matrix subtraction. -/
@[grind =] theorem sub_mulVec [Lean.Grind.Ring R] (A B : Matrix R n m) (v : Vector R m) :
    (A - B) * v = A * v - B * v := by
  ext i hi
  let ii : Fin n := ⟨i, hi⟩
  simp [HMul.hMul, mulVec, row, Vector.dotProduct]
  change
    (List.finRange m).foldl (fun acc j => acc + (A - B)[ii][j] * v[j]) 0 =
      (List.finRange m).foldl (fun acc j => acc + A[ii][j] * v[j]) 0 -
        (List.finRange m).foldl (fun acc j => acc + B[ii][j] * v[j]) 0
  calc
    (List.finRange m).foldl (fun acc j => acc + (A - B)[ii][j] * v[j]) 0 =
        (List.finRange m).foldl
          (fun acc j => acc + (A[ii][j] * v[j] - B[ii][j] * v[j]))
          ((0 : R) - 0) := by
          have hzero : (0 : R) - 0 = 0 := by grind
          rw [hzero]
          apply List.foldl_add_congr
          intro j _hj
          rw [getElem_sub]
          have hdist : ∀ a b c : R, (a - b) * c = a * c - b * c := fun a b c => by grind
          exact hdist _ _ _
    _ = (List.finRange m).foldl (fun acc j => acc + A[ii][j] * v[j]) 0 -
          (List.finRange m).foldl (fun acc j => acc + B[ii][j] * v[j]) 0 := by
          rw [List.foldl_add_sub]

/-- Multiplication by `Q - I` is `Q * v - v`. -/
theorem sub_identity_mulVec [Lean.Grind.Ring R] (Q : Matrix R n n) (v : Vector R n) :
    (Q - Matrix.identity n) * v = Q * v - v := by
  rw [sub_mulVec, identity_mulVec]

end Matrix

end Hex
