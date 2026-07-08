/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexMatrix.Submatrix
public import HexMatrix.DotProduct

public section

/-!
Zero-padding of dense matrices and the top-left-block product lemma.

`pad M n' m'` places `M` in the top-left corner of an `n' × m'` matrix and fills
the border with zeros. Its correctness lemma — the **padding lemma** — says that
bordering each operand with zero rows and columns and reading back the top-left
block of the product returns the unpadded product (`takeCols_takeRows_mul_pad`).
This is the second of the three lemmas the SPEC decomposes `mulStrassen_eq_mul`
into; it lets the Strassen recursion pad an odd dimension up to even and recover
the true product from the padded one.
-/

namespace Hex

universe u

namespace Matrix

variable {R : Type u} {n m k : Nat}

/-- `M` embedded in the top-left corner of an `n' × m'` matrix, with zeros filling
the rest. Truncation semantics: an entry whose row is `≥ n` or column is `≥ m` is
`0`, and if `n' < n` or `m' < m` the overhanging entries of `M` are dropped. The
padding lemmas below assume `n ≤ n'` / `m ≤ m'`, the regime where this is genuine
zero-padding. -/
@[expose]
def pad [OfNat R 0] (M : Matrix R n m) (n' m' : Nat) : Matrix R n' m' :=
  ofFn fun i j =>
    if h : i.val < n ∧ j.val < m then M[((⟨i.val, h.1⟩ : Fin n), (⟨j.val, h.2⟩ : Fin m))] else 0

/-- Entry formula for a padded matrix: the original entry inside the block, `0`
outside. -/
@[grind =] theorem getElem_pad [OfNat R 0] (M : Matrix R n m) (n' m' : Nat)
    (i : Fin n') (j : Fin m') :
    (pad M n' m')[i][j] =
      if h : i.val < n ∧ j.val < m then M[((⟨i.val, h.1⟩ : Fin n), (⟨j.val, h.2⟩ : Fin m))]
      else 0 := by
  simp only [pad, getElem_ofFn]

/-- Taking the top-left `n × m` block of `pad M n' m'` returns `M`. -/
theorem takeCols_takeRows_pad [OfNat R 0] (M : Matrix R n m) (n' m' : Nat)
    (hn : n ≤ n') (hm : m ≤ m') :
    takeCols (takeRows (pad M n' m') n hn) m hm = M := by
  apply ext_getElem
  intro i j
  rw [getElem_takeCols, getElem_takeRows, getElem_pad,
    dif_pos (⟨i.isLt, j.isLt⟩ : i.val < n ∧ j.val < m)]
  rfl

/-- An in-range row of a padded matrix is the source row followed by zeros. -/
theorem row_pad [OfNat R 0] (M : Matrix R n m) (n' m' : Nat) (I : Fin n') (hI : I.val < n) :
    row (pad M n' m') I
      = Vector.ofFn (fun t : Fin m' =>
          if h : t.val < m then M[((⟨I.val, hI⟩ : Fin n), (⟨t.val, h⟩ : Fin m))] else 0) := by
  apply Vector.ext
  intro t ht
  rw [Vector.getElem_ofFn]
  show (pad M n' m')[I][(⟨t, ht⟩ : Fin m')] = _
  rw [getElem_pad]
  by_cases htm : t < m
  · rw [dif_pos htm, dif_pos (⟨hI, htm⟩ : I.val < n ∧ (⟨t, ht⟩ : Fin m').val < m)]
  · rw [dif_neg (by simp [htm]), dif_neg htm]

/-- An in-range column of a padded matrix is the source column followed by zeros. -/
theorem col_pad [OfNat R 0] (M : Matrix R n m) (n' m' : Nat) (J : Fin m') (hJ : J.val < m) :
    col (pad M n' m') J
      = Vector.ofFn (fun t : Fin n' =>
          if h : t.val < n then M[((⟨t.val, h⟩ : Fin n), (⟨J.val, hJ⟩ : Fin m))] else 0) := by
  apply Vector.ext
  intro t ht
  rw [Vector.getElem_ofFn]
  show (col (pad M n' m') J)[(⟨t, ht⟩ : Fin n')] = _
  rw [getElem_col, getElem_pad]
  by_cases htn : t < n
  · rw [dif_pos htn, dif_pos (⟨htn, hJ⟩ : (⟨t, ht⟩ : Fin n').val < n ∧ J.val < m)]
  · rw [dif_neg htn, dif_neg (by simp [htn])]

/-- **Padding lemma.** Zero-padding each operand to a common larger middle
dimension and reading back the top-left `n × k` block of the product returns the
unpadded product `A * B`. The border entries are zero, so every extended term of
each dot product is `0 * _` or `_ * 0` and drops out (`dotProduct_extendZero`). -/
theorem takeCols_takeRows_mul_pad [Lean.Grind.Ring R]
    (A : Matrix R n m) (B : Matrix R m k) (n' m' k' : Nat)
    (hn : n ≤ n') (hm : m ≤ m') (hk : k ≤ k') :
    takeCols (takeRows (mul (pad A n' m') (pad B m' k')) n hn) k hk = mul A B := by
  apply ext_getElem
  intro i j
  simp only [getElem_takeCols, getElem_takeRows]
  rw [show mul (pad A n' m') (pad B m' k') = pad A n' m' * pad B m' k' from rfl,
    show mul A B = A * B from rfl, getElem_mul, getElem_mul]
  obtain ⟨d, rfl⟩ := Nat.le.dest hm
  rw [row_pad A n' (m + d) _ i.isLt, col_pad B (m + d) k' _ j.isLt,
    Vector.dotProduct_extendZero m d (fun t : Fin m => A[((⟨i.val, i.isLt⟩ : Fin n), t)])
      (fun t : Fin m => B[(t, (⟨j.val, j.isLt⟩ : Fin k))])]
  have hrowA : row A i = Vector.ofFn (fun t : Fin m => A[((⟨i.val, i.isLt⟩ : Fin n), t)]) := by
    apply Vector.ext; intro t ht; rw [Vector.getElem_ofFn]; rfl
  have hcolB : col B j = Vector.ofFn (fun t : Fin m => B[(t, (⟨j.val, j.isLt⟩ : Fin k))]) := by
    apply Vector.ext; intro t ht
    rw [Vector.getElem_ofFn]
    show (col B j)[(⟨t, ht⟩ : Fin m)] = _
    rw [getElem_col]
    rfl
  rw [hrowA, hcolB]

end Matrix

end Hex
