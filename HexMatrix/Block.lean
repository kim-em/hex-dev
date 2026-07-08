/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexMatrix.Basic
public import HexMatrix.DotProduct

public section

/-!
2×2 block assembly and extraction for dense matrices, and the block
decomposition of matrix multiplication.

Blocks are typed over sum-shaped dimensions (`n₁ + n₂`, `m₁ + m₂`), so every
block equation is well-typed with no side conditions. `fromBlocks` assembles a
matrix from its four quadrants; `toBlocks₁₁ … toBlocks₂₂` extract them back.
The capstone is `fromBlocks_mul_fromBlocks`: multiplying two block matrices is
the assembly of the four quadrant products, the first of the three lemmas the
SPEC decomposes Strassen-Winograd correctness into.
-/

namespace Hex

universe u

namespace Matrix

variable {R : Type u} {n₁ n₂ m₁ m₂ k₁ k₂ : Nat}

/-- Assemble a matrix from four blocks, laid out as
`[[A₁₁, A₁₂], [A₂₁, A₂₂]]`. The result is `(n₁ + n₂) × (m₁ + m₂)`; `Fin.addCases`
routes each row/column index to the block it lands in. -/
@[expose]
def fromBlocks (A₁₁ : Matrix R n₁ m₁) (A₁₂ : Matrix R n₁ m₂)
    (A₂₁ : Matrix R n₂ m₁) (A₂₂ : Matrix R n₂ m₂) : Matrix R (n₁ + n₂) (m₁ + m₂) :=
  ofFn fun I J =>
    Fin.addCases
      (fun i => Fin.addCases (fun j => A₁₁[(i, j)]) (fun j => A₁₂[(i, j)]) J)
      (fun i => Fin.addCases (fun j => A₂₁[(i, j)]) (fun j => A₂₂[(i, j)]) J)
      I

variable {A₁₁ : Matrix R n₁ m₁} {A₁₂ : Matrix R n₁ m₂}
  {A₂₁ : Matrix R n₂ m₁} {A₂₂ : Matrix R n₂ m₂}

/-- Top-left block entry of `fromBlocks`. -/
@[simp, grind =] theorem getElem_fromBlocks₁₁ (i : Fin n₁) (j : Fin m₁) :
    (fromBlocks A₁₁ A₁₂ A₂₁ A₂₂)[Fin.castAdd n₂ i][Fin.castAdd m₂ j] = A₁₁[i][j] := by
  simp only [fromBlocks, getElem_ofFn, Fin.addCases_left, getElem_pair_eq_nested]

/-- Top-right block entry of `fromBlocks`. -/
@[simp, grind =] theorem getElem_fromBlocks₁₂ (i : Fin n₁) (j : Fin m₂) :
    (fromBlocks A₁₁ A₁₂ A₂₁ A₂₂)[Fin.castAdd n₂ i][Fin.natAdd m₁ j] = A₁₂[i][j] := by
  simp only [fromBlocks, getElem_ofFn, Fin.addCases_left, Fin.addCases_right, getElem_pair_eq_nested]

/-- Bottom-left block entry of `fromBlocks`. -/
@[simp, grind =] theorem getElem_fromBlocks₂₁ (i : Fin n₂) (j : Fin m₁) :
    (fromBlocks A₁₁ A₁₂ A₂₁ A₂₂)[Fin.natAdd n₁ i][Fin.castAdd m₂ j] = A₂₁[i][j] := by
  simp only [fromBlocks, getElem_ofFn, Fin.addCases_left, Fin.addCases_right, getElem_pair_eq_nested]

/-- Bottom-right block entry of `fromBlocks`. -/
@[simp, grind =] theorem getElem_fromBlocks₂₂ (i : Fin n₂) (j : Fin m₂) :
    (fromBlocks A₁₁ A₁₂ A₂₁ A₂₂)[Fin.natAdd n₁ i][Fin.natAdd m₁ j] = A₂₂[i][j] := by
  simp only [fromBlocks, getElem_ofFn, Fin.addCases_right, getElem_pair_eq_nested]

/-- Extract the top-left `n₁ × m₁` block. -/
@[expose]
def toBlocks₁₁ (M : Matrix R (n₁ + n₂) (m₁ + m₂)) : Matrix R n₁ m₁ :=
  ofFn fun i j => M[(Fin.castAdd n₂ i, Fin.castAdd m₂ j)]

/-- Extract the top-right `n₁ × m₂` block. -/
@[expose]
def toBlocks₁₂ (M : Matrix R (n₁ + n₂) (m₁ + m₂)) : Matrix R n₁ m₂ :=
  ofFn fun i j => M[(Fin.castAdd n₂ i, Fin.natAdd m₁ j)]

/-- Extract the bottom-left `n₂ × m₁` block. -/
@[expose]
def toBlocks₂₁ (M : Matrix R (n₁ + n₂) (m₁ + m₂)) : Matrix R n₂ m₁ :=
  ofFn fun i j => M[(Fin.natAdd n₁ i, Fin.castAdd m₂ j)]

/-- Extract the bottom-right `n₂ × m₂` block. -/
@[expose]
def toBlocks₂₂ (M : Matrix R (n₁ + n₂) (m₁ + m₂)) : Matrix R n₂ m₂ :=
  ofFn fun i j => M[(Fin.natAdd n₁ i, Fin.natAdd m₁ j)]

/-- Entry of the top-left extractor. -/
@[simp, grind =] theorem getElem_toBlocks₁₁ (M : Matrix R (n₁ + n₂) (m₁ + m₂))
    (i : Fin n₁) (j : Fin m₁) :
    (toBlocks₁₁ M)[i][j] = M[Fin.castAdd n₂ i][Fin.castAdd m₂ j] := by
  simp only [toBlocks₁₁, getElem_ofFn, getElem_pair_eq_nested]

/-- Entry of the top-right extractor. -/
@[simp, grind =] theorem getElem_toBlocks₁₂ (M : Matrix R (n₁ + n₂) (m₁ + m₂))
    (i : Fin n₁) (j : Fin m₂) :
    (toBlocks₁₂ M)[i][j] = M[Fin.castAdd n₂ i][Fin.natAdd m₁ j] := by
  simp only [toBlocks₁₂, getElem_ofFn, getElem_pair_eq_nested]

/-- Entry of the bottom-left extractor. -/
@[simp, grind =] theorem getElem_toBlocks₂₁ (M : Matrix R (n₁ + n₂) (m₁ + m₂))
    (i : Fin n₂) (j : Fin m₁) :
    (toBlocks₂₁ M)[i][j] = M[Fin.natAdd n₁ i][Fin.castAdd m₂ j] := by
  simp only [toBlocks₂₁, getElem_ofFn, getElem_pair_eq_nested]

/-- Entry of the bottom-right extractor. -/
@[simp, grind =] theorem getElem_toBlocks₂₂ (M : Matrix R (n₁ + n₂) (m₁ + m₂))
    (i : Fin n₂) (j : Fin m₂) :
    (toBlocks₂₂ M)[i][j] = M[Fin.natAdd n₁ i][Fin.natAdd m₁ j] := by
  simp only [toBlocks₂₂, getElem_ofFn, getElem_pair_eq_nested]

/-- Extracting the top-left quadrant of an assembly returns the block. -/
@[simp, grind =] theorem toBlocks₁₁_fromBlocks :
    toBlocks₁₁ (fromBlocks A₁₁ A₁₂ A₂₁ A₂₂) = A₁₁ := by
  apply ext_getElem; intro i j; grind

/-- Extracting the top-right quadrant of an assembly returns the block. -/
@[simp, grind =] theorem toBlocks₁₂_fromBlocks :
    toBlocks₁₂ (fromBlocks A₁₁ A₁₂ A₂₁ A₂₂) = A₁₂ := by
  apply ext_getElem; intro i j; grind

/-- Extracting the bottom-left quadrant of an assembly returns the block. -/
@[simp, grind =] theorem toBlocks₂₁_fromBlocks :
    toBlocks₂₁ (fromBlocks A₁₁ A₁₂ A₂₁ A₂₂) = A₂₁ := by
  apply ext_getElem; intro i j; grind

/-- Extracting the bottom-right quadrant of an assembly returns the block. -/
@[simp, grind =] theorem toBlocks₂₂_fromBlocks :
    toBlocks₂₂ (fromBlocks A₁₁ A₁₂ A₂₁ A₂₂) = A₂₂ := by
  apply ext_getElem; intro i j; grind

/-- Reassembling a matrix from its four extracted quadrants returns the matrix. -/
@[simp] theorem fromBlocks_toBlocks (M : Matrix R (n₁ + n₂) (m₁ + m₂)) :
    fromBlocks (toBlocks₁₁ M) (toBlocks₁₂ M) (toBlocks₂₁ M) (toBlocks₂₂ M) = M := by
  apply ext_getElem
  intro I J
  refine Fin.addCases (fun i => ?_) (fun i => ?_) I <;>
    refine Fin.addCases (fun j => ?_) (fun j => ?_) J <;> grind

/-- Row `Fin.castAdd n₂ i` of an assembly is the concatenation of the two
top-block rows. -/
@[simp, grind =] theorem row_fromBlocks_castAdd (i : Fin n₁) :
    row (fromBlocks A₁₁ A₁₂ A₂₁ A₂₂) (Fin.castAdd n₂ i) = row A₁₁ i ++ row A₁₂ i := by
  ext j hj
  rw [Vector.getElem_append]
  split
  · rename_i hlt
    exact getElem_fromBlocks₁₁ i ⟨j, hlt⟩
  · rename_i hge
    have h' : j - m₁ < m₂ := by omega
    have hJeq : (⟨j, hj⟩ : Fin (m₁ + m₂)) = Fin.natAdd m₁ ⟨j - m₁, h'⟩ := by
      apply Fin.ext; simp only [Fin.natAdd]; omega
    calc (row (fromBlocks A₁₁ A₁₂ A₂₁ A₂₂) (Fin.castAdd n₂ i))[j]'hj
        = (fromBlocks A₁₁ A₁₂ A₂₁ A₂₂)[Fin.castAdd n₂ i][Fin.natAdd m₁ ⟨j - m₁, h'⟩] :=
          congrArg (fun J : Fin (m₁ + m₂) =>
            (fromBlocks A₁₁ A₁₂ A₂₁ A₂₂)[Fin.castAdd n₂ i][J]) hJeq
      _ = (row A₁₂ i)[j - m₁]'h' := getElem_fromBlocks₁₂ i ⟨j - m₁, h'⟩

/-- Row `Fin.natAdd n₁ i` of an assembly is the concatenation of the two
bottom-block rows. -/
@[simp, grind =] theorem row_fromBlocks_natAdd (i : Fin n₂) :
    row (fromBlocks A₁₁ A₁₂ A₂₁ A₂₂) (Fin.natAdd n₁ i) = row A₂₁ i ++ row A₂₂ i := by
  ext j hj
  rw [Vector.getElem_append]
  split
  · rename_i hlt
    exact getElem_fromBlocks₂₁ i ⟨j, hlt⟩
  · rename_i hge
    have h' : j - m₁ < m₂ := by omega
    have hJeq : (⟨j, hj⟩ : Fin (m₁ + m₂)) = Fin.natAdd m₁ ⟨j - m₁, h'⟩ := by
      apply Fin.ext; simp only [Fin.natAdd]; omega
    calc (row (fromBlocks A₁₁ A₁₂ A₂₁ A₂₂) (Fin.natAdd n₁ i))[j]'hj
        = (fromBlocks A₁₁ A₁₂ A₂₁ A₂₂)[Fin.natAdd n₁ i][Fin.natAdd m₁ ⟨j - m₁, h'⟩] :=
          congrArg (fun J : Fin (m₁ + m₂) =>
            (fromBlocks A₁₁ A₁₂ A₂₁ A₂₂)[Fin.natAdd n₁ i][J]) hJeq
      _ = (row A₂₂ i)[j - m₁]'h' := getElem_fromBlocks₂₂ i ⟨j - m₁, h'⟩

/-- Column `Fin.castAdd m₂ j` of an assembly is the concatenation of the two
left-block columns. -/
@[simp, grind =] theorem col_fromBlocks_castAdd (j : Fin m₁) :
    col (fromBlocks A₁₁ A₁₂ A₂₁ A₂₂) (Fin.castAdd m₂ j) = col A₁₁ j ++ col A₂₁ j := by
  ext i hi
  rw [Vector.getElem_append]
  split
  · rename_i hlt
    show (col (fromBlocks A₁₁ A₁₂ A₂₁ A₂₂) (Fin.castAdd m₂ j))[(⟨i, hi⟩ : Fin (n₁ + n₂))]
      = (col A₁₁ j)[(⟨i, hlt⟩ : Fin n₁)]
    rw [getElem_col, getElem_col]
    exact getElem_fromBlocks₁₁ ⟨i, hlt⟩ j
  · rename_i hge
    have h' : i - n₁ < n₂ := by omega
    have hIeq : (⟨i, hi⟩ : Fin (n₁ + n₂)) = Fin.natAdd n₁ ⟨i - n₁, h'⟩ := by
      apply Fin.ext; simp only [Fin.natAdd]; omega
    show (col (fromBlocks A₁₁ A₁₂ A₂₁ A₂₂) (Fin.castAdd m₂ j))[(⟨i, hi⟩ : Fin (n₁ + n₂))]
      = (col A₂₁ j)[(⟨i - n₁, h'⟩ : Fin n₂)]
    rw [getElem_col, getElem_col]
    calc (fromBlocks A₁₁ A₁₂ A₂₁ A₂₂)[(⟨i, hi⟩ : Fin (n₁ + n₂))][Fin.castAdd m₂ j]
        = (fromBlocks A₁₁ A₁₂ A₂₁ A₂₂)[Fin.natAdd n₁ ⟨i - n₁, h'⟩][Fin.castAdd m₂ j] :=
          congrArg (fun I : Fin (n₁ + n₂) =>
            (fromBlocks A₁₁ A₁₂ A₂₁ A₂₂)[I][Fin.castAdd m₂ j]) hIeq
      _ = A₂₁[(⟨i - n₁, h'⟩ : Fin n₂)][j] := getElem_fromBlocks₂₁ ⟨i - n₁, h'⟩ j

/-- Column `Fin.natAdd m₁ j` of an assembly is the concatenation of the two
right-block columns. -/
@[simp, grind =] theorem col_fromBlocks_natAdd (j : Fin m₂) :
    col (fromBlocks A₁₁ A₁₂ A₂₁ A₂₂) (Fin.natAdd m₁ j) = col A₁₂ j ++ col A₂₂ j := by
  ext i hi
  rw [Vector.getElem_append]
  split
  · rename_i hlt
    show (col (fromBlocks A₁₁ A₁₂ A₂₁ A₂₂) (Fin.natAdd m₁ j))[(⟨i, hi⟩ : Fin (n₁ + n₂))]
      = (col A₁₂ j)[(⟨i, hlt⟩ : Fin n₁)]
    rw [getElem_col, getElem_col]
    exact getElem_fromBlocks₁₂ ⟨i, hlt⟩ j
  · rename_i hge
    have h' : i - n₁ < n₂ := by omega
    have hIeq : (⟨i, hi⟩ : Fin (n₁ + n₂)) = Fin.natAdd n₁ ⟨i - n₁, h'⟩ := by
      apply Fin.ext; simp only [Fin.natAdd]; omega
    show (col (fromBlocks A₁₁ A₁₂ A₂₁ A₂₂) (Fin.natAdd m₁ j))[(⟨i, hi⟩ : Fin (n₁ + n₂))]
      = (col A₂₂ j)[(⟨i - n₁, h'⟩ : Fin n₂)]
    rw [getElem_col, getElem_col]
    calc (fromBlocks A₁₁ A₁₂ A₂₁ A₂₂)[(⟨i, hi⟩ : Fin (n₁ + n₂))][Fin.natAdd m₁ j]
        = (fromBlocks A₁₁ A₁₂ A₂₁ A₂₂)[Fin.natAdd n₁ ⟨i - n₁, h'⟩][Fin.natAdd m₁ j] :=
          congrArg (fun I : Fin (n₁ + n₂) =>
            (fromBlocks A₁₁ A₁₂ A₂₁ A₂₂)[I][Fin.natAdd m₁ j]) hIeq
      _ = A₂₂[(⟨i - n₁, h'⟩ : Fin n₂)][j] := getElem_fromBlocks₂₂ ⟨i - n₁, h'⟩ j

/-- **Block decomposition of matrix multiplication.** The product of two 2×2
block matrices is the assembly of the four quadrant products. -/
theorem fromBlocks_mul_fromBlocks [Lean.Grind.Ring R]
    (A₁₁ : Matrix R n₁ m₁) (A₁₂ : Matrix R n₁ m₂)
    (A₂₁ : Matrix R n₂ m₁) (A₂₂ : Matrix R n₂ m₂)
    (B₁₁ : Matrix R m₁ k₁) (B₁₂ : Matrix R m₁ k₂)
    (B₂₁ : Matrix R m₂ k₁) (B₂₂ : Matrix R m₂ k₂) :
    (fromBlocks A₁₁ A₁₂ A₂₁ A₂₂) * (fromBlocks B₁₁ B₁₂ B₂₁ B₂₂) =
      fromBlocks (A₁₁ * B₁₁ + A₁₂ * B₂₁) (A₁₁ * B₁₂ + A₁₂ * B₂₂)
                 (A₂₁ * B₁₁ + A₂₂ * B₂₁) (A₂₁ * B₁₂ + A₂₂ * B₂₂) := by
  apply ext_getElem
  intro I J
  refine Fin.addCases (fun i => ?_) (fun i => ?_) I <;>
    refine Fin.addCases (fun j => ?_) (fun j => ?_) J <;>
      grind [Vector.dotProduct_append]

end Matrix

end Hex
