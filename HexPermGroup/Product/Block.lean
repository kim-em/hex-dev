/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexPermGroup.Product.Perm

public section

namespace Hex.Perm.Wreath

/-- The point `i` of block `j` has label `j*n+i`. -/
@[expose] def index (i : Fin n) (j : Fin m) : Fin (n * m) :=
  ⟨j.val * n + i.val, by
    calc
      j.val * n + i.val < j.val * n + n := Nat.add_lt_add_left i.isLt _
      _ = (j.val + 1) * n := by rw [Nat.add_mul, Nat.one_mul]
      _ ≤ m * n := Nat.mul_le_mul_right n j.isLt
      _ = n * m := Nat.mul_comm ..⟩

/-- A point of the product degree witnesses that blocks are nonempty. -/
theorem pos_of_lt_mul (x : Fin (n * m)) : 0 < n :=
  Nat.pos_of_ne_zero fun h => by
    have hx := x.isLt
    simp [h] at hx

@[expose] def point (x : Fin (n * m)) : Fin n := ⟨x.val % n, Nat.mod_lt _ (pos_of_lt_mul x)⟩

@[expose] def block (x : Fin (n * m)) : Fin m :=
  ⟨x.val / n, (Nat.div_lt_iff_lt_mul (pos_of_lt_mul x)).mpr (by simpa only [Nat.mul_comm] using x.isLt)⟩

@[simp] theorem point_index (i : Fin n) (j : Fin m) : point (index i j) = i := by
  apply Fin.ext
  simp [point, index, Nat.mod_eq_of_lt i.isLt]

@[simp] theorem block_index (i : Fin n) (j : Fin m) : block (index i j) = j := by
  apply Fin.ext
  change (j.val * n + i.val) / n = j.val
  rw [Nat.mul_comm j.val n, Nat.mul_add_div i.pos, Nat.div_eq_of_lt i.isLt, Nat.add_zero]

@[simp] theorem index_point_block (x : Fin (n * m)) : index (point x) (block x) = x := by
  apply Fin.ext
  simpa only [index, point, block, Nat.mul_comm] using Nat.div_add_mod x.val n

theorem index_injective {i a : Fin n} {j b : Fin m} (h : index i j = index a b) :
    i = a ∧ j = b :=
  ⟨by simpa only [point_index] using congrArg point h,
    by simpa only [block_index] using congrArg block h⟩

end Hex.Perm.Wreath
