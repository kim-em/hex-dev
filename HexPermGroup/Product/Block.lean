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

@[expose] def point (hn : 0 < n) (x : Fin (n * m)) : Fin n := ⟨x.val % n, Nat.mod_lt _ hn⟩

@[expose] def block (hn : 0 < n) (x : Fin (n * m)) : Fin m :=
  ⟨x.val / n, (Nat.div_lt_iff_lt_mul hn).mpr (by simpa only [Nat.mul_comm] using x.isLt)⟩

@[simp] theorem point_index (hn : 0 < n) (i : Fin n) (j : Fin m) : point hn (index i j) = i := by
  apply Fin.ext
  simp [point, index, Nat.mod_eq_of_lt i.isLt]

@[simp] theorem block_index (hn : 0 < n) (i : Fin n) (j : Fin m) : block hn (index i j) = j := by
  apply Fin.ext
  change (j.val * n + i.val) / n = j.val
  rw [Nat.mul_comm j.val n, Nat.mul_add_div hn, Nat.div_eq_of_lt i.isLt, Nat.add_zero]

@[simp] theorem index_point_block (hn : 0 < n) (x : Fin (n * m)) : index (point hn x) (block hn x) = x := by
  apply Fin.ext
  simpa only [index, point, block, Nat.mul_comm] using Nat.div_add_mod x.val n

theorem index_injective (hn : 0 < n) {i a : Fin n} {j b : Fin m} (h : index i j = index a b) :
    i = a ∧ j = b :=
  ⟨by simpa only [point_index] using congrArg (point hn) h,
    by simpa only [block_index] using congrArg (block hn) h⟩

end Hex.Perm.Wreath
