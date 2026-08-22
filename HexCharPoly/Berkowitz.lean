/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexCharPoly.Toeplitz

public section

/-!
The division-free Samuelson--Berkowitz recursion on trailing principal blocks.
The raw result is deliberately kept in descending degree order.
-/

namespace Hex.Matrix

universe u

variable {R : Type u} [Lean.Grind.CommRing R] {n : Nat}

/-- The trailing `k x k` principal block of a square matrix. -/
@[expose]
def trailingBlock (A : Matrix R n n) (k : Nat) (hk : k <= n) : Matrix R k k :=
  let blockRegion : Region n n k k := {
    r0 := n - k
    c0 := n - k
    rows_le := by omega
    cols_le := by omega
  }
  blockRegion.toMatrix A

omit [Lean.Grind.CommRing R] in
/-- Entry formula for a trailing principal block. -/
@[simp, grind =]
theorem getElem_trailingBlock (A : Matrix R n n) (k : Nat) (hk : k <= n)
    (i j : Fin k) :
    (trailingBlock A k hk)[i][j] =
      A[(n - k + i.val, n - k + j.val)]'(by omega) := by
  rw [trailingBlock, Region.getElem_toMatrix, Region.get_apply]

omit [Lean.Grind.CommRing R] in
/-- The trailing block of full size is the original square matrix. -/
@[simp, grind =]
theorem trailingBlock_self (A : Matrix R n n) :
    trailingBlock A n (Nat.le_refl n) = A := by
  apply Matrix.ext_getElem
  intro i j
  rw [getElem_trailingBlock]
  simp

/-- Successive moments `-(row dot B^j col)`.  The final multiplication is
omitted because its result would not be consumed. -/
@[expose]
def berkowitzMoments {k : Nat} (B : Matrix R k k) (row : Vector R k) :
    (count : Nat) -> Vector R k -> List R
  | 0, _ => []
  | 1, w => [-row.dotProduct w]
  | j + 2, w => -row.dotProduct w :: berkowitzMoments B row (j + 1) (B * w)

/-- The moment loop records exactly the requested number of scalars. -/
@[simp, grind =]
theorem length_berkowitzMoments {k : Nat} (B : Matrix R k k) (row : Vector R k)
    (count : Nat) (w : Vector R k) :
    (berkowitzMoments B row count w).length = count := by
  induction count generalizing w with
  | zero => rfl
  | succ count ih =>
      cases count with
      | zero => rfl
      | succ count =>
          simp [berkowitzMoments, ih]

/-- The border row used by the Berkowitz step at trailing size `k`. -/
@[expose]
def berkowitzRow (A : Matrix R n n) (k : Nat) (hk : k + 1 <= n) : Vector R k :=
  let s := n - k - 1
  Hex.Vector.ofFn' fun j =>
    A[((s : Nat), n - k + j.val)]'(by simp only [s]; omega)

/-- The border column used by the Berkowitz step at trailing size `k`. -/
@[expose]
def berkowitzCol (A : Matrix R n n) (k : Nat) (hk : k + 1 <= n) : Vector R k :=
  let s := n - k - 1
  Hex.Vector.ofFn' fun i =>
    A[(n - k + i.val, (s : Nat))]'(by simp only [s]; omega)

/-- The Toeplitz first column for the Berkowitz step at trailing block size
`k + 1`: `1`, `-a`, and `-(row dot B^j col)` for `0 <= j < k`. -/
@[expose]
def berkowitzColumn (A : Matrix R n n) (k : Nat) (hk : k + 1 <= n) :
    Vector R (k + 2) :=
  let s := n - k - 1
  let a := A[((s : Nat), (s : Nat))]'(by simp only [s]; omega)
  let row := berkowitzRow A k hk
  let col := berkowitzCol A k hk
  let block := trailingBlock A k (by omega)
  let moments := (berkowitzMoments block row k col).toArray
  Hex.Vector.ofFn' fun i =>
    if h0 : i.val = 0 then
      1
    else if h1 : i.val = 1 then
      -a
    else
      moments[i.val - 2]'(by
        simp only [moments, List.size_toArray, length_berkowitzMoments]
        omega)

/-- The leading entry of every Berkowitz column is one. -/
@[simp, grind =]
theorem getElem_berkowitzColumn_zero (A : Matrix R n n) (k : Nat) (hk : k + 1 <= n) :
    (berkowitzColumn A k hk)[(0 : Fin (k + 2))] = 1 := by
  simp [berkowitzColumn]

/-- The second entry of a Berkowitz column is the negated newly exposed
diagonal entry. -/
@[simp, grind =]
theorem getElem_berkowitzColumn_one (A : Matrix R n n) (k : Nat) (hk : k + 1 <= n) :
    (berkowitzColumn A k hk)[(1 : Fin (k + 2))] =
      -A[(n - k - 1, n - k - 1)]'(by omega) := by
  simp [berkowitzColumn]

/-- Entries after the first two are the successive row--block--column moments. -/
theorem getElem_berkowitzColumn_add_two (A : Matrix R n n) (k : Nat)
    (hk : k + 1 <= n) (j : Fin k) :
    (berkowitzColumn A k hk)[(⟨j.val + 2, by omega⟩ : Fin (k + 2))] =
      (berkowitzMoments (trailingBlock A k (by omega))
        (berkowitzRow A k hk) k
        (berkowitzCol A k hk))[j.val]'(by
            rw [length_berkowitzMoments]
            exact j.isLt) := by
  simp [berkowitzColumn]

/-- One Berkowitz step, growing the descending coefficient vector from length
`k + 1` to length `k + 2`. -/
@[expose]
def berkowitzStep (A : Matrix R n n) (k : Nat) (hk : k + 1 <= n)
    (v : Vector R (k + 1)) : Vector R (k + 2) :=
  toeplitzMulVec (berkowitzColumn A k hk) v

/-- The descending coefficients for the characteristic polynomial of the
trailing `k x k` principal block of `A`. -/
@[expose]
def berkowitzAux (A : Matrix R n n) : (k : Nat) -> k <= n -> Vector R (k + 1)
  | 0, _ => #v[1]
  | k + 1, hk => berkowitzStep A k hk (berkowitzAux A k (by omega))

/-- The coefficients of the characteristic polynomial of `A` in descending
degree order: entry zero is the coefficient of `x^n`, and entry `n` is the
constant coefficient. -/
@[expose]
def berkowitz (A : Matrix R n n) : Vector R (n + 1) :=
  berkowitzAux A n (Nat.le_refl n)

/-- Every intermediate descending coefficient vector has leading entry one. -/
@[simp, grind =]
theorem berkowitzAux_zero (A : Matrix R n n) (k : Nat) (hk : k <= n) :
    (berkowitzAux A k hk)[(0 : Fin (k + 1))] = 1 := by
  induction k with
  | zero => rfl
  | succ k ih =>
      rw [berkowitzAux, berkowitzStep, getElem_toeplitzMulVec_zero,
        getElem_berkowitzColumn_zero, ih (by omega)]
      grind

/-- The leading coefficient produced by the Berkowitz recursion is one. -/
@[simp, grind =]
theorem berkowitz_zero (A : Matrix R n n) :
    (berkowitz A)[(0 : Fin (n + 1))] = 1 := by
  exact berkowitzAux_zero A n (Nat.le_refl n)

end Hex.Matrix
