/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexMatrix.Submatrix

public section

/-!
Bordered leading minors used by Bareiss-style determinant arguments.
-/

namespace Hex

universe u

namespace Matrix

/-- Bordered Bareiss minor with the first `k` rows/columns and one extra
border row `i` and column `j`. For Bareiss applications `i` and `j` are in the
trailing part, but the constructor is total and leaves that side condition to
the invariant using it. -/
@[expose]
def borderedMinor (M : Matrix R n n) (k : Nat) (hk : k < n) (i j : Fin n) :
    Matrix R (k + 1) (k + 1) :=
  ofFn fun r c =>
    let rr : Fin n :=
      if hr : r.val < k then
        ⟨r.val, Nat.lt_trans hr hk⟩
      else
        i
    let cc : Fin n :=
      if hc : c.val < k then
        ⟨c.val, Nat.lt_trans hc hk⟩
      else
        j
    M[(rr, cc)]

/-- Interior-block case of the bordered-minor entry formula. -/
@[grind =] theorem borderedMinor_entry_lt_lt (M : Matrix R n n) (k : Nat) (hk : k < n)
    (i j : Fin n) (r c : Fin (k + 1)) (hr : r.val < k) (hc : c.val < k) :
    (borderedMinor M k hk i j)[r][c] =
      (let rr : Fin n := ⟨r.val, Nat.lt_trans hr hk⟩
       let cc : Fin n := ⟨c.val, Nat.lt_trans hc hk⟩
       M[(rr, cc)]) := by
  simp [borderedMinor, ofFn, hr, hc]

/-- Border-column case of the bordered-minor entry formula. -/
@[grind =] theorem borderedMinor_entry_lt_last (M : Matrix R n n) (k : Nat) (hk : k < n)
    (i j : Fin n) (r : Fin (k + 1)) (hr : r.val < k) :
    (borderedMinor M k hk i j)[r][Fin.last k] =
      (let rr : Fin n := ⟨r.val, Nat.lt_trans hr hk⟩
       M[rr][j]) := by
  simp [borderedMinor, ofFn, hr]

/-- Border-row case of the bordered-minor entry formula. -/
@[grind =] theorem borderedMinor_entry_last_lt (M : Matrix R n n) (k : Nat) (hk : k < n)
    (i j : Fin n) (c : Fin (k + 1)) (hc : c.val < k) :
    (borderedMinor M k hk i j)[Fin.last k][c] =
      (let cc : Fin n := ⟨c.val, Nat.lt_trans hc hk⟩
       M[i][cc]) := by
  simp [borderedMinor, ofFn, hc]

/-- Corner case of the bordered-minor entry formula. -/
@[grind =] theorem borderedMinor_entry_last_last (M : Matrix R n n) (k : Nat) (hk : k < n)
    (i j : Fin n) :
    (borderedMinor M k hk i j)[Fin.last k][Fin.last k] = M[i][j] := by
  simp [borderedMinor, ofFn]

/-- The top-left `k × k` block of a bordered minor is the leading prefix of the
source matrix. -/
theorem principalSubmatrix_borderedMinor_eq_principalSubmatrix (M : Matrix R n n) (k : Nat)
    (hk : k < n) (i j : Fin n) :
    principalSubmatrix (borderedMinor M k hk i j) k (Nat.le_succ k) =
      principalSubmatrix M k (Nat.le_of_lt hk) := by
  ext r _hr c _hc
  simp [principalSubmatrix, borderedMinor, ofFn]

/-- The top-left `(k + 1) × (k + 1)` block of the next bordered minor is the
current bordered minor whose extra row/column are the `k`-th source row/column. -/
theorem principalSubmatrix_borderedMinor_succ_eq_borderedMinor (M : Matrix R n n)
    (k : Nat) (hk : k < n) (hnext : k + 1 < n) (i j : Fin n) :
    principalSubmatrix (borderedMinor M (k + 1) hnext i j) (k + 1)
        (Nat.le_succ (k + 1)) =
      borderedMinor M k hk ⟨k, hk⟩ ⟨k, hk⟩ := by
  ext r _hr c _hc
  by_cases hrk : r < k <;> by_cases hck : c < k
  · simp [principalSubmatrix, borderedMinor, ofFn, hrk, hck]
  · have hc_eq : c = k := by omega
    simp [principalSubmatrix, borderedMinor, ofFn, hrk, hc_eq]
  · have hr_eq : r = k := by omega
    simp [principalSubmatrix, borderedMinor, ofFn, hck, hr_eq]
  · have hr_eq : r = k := by omega
    have hc_eq : c = k := by omega
    simp [principalSubmatrix, borderedMinor, ofFn, hr_eq, hc_eq]

end Matrix

end Hex
