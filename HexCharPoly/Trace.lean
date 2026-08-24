/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexCharPoly.CharPoly

public section

/-!
The executable matrix trace and the subleading characteristic-polynomial
coefficient.
-/

namespace Hex.Matrix

universe u

variable {R : Type u} [Lean.Grind.CommRing R] [DecidableEq R] {n : Nat}

/-- Sum the last `k` diagonal entries, from the bottom-right corner upward. -/
@[expose]
def traceFold (A : Matrix R n n) (k : Nat) (hk : k <= n) : R :=
  (List.finRange k).foldl (fun acc i =>
    let j : Fin n := ⟨n - i.val - 1, by omega⟩
    acc + A[(j, j)]) 0

omit [DecidableEq R] in
/-- Extending the trailing diagonal fold adds the newly exposed diagonal
entry. -/
theorem traceFold_succ (A : Matrix R n n) (k : Nat) (hk : k + 1 <= n) :
    traceFold A (k + 1) hk =
      traceFold A k (by omega) + A[(n - k - 1, n - k - 1)]'(by omega) := by
  unfold traceFold
  rw [List.finRange_succ_last, List.foldl_append, List.foldl_map]
  simp

/-- The sum of the diagonal entries of a square matrix. -/
@[expose]
def trace (A : Matrix R n n) : R :=
  traceFold A n (Nat.le_refl n)

/-- Entry one of an intermediate Berkowitz vector is the negated trace of the
corresponding trailing principal block. -/
theorem berkowitzAux_one (A : Matrix R n n) (k : Nat) (hk : k <= n)
    (hpos : 0 < k) (i : Fin (k + 1)) (hi : i.val = 1) :
    (berkowitzAux A k hk)[i] = -traceFold A k hk := by
  induction k with
  | zero => omega
  | succ k ih =>
      cases k with
      | zero =>
          rw [berkowitzAux, berkowitzStep,
            getElem_toeplitzMulVec_one_base_of_val (hi := hi),
            getElem_berkowitzColumn_one, berkowitzAux_zero,
            traceFold_succ A 0 hk]
          simp [traceFold]
          grind
      | succ j =>
          rw [berkowitzAux, berkowitzStep,
            getElem_toeplitzMulVec_one_succ_of_val (hi := hi),
            getElem_berkowitzColumn_one, getElem_berkowitzColumn_zero,
            berkowitzAux_zero,
            ih (by omega) (by omega) (1 : Fin (j + 2)) rfl,
            traceFold_succ A (j + 1) hk]
          grind

/-- The coefficient of `x^(n-1)` is the negative trace. -/
theorem coeff_charPoly_pred (A : Matrix R n n) (hn : 0 < n) :
    (charPoly A).coeff (n - 1) = -trace A := by
  rw [coeff_charPoly A (by omega)]
  have hidx : n - (n - 1) = 1 := by omega
  have haux := berkowitzAux_one A n (Nat.le_refl n) hn
    (⟨n - (n - 1), by omega⟩ : Fin (n + 1)) hidx
  change (berkowitz A)[(⟨n - (n - 1), by omega⟩ : Fin (n + 1))] = -trace A
  unfold berkowitz trace
  exact haux

end Hex.Matrix
