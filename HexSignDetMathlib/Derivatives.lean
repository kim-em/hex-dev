/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexSignDet.Thom
public import HexPolyMathlib.Interpret

public section

namespace Hex.SignDet

open HexPolyMathlib.Interpret

variable {E : Type u} {K : Type v} [Zero E] [DecidableEq E] [NatCast E] [Mul E]
variable [Field K] [DecidableEq K]
variable (f : E → K) (hz : ∀ a, f a = 0 ↔ a = 0)
variable (hn : ∀ n : Nat, f (n : E) = (n : K)) (hm : ∀ a b, f (a * b) = f a * f b)

include hn hm in
/-- Every emitted derivative is exactly the formal iterated derivative under
interpretation. No monic normalization or sign-changing scale is inserted. -/
theorem derivativesFrom_get (p : DensePoly E) (n i : Nat) (hi : i < n) :
    interpret f hz ((derivativesFrom p n)[i]'(by rw [derivativesFrom_length]; exact hi)) =
      Polynomial.derivative^[i + 1] (interpret f hz p) := by
  induction n generalizing p i with
  | zero => omega
  | succ n ih =>
    cases i with
    | zero => simp [derivativesFrom, interpret_derivative f hz hn hm]
    | succ i =>
      simp only [derivativesFrom, List.getElem_cons_succ,
        ih p.derivative i (by omega), interpret_derivative f hz hn hm]
      exact (Function.iterate_succ_apply Polynomial.derivative (i + 1) (interpret f hz p)).symm

end Hex.SignDet
