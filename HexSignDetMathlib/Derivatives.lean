/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexSignDet.Thom
public import HexPolyMathlib.Interpret
public import Mathlib.Basic.Sign.Defs

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

variable [LinearOrder K]

include hn hm in
/-- A well-formed raw descriptor's executable query word is the formal
derivative-sign word at any point. -/
theorem RawDescriptor.querySigns {Ctx : Type w} (raw : RawDescriptor E Ctx)
    (hw : raw.wellFormed = true) (x : K) :
    raw.queries.map (fun q => (SignType.sign ((interpret f hz q).eval x) : Int)) =
      raw.indices.map (fun j =>
        (SignType.sign ((Polynomial.derivative^[j]
          (interpret f hz raw.head)).eval x) : Int)) := by
  simp only [RawDescriptor.wellFormed, Bool.and_eq_true, decide_eq_true_eq] at hw
  have hb : ∀ j ∈ raw.indices, 1 ≤ j ∧ j ≤ raw.head.natDegree := by
    intro j hj
    exact of_decide_eq_true (List.all_eq_true.mp hw.1.2 j hj)
  simp only [RawDescriptor.queries, List.map_map]
  apply List.map_congr_left
  intro j hj
  obtain ⟨hjpos, hjdeg⟩ := hb j hj
  have hlt : j - 1 < raw.head.natDegree := by omega
  have hindex : j - 1 < (derivativesFrom raw.head raw.head.natDegree).length := by
    rw [derivativesFrom_length]
    exact hlt
  simp only [Function.comp_apply, derivatives]
  rw [List.getElem?_eq_getElem hindex, Option.getD_some]
  rw [derivativesFrom_get f hz hn hm raw.head raw.head.natDegree (j - 1) hlt]
  simp only [Nat.sub_add_cancel hjpos]

end Hex.SignDet
