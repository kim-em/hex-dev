/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexSignDet.Reencode
public import HexSturmMathlib.Domain

public section

namespace Hex.SignDet

open HexPolyMathlib.Interpret

variable {E : Type u} {K : Type v} [Zero E] [DecidableEq E] [One E] [Sub E]
variable [Field K] [DecidableEq K]
variable (f : E → K) (hz : ∀ a, f a = 0 ↔ a = 0)
variable (h1 : f (1 : E) = 1) (hs : ∀ a b, f (a - b) = f a - f b)

include h1 hs in
/-- The actual endpoint query evaluates to the strict-bound difference,
including on noncanonical coefficient representations. -/
theorem endpoint_eval (b : E) (a : K) :
    (interpret f hz (DensePoly.ofCoeffs #[0, 1] - DensePoly.C b)).eval a = a - f b := by
  have h0 := (hz (0 : E)).mpr rfl
  have hx : interpret f hz (DensePoly.ofCoeffs #[0, 1]) = Polynomial.X := by
    ext i
    simp only [coeff_interpret, DensePoly.coeff_ofCoeffs]
    cases i with
    | zero => simp [h0]
    | succ i => cases i with
      | zero => simp [h1]
      | succ i =>
        simp [Polynomial.coeff_X]
        exact (hz _).mpr rfl
  rw [interpret_sub f hz hs, hx, interpret_C, Polynomial.eval_sub,
    Polynomial.eval_X, Polynomial.eval_C]

variable [LinearOrder K] [IsStrictOrderedRing K]

include h1 hs in
/-- The lower endpoint condition is strict, so endpoint roots are excluded. -/
theorem endpoint_lower (b : E) (a : K) :
    Sturm.orderSign ((interpret f hz (DensePoly.ofCoeffs #[0, 1] - DensePoly.C b)).eval a) = 1 ↔
      f b < a := by
  rw [endpoint_eval f hz h1 hs, (HexSturmMathlib.orderSign_spec _).1, sub_pos]

include h1 hs in
/-- The upper endpoint uses the negative sign of the same difference. -/
theorem endpoint_upper (b : E) (a : K) :
    Sturm.orderSign ((interpret f hz (DensePoly.ofCoeffs #[0, 1] - DensePoly.C b)).eval a) = -1 ↔
      a < f b := by
  rw [endpoint_eval f hz h1 hs]
  obtain ⟨_, hn, _, hlo, _⟩ := HexSturmMathlib.orderSign_spec (a - f b)
  constructor
  · intro h
    exact sub_lt_zero.mp (hn.mp (by omega))
  · intro h
    have hh := hn.mpr (sub_lt_zero.mpr h)
    omega

end Hex.SignDet
