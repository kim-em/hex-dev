/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexResultantMathlib.Chain
public import HexResultantMathlib.Sylvester

public section

/-!
Bivariate specialization laws for executable elimination.
-/
namespace Hex.DensePoly

universe u

variable {R : Type u}

/-- Specializing the coefficient variable after elimination agrees with the
formal-degree Mathlib resultant of the specialized inputs. -/
theorem eval_resultant [CommRing R] [IsDomain R] [DecidableEq R]
    [Div R] [Hex.ExactDivLaws R]
    (f g : DensePoly (DensePoly R)) (a : R) :
    eval (resultant f g) a =
      Polynomial.resultant (specialize f a) (specialize g a)
        (m := f.degree?.getD 0) (n := g.degree?.getD 0) := by
  sorry

/-- The specialization law at default Mathlib degrees when neither outer
leading coefficient vanishes. -/
theorem eval_resultant_default
    [CommRing R] [IsDomain R] [DecidableEq R]
    [Div R] [Hex.ExactDivLaws R]
    (f g : DensePoly (DensePoly R)) (a : R)
    (hf : eval f.leadingCoeff a ≠ 0) (hg : eval g.leadingCoeff a ≠ 0) :
    eval (resultant f g) a =
      Polynomial.resultant (specialize f a) (specialize g a) := by
  sorry

/-- A common bivariate zero forces the specialized eliminant to vanish. -/
theorem eval_resultant_eq_zero_of_common_root
    [CommRing R] [IsDomain R] [DecidableEq R]
    [Div R] [Hex.ExactDivLaws R]
    (f g : DensePoly (DensePoly R)) (a b : R)
    (hfb : evalBivariate f a b = 0) (hgb : evalBivariate g a b = 0) :
    eval (resultant f g) a = 0 := by
  sorry

end Hex.DensePoly
