/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexMvGcd.Divide
public import HexMvPoly.Recursive

@[expose] public section
set_option backward.proofsInPublic true

/-!
The constant embedding associated to the arity-dropping univariate view.

Keeping this operation next to the gcd code avoids adding a second recursive
view to `hex-mv-poly`: being constant in the selected variable is represented
by applying `ofUnivariate` to a dense constant polynomial.
-/

namespace Hex.MvPoly

universe u

variable {n : Nat} {R : Type u}
  {cmp : Mono (n + 1) → Mono (n + 1) → Ordering}
  {cmp' : Mono n → Mono n → Ordering}
  [Std.TransCmp cmp] [Std.LawfulEqCmp cmp]
  [Std.TransCmp cmp'] [Std.LawfulEqCmp cmp']
  [Lean.Grind.CommRing R] [DecidableEq R] [BEq R] [LawfulBEq R]

/-- Embed a polynomial in the remaining variables as a polynomial constant in
the selected variable. -/
def constIn (i : Fin (n + 1)) (cmp' : Mono n → Mono n → Ordering)
    [Std.TransCmp cmp'] [Std.LawfulEqCmp cmp']
    (c : MvPoly n R cmp') : MvPoly (n + 1) R cmp :=
  ofUnivariate (cmp := cmp) i cmp' (DensePoly.C c)

/-- The recursive view of a constant embedding is a dense constant. -/
@[simp] theorem toUnivariate_constIn (i : Fin (n + 1))
    (c : MvPoly n R cmp') :
    toUnivariate i cmp' (constIn (cmp := cmp) i cmp' c) = DensePoly.C c := by
  exact toUnivariate_ofUnivariate i (DensePoly.C c)

/-- The degree-`k` recursive coefficient of `constIn c` is `c` at zero and
zero elsewhere. -/
@[simp] theorem coeff_constIn (i : Fin (n + 1))
    (c : MvPoly n R cmp') (k : Nat) :
    (toUnivariate i cmp' (constIn (cmp := cmp) i cmp' c)).coeff k =
      if k = 0 then c else 0 := by
  rw [toUnivariate_constIn]
  exact DensePoly.coeff_C c k

/-- Constant embedding preserves zero. -/
@[simp] theorem constIn_zero (i : Fin (n + 1)) :
    constIn (R := R) (cmp := cmp) i cmp' 0 = 0 := by
  sorry

/-- Constant embedding preserves one. -/
@[simp] theorem constIn_one (i : Fin (n + 1)) :
    constIn (R := R) (cmp := cmp) i cmp' 1 = 1 := by
  sorry

/-- Constant embedding preserves addition. -/
theorem constIn_add (i : Fin (n + 1)) (a b : MvPoly n R cmp') :
    constIn (cmp := cmp) i cmp' (a + b) =
      constIn i cmp' a + constIn i cmp' b := by
  sorry

/-- Constant embedding preserves multiplication. -/
theorem constIn_mul (i : Fin (n + 1)) (a b : MvPoly n R cmp') :
    constIn (cmp := cmp) i cmp' (a * b) =
      constIn i cmp' a * constIn i cmp' b := by
  sorry

/-- Constant embedding is injective. -/
theorem constIn_injective (i : Fin (n + 1)) :
    Function.Injective (constIn (R := R) (cmp := cmp) i cmp') := by
  intro a b h
  have hview := congrArg (toUnivariate i cmp') h
  rw [toUnivariate_constIn, toUnivariate_constIn] at hview
  have hcoeff := congrArg (fun p : DensePoly (MvPoly n R cmp') => p.coeff 0) hview
  simpa using hcoeff

/-- The degree in the selected variable, with `none` distinguishing zero from
a constant polynomial. -/
def degreeIn? (i : Fin (n + 1)) (cmp' : Mono n → Mono n → Ordering)
    [Std.TransCmp cmp'] [Std.LawfulEqCmp cmp']
    (p : MvPoly (n + 1) R cmp) : Option Nat :=
  (toUnivariate i cmp' p).degree?

/-- Coefficient slice at a named degree in the selected variable. -/
def coeffIn (i : Fin (n + 1)) (cmp' : Mono n → Mono n → Ordering)
    [Std.TransCmp cmp'] [Std.LawfulEqCmp cmp']
    (k : Nat) (p : MvPoly (n + 1) R cmp) : MvPoly n R cmp' :=
  (toUnivariate i cmp' p).coeff k

end Hex.MvPoly
