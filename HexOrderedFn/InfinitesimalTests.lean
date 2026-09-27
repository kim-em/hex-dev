/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexOrderedFn.Infinitesimal

/-!
Concrete rational functions at successive infinitesimal levels for compiled tests.
-/

@[expose] public section

namespace Hex.OrderedFn.InfinitesimalTests

open scoped Hex.OrderedFn.Infinitesimal

abbrev First := RationalFn Rat
abbrev Second := RationalFn First

def epsilon : First := RationalFn.X
def delta : Second := RationalFn.X
def lift (a : First) : Second := RationalFn.C a

example : Infinitesimal.lowestIndex (DensePoly.ofCoeffs #[0, 0, -3, 1] : DensePoly Rat) = 2 :=
  by decide +kernel
example : Infinitesimal.lowestCoeff (DensePoly.ofCoeffs #[0, 0, -3, 1] : DensePoly Rat) = -3 :=
  by decide +kernel
example : Infinitesimal.sign orderSign (0 : First) = 0 := by decide +kernel
example : Infinitesimal.sign orderSign (epsilon - epsilon) = 0 := by decide +kernel
example : (0 : First) < epsilon := by decide +kernel

end Hex.OrderedFn.InfinitesimalTests
