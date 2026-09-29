/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRealClosureMathlib.Ambient

public section

open Hex.RealClosure
open scoped Hex.OrderedFn.Infinitesimal

example : ∃ s : (Ambient.infinitesimal Rat).Carrier,
    0 < s ∧ s ^ 2 = Ambient.nativeHom HexRationalFnMathlib.ratField_eq
      (Ambient.infinitesimal Rat) (Hex.RationalFn.X : Hex.RationalFn Rat) ∧
    Ambient.nativeHom HexRationalFnMathlib.ratField_eq (Ambient.infinitesimal Rat)
      (Hex.RationalFn.X : Hex.RationalFn Rat) < s ∧ s < 1 := by
  simp only [Ambient.nativeHom_X]
  exact Ambient.exists_sqrt_X (Ambient.infinitesimal Rat)

example (f : Hex.RationalFn Rat) :
    Hex.OrderedFn.Infinitesimal.sign Hex.OrderedFn.orderSign f =
      (SignType.sign (Ambient.nativeHom HexRationalFnMathlib.ratField_eq
        (Ambient.infinitesimal Rat) f) : Int) :=
  Ambient.nativeHom_sign HexRationalFnMathlib.ratField_eq (Ambient.infinitesimal Rat) f
