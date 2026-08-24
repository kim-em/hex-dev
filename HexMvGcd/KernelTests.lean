/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexMvGcd.Gauss
public meta import HexMvGcd.Gauss
public meta import HexMvPoly.Basic
public meta import HexMvPoly.Ring

public section

/-!
Kernel-facing examples for the checked multivariate division API.
-/

namespace Hex.MvPoly.KernelTests

open Hex
open scoped Hex

abbrev P := MvPoly 2 Int Mono.lex
abbrev P1 := MvPoly 1 Int Mono.lex

@[expose] def x : P := X 0
@[expose] def y : P := X 1
@[expose] def left : P := x + y
@[expose] def right : P := x - y
@[expose] def product : P := left * right

#guard divExact? product left == some right

#guard divExact? product (left + C 1) == none

example : divExact? product 0 = none := by
  decide +kernel

example : divMod product 0 = (0, product) := by
  decide +kernel

#guard divMod product left == (right, 0)

@[expose] def lower : P1 := X 0 + C 2

#guard toUnivariate 0 Mono.lex
    (constIn (cmp := Mono.lex) 0 Mono.lex lower) == DensePoly.C lower

#guard polyIsUnit (C (-1) : P)

#guard !polyIsUnit x

#guard scalarContent left == 1

#guard polyNormalize (-left) == left

example : Nonempty (CoeffGcd ([12, 18, 30] : List Int)) :=
  coeffGcd_nonempty _

end Hex.MvPoly.KernelTests
