/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexSturmMathlib
public meta import HexSturm.Basic

public section
namespace HexSturmMathlib.ReplayTests
open Hex DensePoly

@[expose] def p : DensePoly Rat := ofCoeffs #[-1, 0, 1]
@[expose] def x : DensePoly Rat := ofCoeffs #[0, 1]

/-- A fully literal rational certificate, checked without invoking a producer. -/
@[expose] def literalChain : QueryChain Rat where
  chain := #[p, x, 1]
  degrees := #[2, 1, 0]
  initial := ⟨1, 0, 2⟩
  steps := #[⟨1, x, 1⟩]
  terminal := some (1, x)

@[expose] def literal : QueryReplay Rat Rat Nat where
  context := 7
  head := p
  queryPoly := 1
  lower := .finite (-2)
  upper := .finite 2
  squarefree := literalChain
  remainders := literalChain
  lowerSigns := #[1, -1, 1]
  upperSigns := #[1, 1, 1]
  lowerVariations := 2
  upperVariations := 0
  value := 2

end HexSturmMathlib.ReplayTests
