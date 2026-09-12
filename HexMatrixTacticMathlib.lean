/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public meta import HexMatrixTacticMathlib.Literal
public import HexMatrixTacticMathlib.Literal
public meta import HexMatrixTacticMathlib.Det
public import HexMatrixTacticMathlib.Det
public meta import HexMatrixTacticMathlib.CharPoly
public import HexMatrixTacticMathlib.CharPoly

public section

/-!
The `HexMatrixTacticMathlib` library extends the `det` and `char_poly`
frontends of `HexMatrixTactic` to closed Mathlib matrices: the term forms
return `Hex.MatrixTactic.Certified` records about `Matrix.det` and
`Matrix.charpoly`, the tactics close the corresponding goals, and the opt-in
`hex_norm_det` simproc composes the Hex determinant with Mathlib's `norm_det`
as its fallback.
-/
