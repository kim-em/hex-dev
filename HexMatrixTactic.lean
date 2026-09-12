/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexMatrixTactic.Result
public meta import HexMatrixTactic.Protocol
public import HexMatrixTactic.Protocol
public meta import HexMatrixTactic.Model
public import HexMatrixTactic.Model
public meta import HexMatrixTactic.Syntax
public import HexMatrixTactic.Syntax
public meta import HexMatrixTactic.Det
public import HexMatrixTactic.Det
public meta import HexMatrixTactic.CharPoly
public import HexMatrixTactic.CharPoly

public section

/-!
The `HexMatrixTactic` library provides the proof-producing `det` and
`char_poly` frontends for executable Hex matrices: the term forms `det% A` and
`char_poly A` return a `Hex.MatrixTactic.Certified` record, and the tactics of
the same names close goals about `Hex.Matrix.bareiss` and
`Hex.Matrix.charPoly`.  The Mathlib companion `HexMatrixTacticMathlib` accepts
Mathlib matrices.  Rank tactics live with their algorithm library, `HexRank`.
-/
