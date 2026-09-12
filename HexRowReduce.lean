/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexRowReduce.RowEchelon
public import HexRowReduce.Pivot
public import HexRowReduce.Loop
public import HexRowReduce.Span
public import HexRowReduce.Nullspace
public import HexRowReduce.Api
public import HexRowReduce.Inverse
public import HexRowReduce.Solve

public section

/-!
The `HexRowReduce` library: executable row reduction for the dense
matrices of `HexMatrix`. It re-exports the elementary-operation algebra and
echelon contracts (`RowEchelon`), the pivot search and column elimination
(`Pivot`), the `rowReduce` loop and its correctness (`Loop`), and the row-span
and nullspace APIs (`Span`, `Nullspace`, `Api`), and field inversion and complete
affine solving with inconsistency certificates (`Inverse`, `Solve`).
-/
