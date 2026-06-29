/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexRowReduceMathlib.RankSpanNullspace

public section

/-!
The `HexRowReduceMathlib` library is the Mathlib bridge for `hex-row-reduce`. It
connects the executable RREF / rank / span / nullspace machinery to Mathlib's
linear-algebra `rank`, span, and kernel definitions, building on the base
matrix equivalence in `HexMatrixMathlib`.
-/
