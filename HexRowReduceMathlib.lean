/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexRowReduceMathlib.RankSpanNullspace
public import HexRowReduceMathlib.InverseSolve

public section

/-!
The `HexRowReduceMathlib` library is the Mathlib bridge for `hex-row-reduce`. It
connects the executable RREF / rank / span / nullspace machinery to Mathlib's
linear-algebra `rank`, span, and kernel definitions. Field inversion agrees
with the nonsingular inverse; solving characterises the complete affine
solution set and its inconsistency certificates. These results build on the
base matrix equivalence in `HexMatrixMathlib`.
-/
