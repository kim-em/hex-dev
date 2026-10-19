/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexRowReduceTheory.RankSpanNullspace
public import HexRowReduceTheory.InverseSolve
public import HexRowReduceTheory.Kernel
public import HexRowReduceTheory.Tactic

public section

/-!
The `HexRowReduceTheory` library is the theory companion of `hex-row-reduce`. It
connects the executable RREF / rank / span / nullspace machinery to Mathlib's
linear-algebra `rank`, span, and kernel definitions. Field inversion agrees
with the nonsingular inverse; solving characterises the complete affine
solution set and its inconsistency certificates. These results build on the
base matrix equivalence in `HexMatrixTheory`.
-/
