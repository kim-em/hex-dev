/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexTruncatedSeries.Inverse

public section

/-!
Kernel-reduction regressions for truncated series.

These examples intentionally live downstream of the executable definitions.
They fail if tabulation, coefficient access, convolution, arithmetic, or
equality becomes opaque across a module boundary.
-/

namespace Hex.TSeries.ModuleBoundaryTests

open scoped Hex

private def a : TSeries Int 8 := ofFn fun i => if i = 0 then 1 else i
private def b : TSeries Int 8 := ofFn fun i => if i < 3 then i + 1 else 0

example : a * b = ofFn fun i =>
    match i with
    | 0 => 1
    | 1 => 3
    | 2 => 7
    | 3 => 10
    | 4 => 16
    | 5 => 22
    | 6 => 28
    | _ => 34 := by
  decide +kernel

example : mulUpTo 4 a b = ofFn fun i =>
    match i with
    | 0 => 1
    | 1 => 3
    | 2 => 7
    | 3 => 10
    | _ => 0 := by
  decide +kernel

example : Nat.log2 8 = 3 := by decide +kernel

example : steps 8 = 3 := by decide +kernel

private def oneMinusX : TSeries Int 8 :=
  ofFn fun i => if i = 0 then 1 else if i = 1 then -1 else 0

example : invOfUnit oneMinusX 1 = ofFn fun _ => 1 := by
  decide +kernel

end Hex.TSeries.ModuleBoundaryTests
