/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexBasic.ArrayDecEq
public import HexBasic.OfFn

open scoped Hex   -- kernel-reducible Array/Vector equality; see HexBasic.ArrayDecEq

public section

/-!
Regression tests for the three module-system exposure gaps worked around by
the `HexBasic.ArrayDecEq` and `HexBasic.OfFn` modules.

These have to live in a *separate module* from the definitions they exercise:
the defect is that a callee's body is unavailable across a module boundary, so
a same-module test passes whether or not the workaround is present and proves
nothing. Without the workarounds, the examples fail against core's
{name}`Array.instDecidableEq`, {name}`Vector`'s derived instance, or
{name}`Array.ofFn`.
-/

namespace Hex.ModuleBoundaryTests

/-! # `Array` equality, both sides nonempty -/

example : (#[0, 1] : Array Nat) ≠ #[1] := by decide
example : (#[2, 3] : Array Nat) = #[2, 3] := by decide
example : (#[1, 2, 3] : Array Nat) ≠ #[1, 2, 4] := by decide +kernel
example : decide ((#[0, 1] : Array Nat) = #[0, 1]) = true := by rfl

/-! Cases that reduced even before the workaround, kept so a regression in the
empty/nonempty branches is caught too. -/

example : (#[] : Array Nat) = #[] := by decide
example : (#[] : Array Nat) ≠ #[1] := by decide

/-! # `Vector` equality, whose core instance is derived -/

example : (#v[0, 1, 2] : Vector Nat 3) ≠ #v[0, 0, 0] := by decide
example : (#v[0, 1, 2] : Vector Nat 3) = #v[0, 1, 2] := by decide +kernel

/-! # `ofFn` -/

example : (Array.ofFn' (n := 3) (fun i => i.val)).size = 3 := by decide
example : Array.ofFn' (n := 3) (fun i => i.val) = #[0, 1, 2] := by decide
example : Vector.ofFn' (n := 4) (fun i => i.val * 2) = #v[0, 2, 4, 6] := by
  decide +kernel

/-! # Combined tabulation and equality

An exponent vector built with `ofFn'` and compared for equality. -/

example :
    (Vector.ofFn' (n := 3) (fun j => if j = 1 then 1 else 0) : Vector Nat 3)
      ≠ Vector.ofFn' (fun j => if j = 2 then 1 else 0) := by
  decide +kernel

end Hex.ModuleBoundaryTests
