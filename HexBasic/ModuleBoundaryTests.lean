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
`HexBasic.ArrayDecEq` and `HexBasic.OfFn`.

These have to live in a *separate module* from the definitions they exercise:
the defect is that a callee's body is unavailable across a module boundary, so
a same-module test passes whether or not the workaround is present and proves
nothing. Every example below fails against core's `Array.instDecidableEq`,
`Vector`'s derived instance, or `Array.ofFn`.

Delete alongside the workarounds once
[leanprover/lean4#14270](https://github.com/leanprover/lean4/pull/14270) lands,
after first re-pointing them at the core definitions and confirming they still
pass. That is the check that the upstream fix actually works.
-/

namespace Hex.ModuleBoundaryTests

/-! ## `Array` equality, both sides nonempty -/

example : (#[0, 1] : Array Nat) ≠ #[1] := by decide
example : (#[2, 3] : Array Nat) = #[2, 3] := by decide
example : (#[1, 2, 3] : Array Nat) ≠ #[1, 2, 4] := by decide +kernel
example : decide ((#[0, 1] : Array Nat) = #[0, 1]) = true := by rfl

/-! Cases that reduced even before the workaround, kept so a regression in the
empty/nonempty branches is caught too. -/

example : (#[] : Array Nat) = #[] := by decide
example : (#[] : Array Nat) ≠ #[1] := by decide

/-! ## `Vector` equality, whose core instance is derived -/

example : (#v[0, 1, 2] : Vector Nat 3) ≠ #v[0, 0, 0] := by decide
example : (#v[0, 1, 2] : Vector Nat 3) = #v[0, 1, 2] := by decide +kernel

/-! ## `ofFn` -/

example : (Array.ofFn' (n := 3) (fun i => i.val)).size = 3 := by decide
example : Array.ofFn' (n := 3) (fun i => i.val) = #[0, 1, 2] := by decide
example : Vector.ofFn' (n := 4) (fun i => i.val * 2) = #v[0, 2, 4, 6] := by
  decide +kernel

/-! ## The combination, which is the shape `hex-mv-poly` will use: an exponent
vector built with `ofFn'` and compared for equality. -/

example :
    (Vector.ofFn' (n := 3) (fun j => if j = 1 then 1 else 0) : Vector Nat 3)
      ≠ Vector.ofFn' (fun j => if j = 2 then 1 else 0) := by
  decide +kernel

end Hex.ModuleBoundaryTests
