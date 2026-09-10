/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexBasic.ArrayDecEq
public import HexBasic.ExtTreeMap
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

The final section also checks that the exposed `ExtTreeMap` merge/traversal
closure remains kernel-reducible after crossing a module boundary; retain it
when the array/vector workarounds are eventually removed.
-/

namespace Hex.ModuleBoundaryTests

/-! # `Array.map` (core implementation loop is not exposed) -/

example : (Hex.Array.map' (fun w => w + 1) #[1, 2]) = #[2, 3] := by decide
example : (Hex.Array.map' (fun w => w * 2) #[3]).toList = [6] := by
  decide +kernel
example : decide ((Hex.Array.map' (fun w => w + 1) #[0, 1]) = #[1, 2]) =
    true := by rfl

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

/-! # `zipWith` -/

example : Array.zipWith' (· + ·) #[1, 2, 3] #[10, 20] = #[11, 22] := by decide +kernel

/-! # Combined tabulation and equality

An exponent vector built with `ofFn'` and compared for equality. -/

example :
    (Vector.ofFn' (n := 3) (fun j => if j = 1 then 1 else 0) : Vector Nat 3)
      ≠ Vector.ofFn' (fun j => if j = 2 then 1 else 0) := by
  decide +kernel

/-! # `ExtTreeMap` joint traversal and size-biased merge -/

example :
    Std.ExtTreeMap.foldl₂
        (fun acc key left right => acc ++ [(key, left, right)])
        []
        (Std.ExtTreeMap.ofList [(0, 10), (2, 12)] compare)
        (Std.ExtTreeMap.ofList [(1, 21), (2, 22), (3, 23)] compare) =
      [(0, some 10, none), (1, none, some 21), (2, some 12, some 22),
        (3, none, some 23)] := by
  decide +kernel

/-- Joint traversal also drains a nonempty left tail after the right side is
exhausted. -/
example :
    Std.ExtTreeMap.foldl₂
        (fun acc key left right => acc ++ [(key, left, right)])
        []
        (Std.ExtTreeMap.ofList [(0, 10), (5, 15)] compare)
        (Std.ExtTreeMap.ofList [(1, 21)] compare) =
      [(0, some 10, none), (1, none, some 21), (5, some 15, none)] := by
  decide +kernel

/-- The left value stays first when the left map is smaller. -/
example :
    (Std.ExtTreeMap.mergeWith? (fun _ left _ => some left)
      (Std.ExtTreeMap.ofList [(1, 10)] compare)
      (Std.ExtTreeMap.ofList [(1, 20), (2, 20)] compare))[1]? = some 10 := by
  decide +kernel

/-- The left value stays first when the right map is smaller. -/
example :
    (Std.ExtTreeMap.mergeWith? (fun _ left _ => some left)
      (Std.ExtTreeMap.ofList [(0, 10), (1, 10)] compare)
      (Std.ExtTreeMap.ofList [(1, 20)] compare))[1]? = some 10 := by
  decide +kernel

end Hex.ModuleBoundaryTests
