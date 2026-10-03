/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexArith.ExtGcd
public meta import HexArith.ExtGcd
public meta import HexArith.Nat.ExtendedGcd
import Lean.Util.TestExtern

public section

/-!
Temporary coverage copied from leanprover/lean4#15160 at
`3c93b48cf60f7053b0a5b3f2ce646a5196c4fc2f`.
TODO(lean4#15160): after upgrading to a toolchain providing Nat.extendedGcd,
remove the copied upstream primitive tests; retain Hex's signed API checks.

Tests exact agreement of `Nat.extendedGcd`'s extern and Lean reference implementation, including
zero and equal inputs, half-size coefficient ties, scalar/bignum boundaries, signed coefficients,
and long Euclidean chains. Retained inputs also exercise the extern's borrowed-input ABI.
-/

test_extern Nat.extendedGcd 0 0
test_extern Nat.extendedGcd 0 19
test_extern Nat.extendedGcd 19 0
test_extern Nat.extendedGcd 19 19
test_extern Nat.extendedGcd 240 46
test_extern Nat.extendedGcd 46 240
test_extern Nat.extendedGcd 2 5
test_extern Nat.extendedGcd 5 2
test_extern Nat.extendedGcd 2 (2 ^ 32 - 1)
test_extern Nat.extendedGcd 2 (2 ^ 32 + 1)
test_extern Nat.extendedGcd 2 (2 ^ 32 + 3)
test_extern Nat.extendedGcd (2 ^ 64) (2 ^ 64)
test_extern Nat.extendedGcd 0 (2 ^ 128)
test_extern Nat.extendedGcd (2 ^ 128) 0
test_extern Nat.extendedGcd (2 ^ 64) (2 ^ 64 + 1)
test_extern Nat.extendedGcd (2 ^ 128 + 1) (2 ^ 64)
test_extern Nat.extendedGcd 65537 (2 ^ 128 + 1)
test_extern Nat.extendedGcd (2 ^ 128 + 1) 65537
-- A half-size tie after the initial zero quotient, with both operands heap-allocated.
test_extern Nat.extendedGcd ((2 ^ 128 + 1) * 2 ^ 64) (2 ^ 65)
test_extern Nat.extendedGcd (2 ^ 65) ((2 ^ 128 + 1) * 2 ^ 64)

private def reference (a b : Nat) : Nat.ExtendedGcdResult :=
  Nat.extendedGcd.go a 1 0 b 0 1

private def agrees (a b : Nat) : Bool :=
  decide (Nat.extendedGcd a b = reference a b)

#guard (List.range 129).all fun a => (List.range 129).all fun b => agrees a b

private def values : List Nat :=
  [0, 1, 2, 3, 6, 15, 46, 97, 240, 65535, 65536, 65537,
    2 ^ 31 - 1, 2 ^ 31, 2 ^ 31 + 1, 2 ^ 31 + 3,
    2 ^ 32 - 1, 2 ^ 32, 2 ^ 32 + 1, 2 ^ 32 + 3,
    2 ^ 63 - 1, 2 ^ 63, 2 ^ 63 + 1, 2 ^ 64 - 1, 2 ^ 64, 2 ^ 64 + 1,
    2 ^ 128 - 1, 2 ^ 128, 2 ^ 128 + 1, 2 ^ 256 - 1, 2 ^ 256 + 1]

#guard values.all fun a => values.all fun b => agrees a b

-- Scaling preserves the exceptional cases while forcing bignum operands and gcds.
#guard [1, 2 ^ 64, 2 ^ 128].all fun g =>
  (List.range 33).all fun a => (List.range 33).all fun b => agrees (a * g) (b * g)

private def fibPair (n : Nat) : Nat × Nat :=
  match n with
  | 0 => (0, 1)
  | n + 1 => let (a, b) := fibPair n; (b, a + b)

#guard [100, 256, 512, 1024].all fun n =>
  let (a, b) := fibPair n
  agrees a b && agrees b a

-- All three result fields require heap allocation in these examples.
#guard [256, 512].all fun n =>
  let (a, b) := fibPair n
  agrees (a * 2 ^ 128) (b * 2 ^ 128) && agrees (b * 2 ^ 128) (a * 2 ^ 128)

-- The operands remain live after the call, including when the gcd aliases an input.
#guard values.all fun a => values.all fun b =>
  let r := Nat.extendedGcd a b
  r.gcd == Nat.gcd a b && decide ((r.gcd : Int) = a * r.coeffA + b * r.coeffB)

-- These checks use the pure reference, which has no compiler rewrite, so
-- comparing it with the public API really exercises the new runtime route.
#guard (List.range 129).all fun i => (List.range 129).all fun j =>
  let a := (i : Int) - 64
  let b := (j : Int) - 64
  HexArith.Int.extGcd a b == Hex.pureIntExtGcd a b

#guard values.all fun a => values.all fun b =>
  [((a : Int), (b : Int)), (-(a : Int), (b : Int)),
   ((a : Int), -(b : Int)), (-(a : Int), -(b : Int))].all fun (x, y) =>
    HexArith.Int.extGcd x y == Hex.pureIntExtGcd x y

/-- info: (0, 1, 0) -/
#guard_msgs in #eval HexArith.Int.extGcd 0 0
/-- info: (19, 0, 1) -/
#guard_msgs in #eval HexArith.Int.extGcd 19 19
/-- info: (2, 1, 2) -/
#guard_msgs in #eval HexArith.Int.extGcd (-6) 4
/-- info: (1, 3, 4) -/
#guard_msgs in #eval HexArith.Int.extGcd 7 (-5)

example : Nat.extendedGcd 240 46 = ⟨2, -9, 47⟩ := by decide +kernel
example : Nat.extendedGcd 0 0 = ⟨0, 0, 1⟩ := by decide +kernel
example : HexArith.Int.extGcd 0 0 = (0, 1, 0) := by decide +kernel
example : HexArith.Int.extGcd (-6) 4 = (2, 1, 2) := by decide +kernel
example : HexArith.Int.extGcd 7 (-5) = (1, 3, 4) := by decide +kernel

/-- The compiled caller keeps its inputs live and checks a separate reference. -/
def main (args : List String) : IO Unit := do
  let inputs := values.map (· + args.length)
  for g in [1, 2 ^ 64] do
    for x in inputs do
      for y in inputs do
        let a := x * g
        let b := y * g
        unless agrees a b do
          throw <| IO.userError s!"extendedGcd disagrees on ({a}, {b})"
        for (m, n) in [((a : Int), (b : Int)), (-(a : Int), (b : Int)),
                       ((a : Int), -(b : Int)), (-(a : Int), -(b : Int))] do
          unless HexArith.Int.extGcd m n == Hex.pureIntExtGcd m n do
            throw <| IO.userError s!"signed extendedGcd disagrees on ({m}, {n})"
