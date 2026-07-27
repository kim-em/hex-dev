/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import Hex.Conformance.Emit
import HexResultant

/-!
Deterministic JSONL fixtures for the `HexResultant` external oracle profile.

The stream contains exactly the SPEC's 30 degree-10 integer-polynomial pairs,
generated from seed `0xC0FFEE` by a fixed 64-bit LCG. Each leading coefficient
is forced nonzero. For every original pair the driver emits both its resultant
and the discriminant of the left input. The companion oracle recomputes these
values independently with python-flint and cypari2/PARI.
-/

namespace Hex.ResultantEmit

open Hex.Conformance.Emit
open Hex Hex.DensePoly

private def lib : String := "HexResultant"

private def initialSeed : UInt64 :=
  0xC0FFEE

private def nextSeed (seed : UInt64) : UInt64 :=
  seed * 6364136223846793005 + 1442695040888963407

private structure PolyState where
  seed : UInt64
  coeffs : Array Int

/-- Generate one dense integer polynomial of exact degree `degree`. -/
private def randomPoly (degree : Nat) (seed : UInt64) : List Int × UInt64 :=
  let state := (Array.range (degree + 1)).foldl
    (fun state i =>
      let seed := nextSeed state.seed
      let raw := (Int.ofNat (seed.toNat % 21)) - 10
      let coeff := if i = degree && raw = 0 then 1 else raw
      { seed := seed, coeffs := state.coeffs.push coeff })
    ({ seed := seed, coeffs := #[] } : PolyState)
  (state.coeffs.toList, state.seed)

private structure Case where
  id : String
  left : List Int
  right : List Int

private structure CaseState where
  seed : UInt64
  cases : Array Case

/-- The committed seed's 30 degree-10 pairs. -/
private def cases : Array Case :=
  ((Array.range 30).foldl
    (fun state i =>
      let (left, seed) := randomPoly 10 state.seed
      let (right, seed) := randomPoly 10 seed
      { seed := seed
        cases := state.cases.push
          { id := "random/deg10/" ++ toString i
            left := left
            right := right } })
    ({ seed := initialSeed, cases := #[] } : CaseState)).cases

private def emitCase (c : Case) : IO Unit := do
  emitPolyFixture lib (c.id ++ "/left") c.left
  emitPolyFixture lib (c.id ++ "/right") c.right
  let left : DensePoly Int := ofList c.left
  let right : DensePoly Int := ofList c.right
  emitResult lib c.id "resultant" (toString (resultant left right))
  emitResult lib c.id "disc_left" (toString (disc left))

end Hex.ResultantEmit

open Hex.ResultantEmit in
def main : IO Unit := do
  for c in cases do
    emitCase c
