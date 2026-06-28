/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import HexBerlekampZassenhaus.Basic

open Hex

private def zp (cs : Array Int) : ZPoly := DensePoly.ofCoeffs cs

/-- (x-1)(x-2)...(x-n) -/
private def splitProduct (n : Nat) : ZPoly := Id.run do
  let mut acc : ZPoly := 1
  for i in [1:n+1] do
    acc := acc * (zp #[-(Int.ofNat i), 1])
  return acc

/-- Encode integer list as compact JSON. -/
private def encodeInts (xs : List Int) : String :=
  "[" ++ String.intercalate "," (xs.map toString) ++ "]"

/-- A hash that depends on every coefficient of every factor — guarantees the
factorization is fully evaluated before we stop the clock. -/
private def factorChecksum (φ : Factorization) : UInt64 :=
  let h0 : UInt64 := hash φ.scalar
  φ.factors.foldl (init := h0) fun acc (g, m) =>
    let gh := g.toArray.foldl (init := (0 : UInt64)) (fun a c => mixHash a (hash c))
    mixHash (mixHash acc gh) (hash m)

private def factorTimed (degree : Nat) (f : ZPoly) : IO Unit := do
  -- Repeat enough that even fast cases give a meaningful reading.
  let reps : Nat := if degree ≤ 6 then 50 else if degree ≤ 10 then 10 else 3
  let t0 ← IO.monoNanosNow
  let mut chk : UInt64 := 0
  let mut nFactors : Nat := 0
  for _ in [0:reps] do
    let φ := Hex.factor f
    chk := chk ^^^ factorChecksum φ
    nFactors := φ.factors.size
  let t1 ← IO.monoNanosNow
  let nanos := (t1 - t0) / reps
  let coeffs := f.toArray.toList
  let line := "{" ++ s!"\"degree\":{degree},\"factors\":{nFactors},\"reps\":{reps},\"lean_nanos\":{nanos},\"checksum\":{chk},\"coeffs\":{encodeInts coeffs}" ++ "}"
  IO.println line

def main (argv : List String) : IO Unit := do
  let degrees :=
    match argv with
    | [] => [2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,18,20,22,24]
    | _  => argv.filterMap (fun (s : String) => String.toNat? s)
  -- warm up
  let _ := Hex.factor (zp #[-1,1])
  for d in degrees do
    factorTimed d (splitProduct d)
