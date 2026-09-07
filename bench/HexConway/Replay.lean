/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import HexConway

open Hex Hex.Conway Lean

/-! Compiled verification timings for the complete supported scope.
The mutable input prevents closed checks from being folded by the compiler.
These timings measure runtime verification, not proof elaboration or replay. -/

private def measureEntry (p n : Nat) [ZMod64.Bounds p] [ZMod64.PrimeModulus p]
    (input : {f : FpPoly p // DensePoly.Monic f})
    (qs es fullDigits : List Nat) (perPrimeDigits : List (List Nat))
    (divisors : List (Nat × FpPoly p)) : IO Unit := do
  let ref ← IO.mkRef input
  let f ← ref.get
  let start ← IO.monoNanosNow
  unless Berlekamp.rabinTest f.val f.property do
    throw <| IO.userError s!"irreducibility failed: ({p}, {n})"
  let irreducible ← IO.monoNanosNow
  unless primitiveCheck f.val f.property n qs es fullDigits perPrimeDigits do
    throw <| IO.userError s!"primitivity failed: ({p}, {n})"
  let primitive ← IO.monoNanosNow
  for (m, small) in divisors do
    unless compatCheck small f.val f.property m (n / m) do
      throw <| IO.userError s!"compatibility failed: ({p}, {m}, {n})"
  let compatible ← IO.monoNanosNow
  IO.println <| Json.compress <| Json.mkObj [
    ("p", toJson p), ("n", toJson n),
    ("irreducibility_ns", toJson (irreducible - start)),
    ("primitivity_ns", toJson (primitive - irreducible)),
    ("compatibility_ns", toJson (compatible - primitive)),
    ("compatibility_obligations", toJson divisors.length)]

def main : IO Unit := do
  measureEntry 2 1 ⟨luebeckConwayPolynomial_2_1, luebeckConwayPolynomial_2_1_monic⟩
    [] [] [1]
    [] []
  measureEntry 2 2 ⟨luebeckConwayPolynomial_2_2, luebeckConwayPolynomial_2_2_monic⟩
    [3] [1] [1, 1]
    [[1]] [(1, luebeckConwayPolynomial_2_1)]
  measureEntry 2 3 ⟨luebeckConwayPolynomial_2_3, luebeckConwayPolynomial_2_3_monic⟩
    [7] [1] [1, 1, 1]
    [[1]] [(1, luebeckConwayPolynomial_2_1)]
  measureEntry 2 4 ⟨luebeckConwayPolynomial_2_4, luebeckConwayPolynomial_2_4_monic⟩
    [3, 5] [1, 1] [1, 1, 1, 1]
    [[1, 0, 1], [1, 1]] [(1, luebeckConwayPolynomial_2_1), (2, luebeckConwayPolynomial_2_2)]
  measureEntry 2 5 ⟨luebeckConwayPolynomial_2_5, luebeckConwayPolynomial_2_5_monic⟩
    [31] [1] [1, 1, 1, 1, 1]
    [[1]] [(1, luebeckConwayPolynomial_2_1)]
  measureEntry 2 6 ⟨luebeckConwayPolynomial_2_6, luebeckConwayPolynomial_2_6_monic⟩
    [3, 7] [2, 1] [1, 1, 1, 1, 1, 1]
    [[1, 0, 1, 0, 1], [1, 0, 0, 1]] [(1, luebeckConwayPolynomial_2_1), (2, luebeckConwayPolynomial_2_2), (3, luebeckConwayPolynomial_2_3)]
  measureEntry 2 7 ⟨luebeckConwayPolynomial_2_7, luebeckConwayPolynomial_2_7_monic⟩
    [127] [1] [1, 1, 1, 1, 1, 1, 1]
    [[1]] [(1, luebeckConwayPolynomial_2_1)]
  measureEntry 2 8 ⟨luebeckConwayPolynomial_2_8, luebeckConwayPolynomial_2_8_monic⟩
    [3, 5, 17] [1, 1, 1] [1, 1, 1, 1, 1, 1, 1, 1]
    [[1, 0, 1, 0, 1, 0, 1], [1, 1, 0, 0, 1, 1], [1, 1, 1, 1]] [(1, luebeckConwayPolynomial_2_1), (2, luebeckConwayPolynomial_2_2), (4, luebeckConwayPolynomial_2_4)]
  measureEntry 2 9 ⟨luebeckConwayPolynomial_2_9, luebeckConwayPolynomial_2_9_monic⟩
    [7, 73] [1, 1] [1, 1, 1, 1, 1, 1, 1, 1, 1]
    [[1, 0, 0, 1, 0, 0, 1], [1, 1, 1]] [(1, luebeckConwayPolynomial_2_1), (3, luebeckConwayPolynomial_2_3)]
  measureEntry 2 10 ⟨luebeckConwayPolynomial_2_10, luebeckConwayPolynomial_2_10_monic⟩
    [3, 11, 31] [1, 1, 1] [1, 1, 1, 1, 1, 1, 1, 1, 1, 1]
    [[1, 0, 1, 0, 1, 0, 1, 0, 1], [1, 0, 1, 1, 1, 0, 1], [1, 0, 0, 0, 0, 1]] [(1, luebeckConwayPolynomial_2_1), (2, luebeckConwayPolynomial_2_2), (5, luebeckConwayPolynomial_2_5)]
  measureEntry 2 11 ⟨luebeckConwayPolynomial_2_11, luebeckConwayPolynomial_2_11_monic⟩
    [23, 89] [1, 1] [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]
    [[1, 0, 1, 1, 0, 0, 1], [1, 0, 1, 1, 1]] [(1, luebeckConwayPolynomial_2_1)]
  measureEntry 2 12 ⟨luebeckConwayPolynomial_2_12, luebeckConwayPolynomial_2_12_monic⟩
    [3, 5, 7, 13] [2, 1, 1, 1] [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]
    [[1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1], [1, 1, 0, 0, 1, 1, 0, 0, 1, 1], [1, 0, 0, 1, 0, 0, 1, 0, 0, 1], [1, 0, 0, 1, 1, 1, 0, 1, 1]] [(1, luebeckConwayPolynomial_2_1), (2, luebeckConwayPolynomial_2_2), (3, luebeckConwayPolynomial_2_3), (4, luebeckConwayPolynomial_2_4), (6, luebeckConwayPolynomial_2_6)]
  measureEntry 2 13 ⟨luebeckConwayPolynomial_2_13, luebeckConwayPolynomial_2_13_monic⟩
    [8191] [1] [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]
    [[1]] [(1, luebeckConwayPolynomial_2_1)]
  measureEntry 2 14 ⟨luebeckConwayPolynomial_2_14, luebeckConwayPolynomial_2_14_monic⟩
    [3, 43, 127] [1, 1, 1] [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]
    [[1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1], [1, 0, 1, 1, 1, 1, 1, 0, 1], [1, 0, 0, 0, 0, 0, 0, 1]] [(1, luebeckConwayPolynomial_2_1), (2, luebeckConwayPolynomial_2_2), (7, luebeckConwayPolynomial_2_7)]
  measureEntry 2 15 ⟨luebeckConwayPolynomial_2_15, luebeckConwayPolynomial_2_15_monic⟩
    [7, 31, 151] [1, 1, 1] [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]
    [[1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1], [1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1], [1, 1, 0, 1, 1, 0, 0, 1]] [(1, luebeckConwayPolynomial_2_1), (3, luebeckConwayPolynomial_2_3), (5, luebeckConwayPolynomial_2_5)]
  measureEntry 2 16 ⟨luebeckConwayPolynomial_2_16, luebeckConwayPolynomial_2_16_monic⟩
    [3, 5, 17, 257] [1, 1, 1, 1] [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]
    [[1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1], [1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1], [1, 1, 1, 1, 0, 0, 0, 0, 1, 1, 1, 1], [1, 1, 1, 1, 1, 1, 1, 1]] [(1, luebeckConwayPolynomial_2_1), (2, luebeckConwayPolynomial_2_2), (4, luebeckConwayPolynomial_2_4), (8, luebeckConwayPolynomial_2_8)]
  measureEntry 3 1 ⟨luebeckConwayPolynomial_3_1, luebeckConwayPolynomial_3_1_monic⟩
    [2] [1] [1, 0]
    [[1]] []
  measureEntry 3 2 ⟨luebeckConwayPolynomial_3_2, luebeckConwayPolynomial_3_2_monic⟩
    [2] [3] [1, 0, 0, 0]
    [[1, 0, 0]] [(1, luebeckConwayPolynomial_3_1)]
  measureEntry 3 3 ⟨luebeckConwayPolynomial_3_3, luebeckConwayPolynomial_3_3_monic⟩
    [2, 13] [1, 1] [1, 1, 0, 1, 0]
    [[1, 1, 0, 1], [1, 0]] [(1, luebeckConwayPolynomial_3_1)]
  measureEntry 3 4 ⟨luebeckConwayPolynomial_3_4, luebeckConwayPolynomial_3_4_monic⟩
    [2, 5] [4, 1] [1, 0, 1, 0, 0, 0, 0]
    [[1, 0, 1, 0, 0, 0], [1, 0, 0, 0, 0]] [(1, luebeckConwayPolynomial_3_1), (2, luebeckConwayPolynomial_3_2)]
  measureEntry 3 5 ⟨luebeckConwayPolynomial_3_5, luebeckConwayPolynomial_3_5_monic⟩
    [2, 11] [1, 2] [1, 1, 1, 1, 0, 0, 1, 0]
    [[1, 1, 1, 1, 0, 0, 1], [1, 0, 1, 1, 0]] [(1, luebeckConwayPolynomial_3_1)]
  measureEntry 3 6 ⟨luebeckConwayPolynomial_3_6, luebeckConwayPolynomial_3_6_monic⟩
    [2, 7, 13] [3, 1, 1] [1, 0, 1, 1, 0, 1, 1, 0, 0, 0]
    [[1, 0, 1, 1, 0, 1, 1, 0, 0], [1, 1, 0, 1, 0, 0, 0], [1, 1, 1, 0, 0, 0]] [(1, luebeckConwayPolynomial_3_1), (2, luebeckConwayPolynomial_3_2), (3, luebeckConwayPolynomial_3_3)]
  measureEntry 3 7 ⟨luebeckConwayPolynomial_3_7, luebeckConwayPolynomial_3_7_monic⟩
    [2, 1093] [1, 1] [1, 0, 0, 0, 1, 0, 0, 0, 1, 0, 1, 0]
    [[1, 0, 0, 0, 1, 0, 0, 0, 1, 0, 1], [1, 0]] [(1, luebeckConwayPolynomial_3_1)]
  measureEntry 3 8 ⟨luebeckConwayPolynomial_3_8, luebeckConwayPolynomial_3_8_monic⟩
    [2, 5, 41] [5, 1, 1] [1, 1, 0, 0, 1, 1, 0, 1, 0, 0, 0, 0, 0]
    [[1, 1, 0, 0, 1, 1, 0, 1, 0, 0, 0, 0], [1, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0], [1, 0, 1, 0, 0, 0, 0, 0]] [(1, luebeckConwayPolynomial_3_1), (2, luebeckConwayPolynomial_3_2), (4, luebeckConwayPolynomial_3_4)]
  measureEntry 5 1 ⟨luebeckConwayPolynomial_5_1, luebeckConwayPolynomial_5_1_monic⟩
    [2] [2] [1, 0, 0]
    [[1, 0]] []
  measureEntry 5 2 ⟨luebeckConwayPolynomial_5_2, luebeckConwayPolynomial_5_2_monic⟩
    [2, 3] [3, 1] [1, 1, 0, 0, 0]
    [[1, 1, 0, 0], [1, 0, 0, 0]] [(1, luebeckConwayPolynomial_5_1)]
  measureEntry 5 3 ⟨luebeckConwayPolynomial_5_3, luebeckConwayPolynomial_5_3_monic⟩
    [2, 31] [2, 1] [1, 1, 1, 1, 1, 0, 0]
    [[1, 1, 1, 1, 1, 0], [1, 0, 0]] [(1, luebeckConwayPolynomial_5_1)]
  measureEntry 5 4 ⟨luebeckConwayPolynomial_5_4, luebeckConwayPolynomial_5_4_monic⟩
    [2, 3, 13] [4, 1, 1] [1, 0, 0, 1, 1, 1, 0, 0, 0, 0]
    [[1, 0, 0, 1, 1, 1, 0, 0, 0], [1, 1, 0, 1, 0, 0, 0, 0], [1, 1, 0, 0, 0, 0]] [(1, luebeckConwayPolynomial_5_1), (2, luebeckConwayPolynomial_5_2)]
  measureEntry 5 5 ⟨luebeckConwayPolynomial_5_5, luebeckConwayPolynomial_5_5_monic⟩
    [2, 11, 71] [2, 1, 1] [1, 1, 0, 0, 0, 0, 1, 1, 0, 1, 0, 0]
    [[1, 1, 0, 0, 0, 0, 1, 1, 0, 1, 0], [1, 0, 0, 0, 1, 1, 1, 0, 0], [1, 0, 1, 1, 0, 0]] [(1, luebeckConwayPolynomial_5_1)]
  measureEntry 5 6 ⟨luebeckConwayPolynomial_5_6, luebeckConwayPolynomial_5_6_monic⟩
    [2, 3, 7, 31] [3, 2, 1, 1] [1, 1, 1, 1, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0]
    [[1, 1, 1, 1, 0, 1, 0, 0, 0, 0, 1, 0, 0], [1, 0, 1, 0, 0, 0, 1, 0, 1, 1, 0, 0, 0], [1, 0, 0, 0, 1, 0, 1, 1, 1, 0, 0, 0], [1, 1, 1, 1, 1, 1, 0, 0, 0]] [(1, luebeckConwayPolynomial_5_1), (2, luebeckConwayPolynomial_5_2), (3, luebeckConwayPolynomial_5_3)]
  measureEntry 5 7 ⟨luebeckConwayPolynomial_5_7, luebeckConwayPolynomial_5_7_monic⟩
    [2, 19531] [2, 1] [1, 0, 0, 1, 1, 0, 0, 0, 1, 0, 0, 1, 0, 1, 1, 0, 0]
    [[1, 0, 0, 1, 1, 0, 0, 0, 1, 0, 0, 1, 0, 1, 1, 0], [1, 0, 0]] [(1, luebeckConwayPolynomial_5_1)]
  measureEntry 5 8 ⟨luebeckConwayPolynomial_5_8, luebeckConwayPolynomial_5_8_monic⟩
    [2, 3, 13, 313] [5, 1, 1, 1] [1, 0, 1, 1, 1, 1, 1, 0, 1, 0, 1, 1, 1, 1, 0, 0, 0, 0, 0]
    [[1, 0, 1, 1, 1, 1, 1, 0, 1, 0, 1, 1, 1, 1, 0, 0, 0, 0], [1, 1, 1, 1, 1, 1, 1, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0], [1, 1, 1, 0, 1, 0, 1, 0, 1, 1, 0, 0, 0, 0, 0], [1, 0, 0, 1, 1, 1, 0, 0, 0, 0, 0]] [(1, luebeckConwayPolynomial_5_1), (2, luebeckConwayPolynomial_5_2), (4, luebeckConwayPolynomial_5_4)]
  measureEntry 7 1 ⟨luebeckConwayPolynomial_7_1, luebeckConwayPolynomial_7_1_monic⟩
    [2, 3] [1, 1] [1, 1, 0]
    [[1, 1], [1, 0]] []
  measureEntry 7 2 ⟨luebeckConwayPolynomial_7_2, luebeckConwayPolynomial_7_2_monic⟩
    [2, 3] [4, 1] [1, 1, 0, 0, 0, 0]
    [[1, 1, 0, 0, 0], [1, 0, 0, 0, 0]] [(1, luebeckConwayPolynomial_7_1)]
  measureEntry 7 3 ⟨luebeckConwayPolynomial_7_3, luebeckConwayPolynomial_7_3_monic⟩
    [2, 3, 19] [1, 2, 1] [1, 0, 1, 0, 1, 0, 1, 1, 0]
    [[1, 0, 1, 0, 1, 0, 1, 1], [1, 1, 1, 0, 0, 1, 0], [1, 0, 0, 1, 0]] [(1, luebeckConwayPolynomial_7_1)]
  measureEntry 7 4 ⟨luebeckConwayPolynomial_7_4, luebeckConwayPolynomial_7_4_monic⟩
    [2, 3, 5] [5, 1, 2] [1, 0, 0, 1, 0, 1, 1, 0, 0, 0, 0, 0]
    [[1, 0, 0, 1, 0, 1, 1, 0, 0, 0, 0], [1, 1, 0, 0, 1, 0, 0, 0, 0, 0], [1, 1, 1, 1, 0, 0, 0, 0, 0]] [(1, luebeckConwayPolynomial_7_1), (2, luebeckConwayPolynomial_7_2)]
  measureEntry 7 5 ⟨luebeckConwayPolynomial_7_5, luebeckConwayPolynomial_7_5_monic⟩
    [2, 3, 2801] [1, 1, 1] [1, 0, 0, 0, 0, 0, 1, 1, 0, 1, 0, 0, 1, 1, 0]
    [[1, 0, 0, 0, 0, 0, 1, 1, 0, 1, 0, 0, 1, 1], [1, 0, 1, 0, 1, 1, 1, 1, 0, 0, 0, 1, 0], [1, 1, 0]] [(1, luebeckConwayPolynomial_7_1)]
  measureEntry 7 6 ⟨luebeckConwayPolynomial_7_6, luebeckConwayPolynomial_7_6_monic⟩
    [2, 3, 19, 43] [4, 2, 1, 1] [1, 1, 1, 0, 0, 1, 0, 1, 1, 1, 0, 0, 1, 0, 0, 0, 0]
    [[1, 1, 1, 0, 0, 1, 0, 1, 1, 1, 0, 0, 1, 0, 0, 0], [1, 0, 0, 1, 1, 0, 0, 1, 0, 0, 1, 1, 0, 0, 0, 0], [1, 1, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0], [1, 0, 1, 0, 1, 0, 1, 1, 0, 0, 0, 0]] [(1, luebeckConwayPolynomial_7_1), (2, luebeckConwayPolynomial_7_2), (3, luebeckConwayPolynomial_7_3)]
  measureEntry 7 7 ⟨luebeckConwayPolynomial_7_7, luebeckConwayPolynomial_7_7_monic⟩
    [2, 3, 29, 4733] [1, 1, 1, 1] [1, 1, 0, 0, 1, 0, 0, 1, 0, 0, 0, 0, 1, 1, 1, 1, 0, 1, 1, 0]
    [[1, 1, 0, 0, 1, 0, 0, 1, 0, 0, 0, 0, 1, 1, 1, 1, 0, 1, 1], [1, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 1, 0], [1, 1, 0, 1, 1, 1, 0, 1, 1, 1, 0, 1, 1, 1, 0], [1, 0, 1, 0, 1, 1, 1, 0]] [(1, luebeckConwayPolynomial_7_1)]
  measureEntry 7 8 ⟨luebeckConwayPolynomial_7_8, luebeckConwayPolynomial_7_8_monic⟩
    [2, 3, 5, 1201] [6, 1, 2, 1] [1, 0, 1, 0, 1, 1, 1, 1, 1, 1, 1, 0, 1, 1, 0, 1, 1, 0, 0, 0, 0, 0, 0]
    [[1, 0, 1, 0, 1, 1, 1, 1, 1, 1, 1, 0, 1, 1, 0, 1, 1, 0, 0, 0, 0, 0], [1, 1, 1, 0, 1, 0, 1, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0], [1, 0, 0, 0, 1, 1, 0, 0, 1, 0, 1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0], [1, 0, 0, 1, 0, 1, 1, 0, 0, 0, 0, 0, 0]] [(1, luebeckConwayPolynomial_7_1), (2, luebeckConwayPolynomial_7_2), (4, luebeckConwayPolynomial_7_4)]
  measureEntry 11 1 ⟨luebeckConwayPolynomial_11_1, luebeckConwayPolynomial_11_1_monic⟩
    [2, 5] [1, 1] [1, 0, 1, 0]
    [[1, 0, 1], [1, 0]] []
  measureEntry 11 2 ⟨luebeckConwayPolynomial_11_2, luebeckConwayPolynomial_11_2_monic⟩
    [2, 3, 5] [3, 1, 1] [1, 1, 1, 1, 0, 0, 0]
    [[1, 1, 1, 1, 0, 0], [1, 0, 1, 0, 0, 0], [1, 1, 0, 0, 0]] [(1, luebeckConwayPolynomial_11_1)]
  measureEntry 11 3 ⟨luebeckConwayPolynomial_11_3, luebeckConwayPolynomial_11_3_monic⟩
    [2, 5, 7, 19] [1, 1, 1, 1] [1, 0, 1, 0, 0, 1, 1, 0, 0, 1, 0]
    [[1, 0, 1, 0, 0, 1, 1, 0, 0, 1], [1, 0, 0, 0, 0, 1, 0, 1, 0], [1, 0, 1, 1, 1, 1, 1, 0], [1, 0, 0, 0, 1, 1, 0]] [(1, luebeckConwayPolynomial_11_1)]
  measureEntry 11 4 ⟨luebeckConwayPolynomial_11_4, luebeckConwayPolynomial_11_4_monic⟩
    [2, 3, 5, 61] [4, 1, 1, 1] [1, 1, 1, 0, 0, 1, 0, 0, 1, 1, 0, 0, 0, 0]
    [[1, 1, 1, 0, 0, 1, 0, 0, 1, 1, 0, 0, 0], [1, 0, 0, 1, 1, 0, 0, 0, 1, 0, 0, 0, 0], [1, 0, 1, 1, 0, 1, 1, 1, 0, 0, 0, 0], [1, 1, 1, 1, 0, 0, 0, 0]] [(1, luebeckConwayPolynomial_11_1), (2, luebeckConwayPolynomial_11_2)]
  measureEntry 11 5 ⟨luebeckConwayPolynomial_11_5, luebeckConwayPolynomial_11_5_monic⟩
    [2, 5, 3221] [1, 2, 1] [1, 0, 0, 1, 1, 1, 0, 1, 0, 1, 0, 0, 0, 1, 1, 0, 1, 0]
    [[1, 0, 0, 1, 1, 1, 0, 1, 0, 1, 0, 0, 0, 1, 1, 0, 1], [1, 1, 1, 1, 1, 0, 1, 1, 1, 0, 1, 0, 0, 1, 0], [1, 1, 0, 0, 1, 0]] [(1, luebeckConwayPolynomial_11_1)]
  measureEntry 11 6 ⟨luebeckConwayPolynomial_11_6, luebeckConwayPolynomial_11_6_monic⟩
    [2, 3, 5, 7, 19, 37] [3, 2, 1, 1, 1, 1] [1, 1, 0, 1, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0]
    [[1, 1, 0, 1, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0], [1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 1, 1, 1, 0, 0, 0], [1, 0, 1, 0, 1, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [1, 1, 1, 1, 0, 1, 1, 1, 0, 0, 1, 0, 0, 1, 1, 0, 0, 0], [1, 0, 1, 1, 0, 1, 1, 0, 0, 0, 0, 1, 1, 1, 0, 0, 0], [1, 0, 1, 1, 1, 0, 1, 1, 0, 0, 0, 0, 1, 0, 0, 0]] [(1, luebeckConwayPolynomial_11_1), (2, luebeckConwayPolynomial_11_2), (3, luebeckConwayPolynomial_11_3)]
  measureEntry 13 1 ⟨luebeckConwayPolynomial_13_1, luebeckConwayPolynomial_13_1_monic⟩
    [2, 3] [2, 1] [1, 1, 0, 0]
    [[1, 1, 0], [1, 0, 0]] []
  measureEntry 13 2 ⟨luebeckConwayPolynomial_13_2, luebeckConwayPolynomial_13_2_monic⟩
    [2, 3, 7] [3, 1, 1] [1, 0, 1, 0, 1, 0, 0, 0]
    [[1, 0, 1, 0, 1, 0, 0], [1, 1, 1, 0, 0, 0], [1, 1, 0, 0, 0]] [(1, luebeckConwayPolynomial_13_1)]
  measureEntry 13 3 ⟨luebeckConwayPolynomial_13_3, luebeckConwayPolynomial_13_3_monic⟩
    [2, 3, 61] [2, 2, 1] [1, 0, 0, 0, 1, 0, 0, 1, 0, 1, 0, 0]
    [[1, 0, 0, 0, 1, 0, 0, 1, 0, 1, 0], [1, 0, 1, 1, 0, 1, 1, 1, 0, 0], [1, 0, 0, 1, 0, 0]] [(1, luebeckConwayPolynomial_13_1)]
  measureEntry 13 4 ⟨luebeckConwayPolynomial_13_4, luebeckConwayPolynomial_13_4_monic⟩
    [2, 3, 5, 7, 17] [4, 1, 1, 1, 1] [1, 1, 0, 1, 1, 1, 1, 1, 0, 0, 1, 0, 0, 0, 0]
    [[1, 1, 0, 1, 1, 1, 1, 1, 0, 0, 1, 0, 0, 0], [1, 0, 0, 1, 0, 1, 0, 0, 1, 1, 0, 0, 0, 0], [1, 0, 1, 1, 0, 0, 1, 0, 1, 0, 0, 0, 0], [1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 0], [1, 1, 0, 1, 0, 0, 1, 0, 0, 0, 0]] [(1, luebeckConwayPolynomial_13_1), (2, luebeckConwayPolynomial_13_2)]
  measureEntry 13 5 ⟨luebeckConwayPolynomial_13_5, luebeckConwayPolynomial_13_5_monic⟩
    [2, 3, 30941] [2, 1, 1] [1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 0, 1, 0, 1, 1, 1, 0, 0]
    [[1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 0, 1, 0, 1, 1, 1, 0], [1, 1, 1, 1, 0, 0, 0, 1, 1, 0, 1, 1, 1, 0, 1, 0, 0], [1, 1, 0, 0]] [(1, luebeckConwayPolynomial_13_1)]
  measureEntry 13 6 ⟨luebeckConwayPolynomial_13_6, luebeckConwayPolynomial_13_6_monic⟩
    [2, 3, 7, 61, 157] [3, 2, 1, 1, 1] [1, 0, 0, 1, 0, 0, 1, 1, 0, 1, 0, 0, 1, 1, 0, 1, 0, 1, 1, 1, 0, 0, 0]
    [[1, 0, 0, 1, 0, 0, 1, 1, 0, 1, 0, 0, 1, 1, 0, 1, 0, 1, 1, 1, 0, 0], [1, 1, 0, 0, 0, 1, 0, 0, 0, 1, 1, 0, 0, 1, 1, 1, 0, 1, 0, 0, 0], [1, 0, 1, 0, 1, 0, 0, 0, 0, 1, 0, 1, 1, 0, 0, 0, 1, 0, 0, 0], [1, 0, 0, 1, 1, 0, 1, 0, 1, 0, 0, 0, 1, 1, 0, 0, 0], [1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0]] [(1, luebeckConwayPolynomial_13_1), (2, luebeckConwayPolynomial_13_2), (3, luebeckConwayPolynomial_13_3)]
  measureEntry 17 1 ⟨luebeckConwayPolynomial_17_1, luebeckConwayPolynomial_17_1_monic⟩
    [2] [4] [1, 0, 0, 0, 0]
    [[1, 0, 0, 0]] []
  measureEntry 17 2 ⟨luebeckConwayPolynomial_17_2, luebeckConwayPolynomial_17_2_monic⟩
    [2, 3] [5, 2] [1, 0, 0, 1, 0, 0, 0, 0, 0]
    [[1, 0, 0, 1, 0, 0, 0, 0], [1, 1, 0, 0, 0, 0, 0]] [(1, luebeckConwayPolynomial_17_1)]
  measureEntry 19 1 ⟨luebeckConwayPolynomial_19_1, luebeckConwayPolynomial_19_1_monic⟩
    [2, 3] [1, 2] [1, 0, 0, 1, 0]
    [[1, 0, 0, 1], [1, 1, 0]] []
  measureEntry 19 2 ⟨luebeckConwayPolynomial_19_2, luebeckConwayPolynomial_19_2_monic⟩
    [2, 3, 5] [3, 2, 1] [1, 0, 1, 1, 0, 1, 0, 0, 0]
    [[1, 0, 1, 1, 0, 1, 0, 0], [1, 1, 1, 1, 0, 0, 0], [1, 0, 0, 1, 0, 0, 0]] [(1, luebeckConwayPolynomial_19_1)]
  measureEntry 23 1 ⟨luebeckConwayPolynomial_23_1, luebeckConwayPolynomial_23_1_monic⟩
    [2, 11] [1, 1] [1, 0, 1, 1, 0]
    [[1, 0, 1, 1], [1, 0]] []
  measureEntry 23 2 ⟨luebeckConwayPolynomial_23_2, luebeckConwayPolynomial_23_2_monic⟩
    [2, 3, 11] [4, 1, 1] [1, 0, 0, 0, 0, 1, 0, 0, 0, 0]
    [[1, 0, 0, 0, 0, 1, 0, 0, 0], [1, 0, 1, 1, 0, 0, 0, 0], [1, 1, 0, 0, 0, 0]] [(1, luebeckConwayPolynomial_23_1)]
  measureEntry 29 1 ⟨luebeckConwayPolynomial_29_1, luebeckConwayPolynomial_29_1_monic⟩
    [2, 7] [2, 1] [1, 1, 1, 0, 0]
    [[1, 1, 1, 0], [1, 0, 0]] []
  measureEntry 29 2 ⟨luebeckConwayPolynomial_29_2, luebeckConwayPolynomial_29_2_monic⟩
    [2, 3, 5, 7] [3, 1, 1, 1] [1, 1, 0, 1, 0, 0, 1, 0, 0, 0]
    [[1, 1, 0, 1, 0, 0, 1, 0, 0], [1, 0, 0, 0, 1, 1, 0, 0, 0], [1, 0, 1, 0, 1, 0, 0, 0], [1, 1, 1, 1, 0, 0, 0]] [(1, luebeckConwayPolynomial_29_1)]
  measureEntry 31 1 ⟨luebeckConwayPolynomial_31_1, luebeckConwayPolynomial_31_1_monic⟩
    [2, 3, 5] [1, 1, 1] [1, 1, 1, 1, 0]
    [[1, 1, 1, 1], [1, 0, 1, 0], [1, 1, 0]] []
  measureEntry 31 2 ⟨luebeckConwayPolynomial_31_2, luebeckConwayPolynomial_31_2_monic⟩
    [2, 3, 5] [6, 1, 1] [1, 1, 1, 1, 0, 0, 0, 0, 0, 0]
    [[1, 1, 1, 1, 0, 0, 0, 0, 0], [1, 0, 1, 0, 0, 0, 0, 0, 0], [1, 1, 0, 0, 0, 0, 0, 0]] [(1, luebeckConwayPolynomial_31_1)]
  measureEntry 37 1 ⟨luebeckConwayPolynomial_37_1, luebeckConwayPolynomial_37_1_monic⟩
    [2, 3] [2, 2] [1, 0, 0, 1, 0, 0]
    [[1, 0, 0, 1, 0], [1, 1, 0, 0]] []
  measureEntry 37 2 ⟨luebeckConwayPolynomial_37_2, luebeckConwayPolynomial_37_2_monic⟩
    [2, 3, 19] [3, 2, 1] [1, 0, 1, 0, 1, 0, 1, 1, 0, 0, 0]
    [[1, 0, 1, 0, 1, 0, 1, 1, 0, 0], [1, 1, 1, 0, 0, 1, 0, 0, 0], [1, 0, 0, 1, 0, 0, 0]] [(1, luebeckConwayPolynomial_37_1)]
  measureEntry 41 1 ⟨luebeckConwayPolynomial_41_1, luebeckConwayPolynomial_41_1_monic⟩
    [2, 5] [3, 1] [1, 0, 1, 0, 0, 0]
    [[1, 0, 1, 0, 0], [1, 0, 0, 0]] []
  measureEntry 41 2 ⟨luebeckConwayPolynomial_41_2, luebeckConwayPolynomial_41_2_monic⟩
    [2, 3, 5, 7] [4, 1, 1, 1] [1, 1, 0, 1, 0, 0, 1, 0, 0, 0, 0]
    [[1, 1, 0, 1, 0, 0, 1, 0, 0, 0], [1, 0, 0, 0, 1, 1, 0, 0, 0, 0], [1, 0, 1, 0, 1, 0, 0, 0, 0], [1, 1, 1, 1, 0, 0, 0, 0]] [(1, luebeckConwayPolynomial_41_1)]
  measureEntry 43 1 ⟨luebeckConwayPolynomial_43_1, luebeckConwayPolynomial_43_1_monic⟩
    [2, 3, 7] [1, 1, 1] [1, 0, 1, 0, 1, 0]
    [[1, 0, 1, 0, 1], [1, 1, 1, 0], [1, 1, 0]] []
  measureEntry 43 2 ⟨luebeckConwayPolynomial_43_2, luebeckConwayPolynomial_43_2_monic⟩
    [2, 3, 7, 11] [3, 1, 1, 1] [1, 1, 1, 0, 0, 1, 1, 1, 0, 0, 0]
    [[1, 1, 1, 0, 0, 1, 1, 1, 0, 0], [1, 0, 0, 1, 1, 0, 1, 0, 0, 0], [1, 0, 0, 0, 0, 1, 0, 0, 0], [1, 0, 1, 0, 1, 0, 0, 0]] [(1, luebeckConwayPolynomial_43_1)]
  measureEntry 47 1 ⟨luebeckConwayPolynomial_47_1, luebeckConwayPolynomial_47_1_monic⟩
    [2, 23] [1, 1] [1, 0, 1, 1, 1, 0]
    [[1, 0, 1, 1, 1], [1, 0]] []
  measureEntry 47 2 ⟨luebeckConwayPolynomial_47_2, luebeckConwayPolynomial_47_2_monic⟩
    [2, 3, 23] [5, 1, 1] [1, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0]
    [[1, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0], [1, 0, 1, 1, 1, 0, 0, 0, 0, 0], [1, 1, 0, 0, 0, 0, 0]] [(1, luebeckConwayPolynomial_47_1)]
  measureEntry 53 1 ⟨luebeckConwayPolynomial_53_1, luebeckConwayPolynomial_53_1_monic⟩
    [2, 13] [2, 1] [1, 1, 0, 1, 0, 0]
    [[1, 1, 0, 1, 0], [1, 0, 0]] []
  measureEntry 53 2 ⟨luebeckConwayPolynomial_53_2, luebeckConwayPolynomial_53_2_monic⟩
    [2, 3, 13] [3, 3, 1] [1, 0, 1, 0, 1, 1, 1, 1, 1, 0, 0, 0]
    [[1, 0, 1, 0, 1, 1, 1, 1, 1, 0, 0], [1, 1, 1, 0, 1, 0, 1, 0, 0, 0], [1, 1, 0, 1, 1, 0, 0, 0]] [(1, luebeckConwayPolynomial_53_1)]
  measureEntry 59 1 ⟨luebeckConwayPolynomial_59_1, luebeckConwayPolynomial_59_1_monic⟩
    [2, 29] [1, 1] [1, 1, 1, 0, 1, 0]
    [[1, 1, 1, 0, 1], [1, 0]] []
  measureEntry 59 2 ⟨luebeckConwayPolynomial_59_2, luebeckConwayPolynomial_59_2_monic⟩
    [2, 3, 5, 29] [3, 1, 1, 1] [1, 1, 0, 1, 1, 0, 0, 1, 1, 0, 0, 0]
    [[1, 1, 0, 1, 1, 0, 0, 1, 1, 0, 0], [1, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0], [1, 0, 1, 0, 1, 1, 1, 0, 0, 0], [1, 1, 1, 1, 0, 0, 0]] [(1, luebeckConwayPolynomial_59_1)]
  measureEntry 61 1 ⟨luebeckConwayPolynomial_61_1, luebeckConwayPolynomial_61_1_monic⟩
    [2, 3, 5] [2, 1, 1] [1, 1, 1, 1, 0, 0]
    [[1, 1, 1, 1, 0], [1, 0, 1, 0, 0], [1, 1, 0, 0]] []
  measureEntry 61 2 ⟨luebeckConwayPolynomial_61_2, luebeckConwayPolynomial_61_2_monic⟩
    [2, 3, 5, 31] [3, 1, 1, 1] [1, 1, 1, 0, 1, 0, 0, 0, 1, 0, 0, 0]
    [[1, 1, 1, 0, 1, 0, 0, 0, 1, 0, 0], [1, 0, 0, 1, 1, 0, 1, 1, 0, 0, 0], [1, 0, 1, 1, 1, 0, 1, 0, 0, 0], [1, 1, 1, 1, 0, 0, 0]] [(1, luebeckConwayPolynomial_61_1)]
  measureEntry 67 1 ⟨luebeckConwayPolynomial_67_1, luebeckConwayPolynomial_67_1_monic⟩
    [2, 3, 11] [1, 1, 1] [1, 0, 0, 0, 0, 1, 0]
    [[1, 0, 0, 0, 0, 1], [1, 0, 1, 1, 0], [1, 1, 0]] []
  measureEntry 67 2 ⟨luebeckConwayPolynomial_67_2, luebeckConwayPolynomial_67_2_monic⟩
    [2, 3, 11, 17] [3, 1, 1, 1] [1, 0, 0, 0, 1, 1, 0, 0, 0, 1, 0, 0, 0]
    [[1, 0, 0, 0, 1, 1, 0, 0, 0, 1, 0, 0], [1, 0, 1, 1, 1, 0, 1, 1, 0, 0, 0], [1, 1, 0, 0, 1, 1, 0, 0, 0], [1, 0, 0, 0, 0, 1, 0, 0, 0]] [(1, luebeckConwayPolynomial_67_1)]
  measureEntry 71 1 ⟨luebeckConwayPolynomial_71_1, luebeckConwayPolynomial_71_1_monic⟩
    [2, 5, 7] [1, 1, 1] [1, 0, 0, 0, 1, 1, 0]
    [[1, 0, 0, 0, 1, 1], [1, 1, 1, 0], [1, 0, 1, 0]] []
  measureEntry 71 2 ⟨luebeckConwayPolynomial_71_2, luebeckConwayPolynomial_71_2_monic⟩
    [2, 3, 5, 7] [4, 2, 1, 1] [1, 0, 0, 1, 1, 1, 0, 1, 1, 0, 0, 0, 0]
    [[1, 0, 0, 1, 1, 1, 0, 1, 1, 0, 0, 0], [1, 1, 0, 1, 0, 0, 1, 0, 0, 0, 0], [1, 1, 1, 1, 1, 1, 0, 0, 0, 0], [1, 0, 1, 1, 0, 1, 0, 0, 0, 0]] [(1, luebeckConwayPolynomial_71_1)]
  measureEntry 73 1 ⟨luebeckConwayPolynomial_73_1, luebeckConwayPolynomial_73_1_monic⟩
    [2, 3] [3, 2] [1, 0, 0, 1, 0, 0, 0]
    [[1, 0, 0, 1, 0, 0], [1, 1, 0, 0, 0]] []
  measureEntry 73 2 ⟨luebeckConwayPolynomial_73_2, luebeckConwayPolynomial_73_2_monic⟩
    [2, 3, 37] [4, 2, 1] [1, 0, 1, 0, 0, 1, 1, 0, 1, 0, 0, 0, 0]
    [[1, 0, 1, 0, 0, 1, 1, 0, 1, 0, 0, 0], [1, 1, 0, 1, 1, 1, 1, 0, 0, 0, 0], [1, 0, 0, 1, 0, 0, 0, 0]] [(1, luebeckConwayPolynomial_73_1)]
  measureEntry 79 1 ⟨luebeckConwayPolynomial_79_1, luebeckConwayPolynomial_79_1_monic⟩
    [2, 3, 13] [1, 1, 1] [1, 0, 0, 1, 1, 1, 0]
    [[1, 0, 0, 1, 1, 1], [1, 1, 0, 1, 0], [1, 1, 0]] []
  measureEntry 79 2 ⟨luebeckConwayPolynomial_79_2, luebeckConwayPolynomial_79_2_monic⟩
    [2, 3, 5, 13] [5, 1, 1, 1] [1, 1, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0]
    [[1, 1, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0], [1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [1, 0, 0, 1, 1, 1, 0, 0, 0, 0, 0], [1, 1, 1, 1, 0, 0, 0, 0, 0]] [(1, luebeckConwayPolynomial_79_1)]
  measureEntry 83 1 ⟨luebeckConwayPolynomial_83_1, luebeckConwayPolynomial_83_1_monic⟩
    [2, 41] [1, 1] [1, 0, 1, 0, 0, 1, 0]
    [[1, 0, 1, 0, 0, 1], [1, 0]] []
  measureEntry 83 2 ⟨luebeckConwayPolynomial_83_2, luebeckConwayPolynomial_83_2_monic⟩
    [2, 3, 7, 41] [3, 1, 1, 1] [1, 1, 0, 1, 0, 1, 1, 1, 0, 1, 0, 0, 0]
    [[1, 1, 0, 1, 0, 1, 1, 1, 0, 1, 0, 0], [1, 0, 0, 0, 1, 1, 1, 1, 1, 0, 0, 0], [1, 1, 1, 1, 0, 1, 1, 0, 0, 0], [1, 0, 1, 0, 1, 0, 0, 0]] [(1, luebeckConwayPolynomial_83_1)]
  measureEntry 89 1 ⟨luebeckConwayPolynomial_89_1, luebeckConwayPolynomial_89_1_monic⟩
    [2, 11] [3, 1] [1, 0, 1, 1, 0, 0, 0]
    [[1, 0, 1, 1, 0, 0], [1, 0, 0, 0]] []
  measureEntry 89 2 ⟨luebeckConwayPolynomial_89_2, luebeckConwayPolynomial_89_2_monic⟩
    [2, 3, 5, 11] [4, 2, 1, 1] [1, 1, 1, 1, 0, 1, 1, 1, 1, 0, 0, 0, 0]
    [[1, 1, 1, 1, 0, 1, 1, 1, 1, 0, 0, 0], [1, 0, 1, 0, 0, 1, 0, 1, 0, 0, 0, 0], [1, 1, 0, 0, 0, 1, 1, 0, 0, 0, 0], [1, 0, 1, 1, 0, 1, 0, 0, 0, 0]] [(1, luebeckConwayPolynomial_89_1)]
  measureEntry 97 1 ⟨luebeckConwayPolynomial_97_1, luebeckConwayPolynomial_97_1_monic⟩
    [2, 3] [5, 1] [1, 1, 0, 0, 0, 0, 0]
    [[1, 1, 0, 0, 0, 0], [1, 0, 0, 0, 0, 0]] []
  measureEntry 97 2 ⟨luebeckConwayPolynomial_97_2, luebeckConwayPolynomial_97_2_monic⟩
    [2, 3, 7] [6, 1, 2] [1, 0, 0, 1, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0]
    [[1, 0, 0, 1, 0, 0, 1, 1, 0, 0, 0, 0, 0], [1, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [1, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0]] [(1, luebeckConwayPolynomial_97_1)]
