/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import HexModularMatrix

/-! Deterministic integer matrices shared by conformance and determinant benchmarks. -/

namespace Hex.ModularMatrixFixtures

/-- The same tridiagonal fixture as the Bareiss benchmark at salt 71. -/
def structured (n : Nat) : Matrix Int n n :=
  Matrix.ofFn fun i j =>
    if i.val = j.val then 3
    else if i.val + 1 = j.val then -1
    else if j.val + 1 = i.val then 1 else 0

/-- Dense signed entries from splitmix64, truncated to the requested bit width. -/
def dense (n bits : Nat) (seed : Nat := 10219) : Matrix Int n n := Id.run do
  let mut r := Rand.ofSeed seed
  let mut entries : Array Int := #[]
  for _ in [:n * n] do
    let (x, next) := r.words ((bits + 63) / 64)
    r := next
    entries := entries.push ((x % (2 ^ bits) : Int) - (2 ^ (bits - 1) : Nat))
  return Matrix.ofFn fun i j => entries.getD (i.val * n + j.val) 0

/-- A dense unimodular rank-one update of the identity. The update is `u vᵀ`
with `u` all ones and the coordinates of `v` summing to zero. -/
def unimodular (n bits : Nat) : Matrix Int n n :=
  Matrix.ofFn fun i j =>
    let v : Int := if n % 2 = 1 && j.val + 1 = n then 0
      else if j.val % 2 = 0 then (2 ^ bits : Nat) else -(2 ^ bits : Int)
    (if i = j then 1 else 0) + v

/-- A named square integer fixture. -/
structure Case where
  name : String
  n : Nat
  matrix : Matrix Int n n

private def small (a b c d : Int) : Matrix Int 2 2 :=
  Matrix.ofFn fun i j => if i.val = 0 then (if j.val = 0 then a else b)
    else if j.val = 0 then c else d

/-- Determinant edge cases and the three required input families. -/
def cases : List Case :=
  let big : Int := 2 ^ 2048
  let p : Int := 2147483647
  let q : Int := 2147483629
  [⟨"empty", 0, Matrix.ofFn fun _ _ => 0⟩,
   ⟨"singleton-negative", 1, Matrix.ofFn fun _ _ => -37⟩,
   ⟨"zero", 3, 0⟩,
   ⟨"singular", 2, small 1 2 2 4⟩,
   ⟨"swap-sign", 2, small 0 2 3 4⟩,
   ⟨"modulus", 1, Matrix.ofFn fun _ _ => p⟩,
   ⟨"two-bad-primes", 1, Matrix.ofFn fun _ _ => p * q⟩,
   ⟨"large-small-determinant", 2, small big (big - 1) (big + 6) (big + 5)⟩,
   ⟨"scaled-hadamard", 4, Matrix.ofFn fun i j =>
      (if (i.val % 2 * (j.val % 2) + i.val / 2 * (j.val / 2)) % 2 = 0 then 1 else -1) * (2 ^ 16 : Int)⟩,
   ⟨"structured-determinant/8", 8, structured 8⟩,
   ⟨"dense-random-determinant/8-bit", 4, dense 4 8⟩,
   ⟨"dense-random-determinant/64-bit", 4, dense 4 64⟩,
   ⟨"dense-random-determinant/1024-bit", 3, dense 3 1024⟩,
   ⟨"unimodular-determinant/positive", 6, unimodular 6 64⟩,
   ⟨"unimodular-determinant/negative", 6, (unimodular 6 64).rowSwap 0 1⟩]

end Hex.ModularMatrixFixtures
