/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import HexMatrix

/-!
Core conformance checks for `hex-matrix` (the dense base).

Run this file through the conformance Lake target, not direct `lake env lean`.

Oracle: none
Mode: always
Covered operations:
- dense matrix constructors and accessors (`ofFn`, `row`, `col`, `transpose`, `principalSubmatrix`)
- vector and matrix arithmetic (`dotProduct`, ``.normSq, `mulVec`, `mul`, `gramMatrix`)
- elementary row operations (`rowSwap`, `rowScale`, `rowAdd`)
- Strassen-Winograd multiplication (`mulStrassen`) under the default and a custom
  base-kernel configuration
Covered properties:
- transpose is involutive on committed fixtures
- identity matrices act as left and right multiplicative identities
- `rowSwap` is involutive
- `mulStrassen cfg A B = mul A B` (the reference product) on committed fixtures for
  `strassenDefault`, a custom naive-kernel config (`cutoff := 4`), and a
  deep-recursion config (`cutoff := 0`)
Covered edge cases:
- zero matrices and zero vectors, identity matrices, 2×2 and 6×6 dimension bands
- Strassen fixtures spanning even, odd, and prime dimensions, distinct-`n`,`m`,`k`
  rectangles, a zero contraction axis (empty product), 1×1, and a square past the
  default cutoff so the recursion fires under `strassenDefault`

The determinant, Bareiss, and row-reduction conformance guards live in the
`HexDeterminant`, `HexBareiss`, and `HexRowReduce` Conformance modules.
-/

namespace Hex

namespace Matrix

private def baseInt : Matrix Int 2 2 :=
  Matrix.ofFn fun i j =>
    match i.val, j.val with
    | 0, 0 => 1
    | 0, _ => 2
    | 1, 0 => 3
    | _, _ => 4

private def pivotInt : Matrix Int 3 3 :=
  Matrix.ofFn fun i j =>
    match i.val, j.val with
    | 0, 0 => 0
    | 0, 1 => 2
    | 0, _ => 1
    | 1, 0 => 3
    | 1, 1 => 0
    | 1, _ => 4
    | 2, 0 => 5
    | 2, 1 => 6
    | _, _ => 0

private def vecInt : Vector Int 2 :=
  Vector.ofFn fun i => if i.val = 0 then 5 else 6

private def rowOneInt : Vector Int 2 :=
  Vector.ofFn fun i => if i.val = 0 then 3 else 4

private def colZeroInt : Vector Int 2 :=
  Vector.ofFn fun i => if i.val = 0 then 1 else 3

private def unitSubmatrix : Matrix Int 1 1 :=
  Matrix.ofFn fun _ _ => 1

private def baseGramInt : Matrix Int 2 2 :=
  Matrix.ofFn fun i j =>
    match i.val, j.val with
    | 0, 0 => 5
    | 0, _ => 11
    | 1, 0 => 11
    | _, _ => 25

private def spanVec : Vector Rat 3 :=
  Vector.ofFn fun i =>
    match i.val with
    | 0 => 1
    | 1 => 2
    | _ => 3

#guard Matrix.row baseInt ⟨1, by decide⟩ = rowOneInt
#guard Matrix.col baseInt ⟨0, by decide⟩ = colZeroInt
#guard Matrix.principalSubmatrix baseInt 1 (by decide) = unitSubmatrix
#guard Matrix.principalSubmatrix baseInt 2 (by decide) = baseInt
#guard vecInt.normSq = 61
#guard spanVec.normSq = 14
#guard Matrix.gramMatrix baseInt = baseGramInt
#guard (Matrix.identity (R := Int) 2) * baseInt = baseInt
#guard baseInt * (Matrix.identity (R := Int) 2) = baseInt
#guard Matrix.transpose (Matrix.transpose baseInt) = baseInt

-- `#m[...]` literal notation agrees with the `ofFn` fixtures.
#guard (#m[1, 2; 3, 4] : Matrix Int 2 2) = baseInt
#guard (#m[0, 2, 1; 3, 0, 4; 5, 6, 0] : Matrix Int 3 3) = pivotInt

/-- info:
#m[1, 3;
   2, 4]
-/
#guard_msgs (whitespace := normalized) in #eval Matrix.transpose baseInt

/-- info: #v[17, 39] -/
#guard_msgs in #eval Matrix.mulVec baseInt vecInt

/-- info:
#m[ 7, 10;
   15, 22]
-/
#guard_msgs (whitespace := normalized) in #eval baseInt * baseInt

/-- info:
#m[3, 4;
   1, 2]
-/
#guard_msgs (whitespace := normalized) in #eval Matrix.rowSwap baseInt ⟨0, by decide⟩ ⟨1, by decide⟩

/-- info:
#m[ 0, 2,  1;
   -6, 0, -8;
    5, 6,  0]
-/
#guard_msgs (whitespace := normalized) in #eval Matrix.rowScale pivotInt ⟨1, by decide⟩ (-2)

/-- info:
#m[0,  2, 1;
   3,  0, 4;
   5, 12, 3]
-/
#guard_msgs (whitespace := normalized) in #eval Matrix.rowAdd pivotInt ⟨0, by decide⟩ ⟨2, by decide⟩ 3

#guard Matrix.rowSwap (Matrix.rowSwap baseInt ⟨0, by decide⟩ ⟨1, by decide⟩)
    ⟨0, by decide⟩ ⟨1, by decide⟩ = baseInt

/-!
6×6 fixtures matching the SPEC `core` matrix-dimension band: `bigInt` is a
typical full-rank Int (entries `min i j + 1`), dense enough to exercise the
base arithmetic at the larger band.
-/

private def bigInt : Matrix Int 6 6 :=
  Matrix.ofFn fun i j => (min i.val j.val + 1 : Int)

#guard Matrix.transpose (Matrix.transpose bigInt) = bigInt
#guard (Matrix.identity (R := Int) 6) * bigInt = bigInt

/-!
Strassen-Winograd (`mulStrassen`) differential guards. Each check asserts
`mulStrassen cfg A B = A * B`, where `A * B` is the reference `mul` — the same
product `mulStrassen_eq_mul` proves it equal to. This is a compiled-evaluator
cross-check (`mul` is `noncomputable` with a `@[csimp]` twin, and `mulStrassen`
is well-founded recursion), not a kernel `decide`.

The custom configs pin an **explicit** cutoff rather than the provisional
`strassenDefault.cutoff` of 64, so a later re-measurement of that constant cannot
silently turn a recursion test into a base-kernel test. `cfgNaive` (`cutoff := 4`)
forces one-or-two recursion levels on the small square/rectangular fixtures with a
deliberately different — but valid — textbook triple-loop base kernel; `cfgDeep`
(`cutoff := 0`) drives the recursion down to the config-independent `≤ 1` base
condition (the 1×1 and empty fixtures exercise exactly that terminating case). The
single `strassenDefault` recursion test uses a 96×96 square, comfortably above any
plausible measured crossover so it keeps firing the recursion regardless of #8680.
-/

/-- Deterministic Int fixture generator; `seed` distinguishes the two operands so
the product is not accidentally symmetric. Entries are kept small to keep the
96×96 default-config guard in the millisecond range. -/
private def genInt (seed n m : Nat) : Matrix Int n m :=
  Matrix.ofFn fun i j => (((i.val + 1) * (j.val + 2) + seed * (i.val + j.val) : Int) % 13) - 6

/-- A deliberately different — but valid — base kernel: the textbook triple-loop
naive product, computed entrywise with `Fin.foldl`. It agrees with `mul` (both sum
`∑ₜ X[i,t]·Y[t,j]`), so plugging it in cross-checks the recursion, the block
assembly, and the kernel itself against the reference `mul`. -/
private def naiveKernel {n m k : Nat} (X : Matrix Int n m) (Y : Matrix Int m k) :
    Matrix Int n k :=
  Matrix.ofFn fun i j => Fin.foldl m (fun acc t => acc + X[(i, t)] * Y[(t, j)]) (0 : Int)

/-- Custom-kernel config with an explicit small cutoff: recursion fires on the
small fixtures while the base leaves hit `naiveKernel`. -/
private def cfgNaive : StrassenConfig Int := { cutoff := 4, baseMul := naiveKernel }

/-- Deep-recursion config: `cutoff := 0` splits until a dimension reaches the
config-independent `≤ 1` base condition. -/
private def cfgDeep : StrassenConfig Int := { cutoff := 0, baseMul := naiveKernel }

-- Even, odd, and prime square dimensions under both custom configs.
#guard let A := genInt 0 8 8; let B := genInt 1 8 8; mulStrassen cfgNaive A B = A * B
#guard let A := genInt 0 8 8; let B := genInt 1 8 8; mulStrassen cfgDeep A B = A * B
#guard let A := genInt 0 9 9; let B := genInt 1 9 9; mulStrassen cfgNaive A B = A * B
#guard let A := genInt 0 9 9; let B := genInt 1 9 9; mulStrassen cfgDeep A B = A * B
#guard let A := genInt 0 5 5; let B := genInt 1 5 5; mulStrassen cfgNaive A B = A * B
#guard let A := genInt 0 5 5; let B := genInt 1 5 5; mulStrassen cfgDeep A B = A * B

-- Rectangular with distinct `n`, `m`, `k` (each ≥ 4 so `cfgNaive` recurses).
#guard let A := genInt 0 5 7; let B := genInt 1 7 9; mulStrassen cfgNaive A B = A * B
#guard let A := genInt 0 5 7; let B := genInt 1 7 9; mulStrassen cfgDeep A B = A * B

-- Zero contraction axis (empty product) and a zero output axis, under `cfgDeep`
-- (hits the `m ≤ 1` / `n ≤ 1` base immediately) and `strassenDefault`.
#guard let A := genInt 0 3 0; let B := genInt 1 0 3
  mulStrassen cfgDeep A B = A * B
#guard let A := genInt 0 3 0; let B := genInt 1 0 3
  mulStrassen (strassenDefault (R := Int)) A B = A * B
#guard let A := genInt 0 0 3; let B := genInt 1 3 2
  mulStrassen cfgDeep A B = A * B

-- 1×1: the config-independent `≤ 1` base condition, under both `cfgDeep` and default.
#guard let A := genInt 0 1 1; let B := genInt 1 1 1
  mulStrassen cfgDeep A B = A * B
#guard let A := genInt 0 1 1; let B := genInt 1 1 1
  mulStrassen (strassenDefault (R := Int)) A B = A * B

-- A square past the default cutoff so `strassenDefault` actually recurses.
#guard let A := genInt 0 96 96; let B := genInt 1 96 96
  mulStrassen (strassenDefault (R := Int)) A B = A * B

end Matrix
