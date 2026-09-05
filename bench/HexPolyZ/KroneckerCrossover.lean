/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import HexPolyZ
import HexPolyZ.KroneckerMulti
import HexPolyZ.NttMul

/-!
Kernel microbenchmark for the integer dense polynomial product: schoolbook
convolution and KS1/KS2/KS3/KS4, by degree and coefficient width.

This is the measurement behind `Hex.ZPoly.kroneckerSizeCutoff` and
`Hex.ZPoly.kroneckerBitCutoff` (see `HexPolyZ/SPEC/hex-poly-z.md`). It is a
manual diagnostic driver, not a CI job and not a `lean-bench` registration: it
sweeps a two-dimensional grid looking for a crossover rather than fitting one
operation against a declared complexity model, so it does not belong in the
scientific harness.

The base grid locates the schoolbook/KS1 boundary.  Additional wide-coefficient
cells make the packed integers cross the GMP Karatsuba, Toom, and FFT ranges
and compare all four multipoint Kronecker kernels there.  The exact internal
GMP thresholds are host-tuned, so the durable record retains the degree, width,
and every forced-kernel time rather than assigning a regime in Lean. Emits one
JSON document on stdout; `scripts/bench/kronecker_crossover.py` pins it to a
verified-idle core and wraps the result with environment metadata.
-/

open Hex

namespace Hex.KroneckerCrossover

/-- Deterministic xorshift over `UInt64`. -/
def nextRand (s : UInt64) : UInt64 :=
  let s := s ^^^ (s <<< 13)
  let s := s ^^^ (s >>> 7)
  s ^^^ (s <<< 17)

/-- A pseudorandom odd natural number of `bits` bits. -/
partial def randNat (bits : Nat) (s : UInt64) : Nat × UInt64 :=
  let rec go (acc : Nat) (need : Nat) (s : UInt64) : Nat × UInt64 :=
    if need == 0 then (acc, s)
    else
      let s := nextRand s
      let take := min need 32
      go (acc * 2 ^ take + (s.toNat) % (2 ^ take)) (need - take) s
  go 0 bits s

/-- `n` pseudorandom coefficients of `bits` bits each, alternating in sign when
`signed` is set. -/
def randPoly (n bits : Nat) (seed : UInt64) (signed : Bool) : ZPoly := Id.run do
  let mut out : Array Int := Array.emptyWithCapacity n
  let mut s := seed
  for i in [0:n] do
    let (v, s') := randNat bits s
    let z := Int.ofNat (v ||| 1)
    out := out.push (if signed && i % 2 == 0 then -z else z)
    s := s'
  return DensePoly.ofCoeffs out

/-- Forced multiplication kernels represented in the diagnostic grid. -/
inductive Kernel where
  | schoolbook
  | ks1
  | ks2
  | ks3
  | ks4

/-- Run one forced kernel without consulting the production dispatcher. -/
def Kernel.mul : Kernel → ZPoly → ZPoly → ZPoly
  | .schoolbook => DensePoly.mulImpl
  | .ks1 => ZPoly.mulKroneckerAt 0 0
  | .ks2 => ZPoly.mulKS2
  | .ks3 => ZPoly.mulKS3
  | .ks4 => ZPoly.mulKS4

/-- Time `reps` products with one forced kernel.

Each iteration selects its left operand by a branch on the running checksum, so
the product depends on the previous iteration and cannot be hoisted out of the
loop — without this the compiler lifts the whole loop body and the measured
times are a flat few nanoseconds at every degree.

The checksum is seeded from the clock and only ever advanced by an even amount,
so the branch is not statically decidable but always takes the same side at
runtime: every iteration multiplies the same pair, and the forced kernels compare
like for like. Seeding it from a literal would let a sufficiently strong
optimiser prove the branch constant and hoist the loop body again. The caller
passes one seed to every kernel so their checksums remain comparable. -/
def timeProduct (seed : Int) (reps : Nat) (kernel : Kernel) (p q : ZPoly) :
    IO (Float × Int) := do
  let mut chk : Int := seed
  let _ := kernel.mul p q
  let t0 ← IO.monoNanosNow
  for _ in [0:reps] do
    let p' := if chk % 2 == 1 then q else p
    let r := kernel.mul p' q
    chk := chk + 2 * r.coeff 0
  let t1 ← IO.monoNanosNow
  return (Float.ofNat (t1 - t0) / Float.ofNat reps, chk)

/-- One grid cell: all forced kernels plus the schoolbook/KS1 ratio. -/
def cell (n bits reps : Nat) (signed : Bool) : IO String := do
  let p := randPoly n bits 0x243f6a8885a308d3 signed
  let q := randPoly n bits 0x13198a2e03707344 signed
  -- One clock-derived even seed, shared by every kernel: the branch inside the
  -- timing loop is then not statically decidable, every kernel takes the same
  -- side of it at runtime, and their checksums stay directly comparable.
  let seed : Int := 2 * Int.ofNat ((← IO.monoNanosNow) % 3)
  let (school, cSchool) ← timeProduct seed reps .schoolbook p q
  let (ks1, cKs1) ← timeProduct seed reps .ks1 p q
  let (ks2, cKs2) ← timeProduct seed reps .ks2 p q
  let (ks3, cKs3) ← timeProduct seed reps .ks3 p q
  let (ks4, cKs4) ← timeProduct seed reps .ks4 p q
  if cSchool != cKs1 || cSchool != cKs2 || cSchool != cKs3 || cSchool != cKs4 then
    throw <| IO.userError s!"kernel disagreement at n={n} bits={bits} signed={signed}"
  return "{\"n\": " ++ toString n ++ ", \"bits\": " ++ toString bits
    ++ ", \"signed\": " ++ (if signed then "true" else "false")
    ++ ", \"reps\": " ++ toString reps
    ++ ", \"schoolbook_nanos\": " ++ toString school
    ++ ", \"kronecker_nanos\": " ++ toString ks1
    ++ ", \"ks1_nanos\": " ++ toString ks1
    ++ ", \"ks2_nanos\": " ++ toString ks2
    ++ ", \"ks3_nanos\": " ++ toString ks3
    ++ ", \"ks4_nanos\": " ++ toString ks4
    ++ ", \"ratio\": " ++ toString (school / ks1) ++ "}"

/-- Repetition count chosen so each cell takes roughly the same wall time. -/
def repsFor (n bits : Nat) : Nat :=
  let work := n * n * (bits + 8)
  max 1 (min 20000 (40000000 / (work + 1)))

/-- The degree by coefficient-width grid the cutoffs are read off. -/
def grid : List (Nat × Nat) :=
  let widths := [4, 8, 12, 14, 15, 16, 17, 18, 19, 20, 22, 24, 32, 48, 64, 92,
    128, 181, 256, 400]
  let degrees := [4, 8, 12, 16, 20, 24, 28, 32, 40, 48, 64, 90, 128]
  widths.flatMap fun b => degrees.map fun n => (n, b)

/-- Wide-coefficient cells whose packed operands extend into host-tuned GMP
Karatsuba, Toom, and FFT ranges.  A diagonal avoids the prohibitive full cross
product while growing packed size from roughly 16K through one million bits. -/
def gmpTargets : List (Nat × Nat) :=
  [(32, 512), (64, 1024), (128, 2048), (128, 4096), (128, 8192)]

/-- The shapes the Hensel lift and recombination actually issue, at both signs. -/
def targets : List (Nat × Nat) :=
  [(90, 92), (90, 181), (89, 46), (60, 120), (56, 200), (178, 92), (120, 20), (105, 20)]

def runGrid : IO Unit := do
  let mut rows : Array String := #[]
  for shape in grid do
    rows := rows.push (← cell shape.1 shape.2 (repsFor shape.1 shape.2) false)
  for shape in gmpTargets do
    rows := rows.push (← cell shape.1 shape.2 (repsFor shape.1 shape.2) false)
    rows := rows.push (← cell shape.1 shape.2 (repsFor shape.1 shape.2) true)
  for shape in targets do
    rows := rows.push (← cell shape.1 shape.2 (repsFor shape.1 shape.2) false)
    rows := rows.push (← cell shape.1 shape.2 (repsFor shape.1 shape.2) true)
  IO.println ("{\"size_cutoff\": " ++ toString ZPoly.kroneckerSizeCutoff
    ++ ", \"bit_cutoff\": " ++ toString ZPoly.kroneckerBitCutoff
    ++ ", \"cells\": [" ++ String.intercalate ",\n  " rows.toList ++ "]}")

/-- Run the full durable grid, or one wide signed-agreement cell for a quick
executable check. -/
def main (args : List String) : IO UInt32 := do
  if args == ["--smoke"] then
    IO.println (← cell 32 512 1 true)
  else if args.isEmpty then
    runGrid
  else
    throw <| IO.userError "usage: hexpolyz_kronecker_crossover [--smoke]"
  return 0

end Hex.KroneckerCrossover

def main (args : List String) : IO UInt32 := Hex.KroneckerCrossover.main args
