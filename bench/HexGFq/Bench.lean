/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import HexGFq.Basic
import LeanBench

/-!
Benchmark registrations for `hex-gfq`.

These registrations all instantiate the wrapper at the degree-one committed
entries, `GFq 2 1` and `GF2q 1`, and vary the size of the representative fed
to the constructor rather than the size of the field. That measures the
constructor and projection surface `hex-gfq` itself contributes; the modulus
arithmetic underneath it is measured by `hex-gfq-field` and `hex-gf2`.

The committed table is wider than what is exercised here: `hex-conway` commits
36 generic entries (`p` in `2, 3, 5, 7, 11, 13`, `n` in `1` to `6`), all
reachable through `GFq.CommittedEntry` instances, and this library exposes
`GFq.PackedGF2Entry` instances for `n` in `1` to `6`. Sweeping the bench
across that range is outstanding work, not a limit of the public API.

* `runGFqOfPolyReprChecksum`: generic `GFq.ofPoly` plus `GFq.repr` on a
  degree-`n` binary representative, `O(n)` against the fixed linear modulus.
* `runGF2qOfWordReprChecksum`: packed `GF2q.ofWord` plus `GF2q.repr` on the
  committed single-word `GF2q 1` entry.
* `runGF2qOfWordReprProfileChecksum`: the same packed constructor/projection
  surface registered parametrically so timed-region-filtered profiling can
  exercise it at a representative word input.
* `runPackedGenericSharedChecksum`: packed and generic constructor/projection
  checksums on the same binary representative family, `O(n)` on the generic
  degree-`n` representative.
-/

namespace Hex
namespace GfqBench

private abbrev Entry21 : Conway.SupportedEntry 2 1 :=
  Conway.supportedEntry_2_1

private abbrev Generic21 : Type :=
  GFq 2 1 Entry21

private abbrev Packed21 : Type :=
  GF2q 1

private instance boundsTwo : ZMod64.Bounds 2 where
  pPos := by decide
  pLtR := by decide

instance {p : Nat} [ZMod64.Bounds p] : Hashable (ZMod64 p) where
  hash a := hash a.toNat

instance {p : Nat} [ZMod64.Bounds p] : Hashable (FpPoly p) where
  hash f := hash f.toArray

/-- Deterministic mixing over machine words for compact benchmark observables. -/
def mixWord (acc x : UInt64) : UInt64 :=
  acc * 0x9E3779B97F4A7C15 + x + 0xBF58476D1CE4E5B9

/-- Stable checksum for a generic polynomial representative. -/
def checksumPoly {p : Nat} [ZMod64.Bounds p] (f : FpPoly p) : UInt64 :=
  f.toArray.foldl (fun acc c => mixWord acc (UInt64.ofNat c.toNat)) 0

/-- Stable checksum for a packed binary polynomial. -/
def checksumGF2Poly (f : GF2Poly) : UInt64 :=
  f.toWords.foldl mixWord 0

/-- Binary coefficient generator keyed by representative size, index, and salt. -/
def coeffBit (n i salt : Nat) : Bool :=
  ((i + 1) * 9_176 + (salt + 3) * 1_021 + n * 29 + i * i * 17) % 5 < 2

/-- Deterministic dense binary representative with `n` scanned coefficients. -/
def binaryPoly (n salt : Nat) : FpPoly 2 :=
  FpPoly.ofCoeffs <| (Array.range n).map fun i =>
    if coeffBit n i salt then
      ZMod64.ofNat 2 1
    else
      ZMod64.ofNat 2 0

/-- Deterministic dense representative over an odd prime, with `n` coefficients
spread across the whole residue range so reduction has work to do. -/
def oddPoly (q n salt : Nat) [ZMod64.Bounds q] : FpPoly q :=
  FpPoly.ofCoeffs <| (Array.range n).map fun i =>
    ZMod64.ofNat q ((i * 7 + salt * 13 + 1) % q)

/-- Single-word representative with a deterministic prefix and a high bit at `n`. -/
def binaryWord (n salt : Nat) : UInt64 :=
  let hi := if n = 0 then 0 else Nat.min n 63
  let base :=
    UInt64.ofNat
      (((n + 1) * 1_103_515_245 + (salt + 97) * 65_537 + n * n * 31) %
        18_446_744_073_709_551_557)
  base ||| ((1 : UInt64) <<< hi.toUInt64)

/-- Prepared shared packed/generic representative input. -/
structure SharedInput where
  poly : FpPoly 2
  word : UInt64
  deriving Hashable

/-- Prepared generic constructor/projection input. -/
def prepGFqInput (n : Nat) : FpPoly 2 :=
  binaryPoly n 11

/-- Prepared packed constructor/projection input. -/
def prepGF2qWordInput (n : Nat) : UInt64 :=
  binaryWord n 37

/-- Prepared shared-domain packed-vs-generic input. -/
def prepSharedInput (n : Nat) : SharedInput :=
  { poly := binaryPoly n 59, word := binaryWord n 59 }

/- The three fixed targets below were `(_ : Unit) → UInt64` over closed terms,
which the compiler folds: each reported the same floor time regardless of what
it named. They now follow the `Unit → IO α` shape this file's header
prescribes, with inputs held in `IO.Ref`s. -/

private instance : Nonempty (FpPoly 2) := ⟨binaryPoly 1 0⟩
private instance : Nonempty (FpPoly 13) := ⟨oddPoly 13 1 0⟩
private instance : Nonempty GF2Poly := ⟨GF2q.modulus (n := 1)⟩

private initialize genModulusRef : IO.Ref (FpPoly 2) ← IO.mkRef (GFq.modulus Entry21)
private initialize packModulusRef : IO.Ref GF2Poly ← IO.mkRef (GF2q.modulus (n := 1))
private initialize packLowerRef : IO.Ref UInt64 ← IO.mkRef (GF2q.lower (n := 1))
private initialize wordRef : IO.Ref UInt64 ← IO.mkRef (binaryWord 63 37)

/-- Benchmark target: selected generic Conway modulus checksum. -/
def runGenericModulusChecksum : Unit → IO UInt64 := fun () => do
  let m ← genModulusRef.get
  return checksumPoly m

/-- Benchmark target: selected packed Conway modulus checksum. -/
def runPackedModulusChecksum : Unit → IO UInt64 := fun () => do
  let m ← packModulusRef.get
  let lo ← packLowerRef.get
  return mixWord lo (checksumGF2Poly m)

/-- Benchmark target: generic constructor plus representative projection. -/
def runGFqOfPolyReprChecksum (g : FpPoly 2) : UInt64 :=
  checksumPoly (GFq.repr (GFq.ofPoly Entry21 g : Generic21))

/-- Benchmark target: packed constructor plus representative projection. -/
def runGF2qOfWordReprChecksum : Unit → IO UInt64 := fun () => do
  let w ← wordRef.get
  return GF2q.repr (GF2q.ofWord (n := 1) w : Packed21)

/-- Parametric profiling target for the packed constructor/projection surface. -/
def runGF2qOfWordReprProfileChecksum (word : UInt64) : UInt64 :=
  GF2q.repr (GF2q.ofWord (n := 1) word : Packed21)

/-! # Degree beyond one

The targets above sit at `GFq 2 1` and `GF2q 1`, where the modulus is linear
and reduction is trivial, so they measure the constructor and projection
surface and nothing else. These add the top of the committed range, where
reduction actually runs: the deepest binary entry, the largest odd-prime
entry, and the ergonomic `GFqC` spelling, which had no coverage at all. -/

private abbrev Entry28 : Conway.SupportedEntry 2 8 :=
  Conway.supportedEntry_2_8

private abbrev Generic28 : Type :=
  GFq 2 8 Entry28

private abbrev Packed28 : Type :=
  GF2q 8

private abbrev Entry136 : Conway.SupportedEntry 13 6 :=
  Conway.supportedEntry_13_6

private abbrev Generic136 : Type :=
  GFq 13 6 Entry136

/- Inputs are threaded through `IO.Ref`s and the targets return `IO`, following
the `Unit → IO α` pattern this file's header describes. Without that, the whole
computation is a closed term and Lean folds it: the four targets below then all
report the same floor time regardless of degree or prime, which is what the
existing fixed targets in this file do. -/

private initialize poly28Ref : IO.Ref (FpPoly 2) ← IO.mkRef (binaryPoly 200 59)
private initialize word8Ref : IO.Ref UInt64 ← IO.mkRef (binaryWord 200 37)
private initialize poly136Ref : IO.Ref (FpPoly 13) ← IO.mkRef (oddPoly 13 40 41)

/-- Benchmark target: generic constructor plus projection at the deepest
committed binary degree, where reduction modulo a degree-8 modulus runs. -/
def runGFqOfPolyRepr_2_8_Checksum : Unit → IO UInt64 := fun () => do
  let g ← poly28Ref.get
  return checksumPoly (GFq.repr (GFq.ofPoly Entry28 g : Generic28))

/-- Benchmark target: packed constructor plus projection at degree 8. -/
def runGF2qOfWordRepr_8_Checksum : Unit → IO UInt64 := fun () => do
  let w ← word8Ref.get
  return GF2q.repr (GF2q.ofWord (n := 8) w : Packed28)

/-- Benchmark target: generic constructor plus projection at the largest
committed odd-prime entry, `GF(13^6)`. This is the widest coefficient
arithmetic in the table. -/
def runGFqOfPolyRepr_13_6_Checksum : Unit → IO UInt64 := fun () => do
  let g ← poly136Ref.get
  return checksumPoly (GFq.repr (GFq.ofPoly Entry136 g : Generic136))

/-- Benchmark target: the ergonomic `GFqC` spelling, which resolves its
committed entry by instance synthesis rather than taking it explicitly. Same
work as the explicit form; this measures that the convenience costs nothing. -/
def runGFqCOfPolyReprChecksum : Unit → IO UInt64 := fun () => do
  let g ← poly136Ref.get
  return checksumPoly (GFqC.repr (GFqC.ofPoly (p := 13) (n := 6) g))

/-- Benchmark target: packed and generic checksums on shared binary inputs. -/
def runPackedGenericSharedChecksum (input : SharedInput) : UInt64 :=
  let packed := GF2q.repr (GF2q.ofWord (n := 1) input.word : Packed21)
  let generic := checksumPoly (GFq.repr (GFq.ofPoly Entry21 input.poly : Generic21))
  mixWord packed generic

setup_fixed_benchmark runGFqOfPolyRepr_2_8_Checksum where {
  repeats := 5
  maxSecondsPerCall := 2.0
  expectedHash := none
}

setup_fixed_benchmark runGF2qOfWordRepr_8_Checksum where {
  repeats := 5
  maxSecondsPerCall := 2.0
  expectedHash := none
}

setup_fixed_benchmark runGFqOfPolyRepr_13_6_Checksum where {
  repeats := 5
  maxSecondsPerCall := 2.0
  expectedHash := none
}

setup_fixed_benchmark runGFqCOfPolyReprChecksum where {
  repeats := 5
  maxSecondsPerCall := 2.0
  expectedHash := none
}

setup_fixed_benchmark runGenericModulusChecksum where {
  repeats := 5
  maxSecondsPerCall := 2.0
  expectedHash := none
}

setup_fixed_benchmark runPackedModulusChecksum where {
  repeats := 5
  maxSecondsPerCall := 2.0
  expectedHash := none
}

setup_fixed_benchmark runGF2qOfWordReprChecksum where {
  repeats := 5
  maxSecondsPerCall := 2.0
  expectedHash := none
}

/-
The fixed packed target above is the benchmark verdict surface. This
parametric companion exposes the same committed `GF2q 1` operation through the
profiling wrapper so timed-region sidecars can sample it across word inputs.
The underlying `GF2q.ofWord`/`GF2q.repr` pair operates on a single packed word,
so the declared cost model is `O(1)` in the parameter: the schedule only varies
which word reaches `ofWord`/`repr` and does not scale the per-call work, which
remains constant.
-/
setup_benchmark runGF2qOfWordReprProfileChecksum _n => 1
  with prep := prepGF2qWordInput
  where {
    paramFloor := 1
    paramCeiling := 63
    paramSchedule := .custom #[1, 2, 4, 8, 16, 32, 63]
    maxSecondsPerCall := 2.0
    targetInnerNanos := 100000000
    signalFloorMultiplier := 1.0
  }

/-
For the committed `GFq 2 1` entry the selected modulus is linear, so reduction
of an input representative scans its `n` coefficients and folds them modulo
`x + 1`; `repr` is a projection of the stored canonical representative.
-/
setup_benchmark runGFqOfPolyReprChecksum n => n
  with prep := prepGFqInput
  where {
    paramFloor := 4
    paramCeiling := 256
    paramSchedule := .custom #[4, 8, 16, 32, 64, 128, 256]
    maxSecondsPerCall := 2.0
    targetInnerNanos := 100000000
    signalFloorMultiplier := 1.0
  }

/-
The shared checksum runs the public packed and generic constructor/projection
surfaces on the same binary representative family. The generic degree-`n`
representative scan dominates the fixed single-word packed projection.
-/
setup_benchmark runPackedGenericSharedChecksum n => n
  with prep := prepSharedInput
  where {
    paramFloor := 4
    paramCeiling := 256
    paramSchedule := .custom #[4, 8, 16, 32, 64, 128, 256]
    maxSecondsPerCall := 2.0
    targetInnerNanos := 100000000
    signalFloorMultiplier := 1.0
  }

end GfqBench
end Hex

def main (args : List String) : IO UInt32 :=
  LeanBench.Cli.dispatch args
