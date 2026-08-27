/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import HexModular
import HexModularBench.Comparator
import LeanBench

/-!
Native benchmark registrations for `hex-modular`.

The registrations cover every compiled operation in the SPEC API and its four
input families.  Input construction is hoisted through `prep`; timed targets
return compact hashes of their exact answers.

* **Incremental CRT:** scalar and fixed-width vector accumulation over `k`
  pairwise-coprime prime powers of roughly 16--30 bits.
* **Balanced batch CRT:** cold plan construction and warm scalar/vector
  reconstruction over the same deterministic modulus and residue families.
* **Vector CRT:** the coordinate count varies independently at a fixed CRT
  depth, making reuse of one extended gcd observable.
* **Rational reconstruction:** early and full Euclidean runs on Fibonacci
  inputs whose bit size is the varied parameter.
* **Failure cost:** the same full run with an impossible numerator bound.

The benchmark has no Mathlib import and no proof/tactic track.
-/

namespace Hex.ModularBench

open Hex
open Hex.Modular

def mixWord (acc x : UInt64) : UInt64 :=
  acc * 0x9E3779B97F4A7C15 + x + 0xBF58476D1CE4E5B9

def hashInt (value : Int) : UInt64 :=
  hash value

def hashCrt (state : Crt) : UInt64 :=
  mixWord (hash state.modulus) (hashInt state.value)

def hashCrtVec {k : Nat} (state : CrtVec k) : UInt64 :=
  state.value.foldl (fun acc value => mixWord acc (hashInt value))
    (hash state.modulus)

def hashRat (value : Rat) : UInt64 :=
  mixWord (hashInt value.num) (hash value.den)

def hashRatVec {k : Nat} (value : Vector Int k × Int) : UInt64 :=
  value.1.foldl (fun acc entry => mixWord acc (hashInt entry))
    (hashInt value.2)

def hashOption (hashValue : α → UInt64) : Option α → UInt64
  | none => 0
  | some value => mixWord 1 (hashValue value)

/-! Deterministic prepared inputs. -/

/-- First `count` primes, found outside every timed region. -/
def smallPrimes (count : Nat) : Array Nat :=
  ((List.range (32 * count + 100)).drop 2).filter Hex.Nat.isPrimeTrial
    |>.take count |>.toArray

/-- A power of `p` below `2^30`. Distinct inputs remain pairwise coprime,
while every CRT step receives a word-sized modulus of realistic size. -/
def wordPrimePower (p : Nat) : Nat :=
  p ^ (30 / max 1 p.log2)

def moduli (count : Nat) : Array Nat :=
  (smallPrimes count).map wordPrimePower

def residue (index modulus salt : Nat) : Int :=
  Int.ofNat ((index * 1_103_515_245 + salt * 12_345 + 97) % modulus)

structure SymModInput where
  value : Int
  modulus : Nat
  deriving Hashable

def prepSymMod (bits : Nat) : SymModInput :=
  let modulus := 2 ^ bits - 1
  { value := Int.ofNat (2 ^ (2 * bits) + 2 ^ bits + 17), modulus }

def runSymMod (input : SymModInput) : UInt64 :=
  hashInt (symMod input.value input.modulus)

structure ScalarCrtInput where
  entries : Array (Int × Nat)
  deriving Hashable

def prepScalarCrt (count : Nat) : ScalarCrtInput :=
  { entries := (moduli count).mapIdx fun index modulus =>
      (residue index modulus 11, modulus) }

def runScalarCrt (input : ScalarCrtInput) : UInt64 :=
  let answer := input.entries.foldl
    (fun state entry => state.bind fun current => current.push entry.1 entry.2)
    (some Crt.init)
  hashOption hashCrt answer

structure VectorCrtInput where
  width : Nat
  entries : Array (Vector Int width × Nat)

instance : Hashable VectorCrtInput where
  hash input := input.entries.foldl
    (fun acc entry => entry.1.foldl
      (fun inner value => mixWord inner (hashInt value))
      (mixWord acc (hash entry.2)))
    (hash input.width)

def prepVectorCrt (width depth : Nat) : VectorCrtInput :=
  { width
    entries := (moduli depth).mapIdx fun index modulus =>
      (Vector.ofFn fun coordinate =>
        residue (index + coordinate.val) modulus 23, modulus) }

def prepVectorCrtWidth (width : Nat) : VectorCrtInput :=
  prepVectorCrt width 16

def prepVectorCrtDepth (depth : Nat) : VectorCrtInput :=
  prepVectorCrt 32 depth

def runVectorCrt (input : VectorCrtInput) : UInt64 :=
  let answer := input.entries.foldl
    (fun state entry => state.bind fun current => current.push entry.1 entry.2)
    (some (CrtVec.init input.width))
  hashOption hashCrtVec answer

def runVectorCrtWidth (input : VectorCrtInput) : UInt64 :=
  runVectorCrt input

def runVectorCrtDepth (input : VectorCrtInput) : UInt64 :=
  runVectorCrt input

/-- Prepared one-lane batch CRT input with all sibling inverses cached. -/
structure BatchScalarInput where
  plan : CrtPlan
  residues : Array Int

instance : Hashable BatchScalarInput where
  hash input := input.residues.foldl
    (fun acc value => mixWord acc (hashInt value)) (hash input.plan.moduli)

/-- Build the balanced scalar plan outside the warm reconstruction target. -/
def prepBatchScalar (count : Nat) : Option BatchScalarInput := do
  let entries := (prepScalarCrt count).entries
  let moduli := entries.map (·.2)
  let plan ← CrtPlan.build? moduli
  pure { plan, residues := entries.map (·.1) }

/-- Benchmark target: validate moduli and construct the balanced CRT tree. -/
def runCrtPlanBuild (input : ScalarCrtInput) : UInt64 :=
  let built := CrtPlan.build? (input.entries.map (·.2))
  hashOption (fun plan => mixWord (hash plan.modulus) (hash plan.moduli)) built

/-- Benchmark target: warm balanced scalar reconstruction.  Its checksum is
identical to the incremental scalar target on the shared residue family. -/
def runBatchScalarCrt (input : Option BatchScalarInput) : UInt64 :=
  match input with
  | none => 0
  | some prepared =>
      hashOption
        (fun value => mixWord (hash prepared.plan.modulus) (hashInt value))
        (prepared.plan.reconstruct? prepared.residues)

/-- Prepared many-lane batch CRT input with one shared balanced plan. -/
structure BatchVectorInput where
  width : Nat
  plan : CrtPlan
  residues : Array (Vector Int width)

instance : Hashable BatchVectorInput where
  hash input := input.residues.foldl
    (fun acc row => row.foldl (fun inner value => mixWord inner (hashInt value)) acc)
    (mixWord (hash input.width) (hash input.plan.moduli))

def prepBatchVector (width depth : Nat) : Option BatchVectorInput := do
  let input := prepVectorCrt width depth
  let moduli := input.entries.map (·.2)
  let plan ← CrtPlan.build? moduli
  pure { width, plan, residues := input.entries.map (·.1) }

/-- Fixed-depth convolution-width batch CRT fixture. -/
def prepBatchVectorWidth (width : Nat) : Option BatchVectorInput :=
  prepBatchVector width 16

/-- Benchmark target: warm balanced vector reconstruction, reusing every
tree inverse across all coefficient lanes. -/
def runBatchVectorCrtWidth (input : Option BatchVectorInput) : UInt64 :=
  match input with
  | none => 0
  | some prepared =>
      hashOption
        (fun values => values.foldl (fun acc value => mixWord acc (hashInt value))
          (hash prepared.plan.modulus))
        (prepared.plan.reconstructVec? prepared.residues)

/-- Consecutive Fibonacci numbers after `steps` additions. -/
def fibonacciPair (steps : Nat) : Nat × Nat :=
  (List.range steps).foldl (fun pair _ => (pair.2, pair.1 + pair.2)) (1, 1)

structure ReconInput where
  residue : Int
  modulus : Nat
  numeratorBound : Int
  denominatorBound : Int
  deriving Hashable

/-- Fibonacci inputs have a worst-shaped Euclidean quotient stream. The
factor `3/2` converts requested bits to a conservative Fibonacci index. -/
def prepReconLate (bits : Nat) : ReconInput :=
  let pair := fibonacciPair (3 * bits / 2 + 3)
  { residue := Int.ofNat pair.1
    modulus := pair.2
    numeratorBound := 1
    denominatorBound := Int.ofNat pair.2 }

def prepReconEarly (bits : Nat) : ReconInput :=
  { residue := 17
    modulus := 2 ^ bits - 1
    numeratorBound := 17
    denominatorBound := 1 }

def prepReconFailure (bits : Nat) : ReconInput :=
  let input := prepReconLate bits
  { input with numeratorBound := 0 }

def prepReconCheck (bits : Nat) : ReconInput :=
  let modulus := 2 ^ bits - 3
  { residue := Int.ofNat ((2 * modulus + 1) / 3)
    modulus
    numeratorBound := 1
    denominatorBound := 3 }

def runEuclid (input : ReconInput) : UInt64 :=
  let row := euclidUntil (Int.ofNat input.modulus) input.residue
    input.numeratorBound
  mixWord (hashInt row.r) (hashInt row.t)

def runRatRecon (input : ReconInput) : UInt64 :=
  hashOption hashRat <|
    ratRecon? input.residue input.modulus input.numeratorBound
      input.denominatorBound

def runRatReconLate (input : ReconInput) : UInt64 :=
  runRatRecon input

def runRatReconFailure (input : ReconInput) : UInt64 :=
  runRatRecon input

def runRatReconWide (input : ReconInput) : UInt64 :=
  hashOption hashRat (ratReconWide? input.residue input.modulus)

def runRatReconMaxQuot (input : ReconInput) : UInt64 :=
  hashOption hashRat (ratReconMaxQuot? input.residue input.modulus)

def runRatReconCheck (input : ReconInput) : UInt64 :=
  let candidate := Rat.divInt 1 3
  hash (ratReconCheck input.residue input.modulus input.numeratorBound
    input.denominatorBound candidate)

structure ReconVecInput where
  width : Nat
  residues : Vector Int width
  modulus : Nat

instance : Hashable ReconVecInput where
  hash input := input.residues.foldl
    (fun acc entry => mixWord acc (hashInt entry)) (hash input.modulus)

def prepReconVec (width : Nat) : ReconVecInput :=
  { width
    residues := Vector.ofFn fun i => Int.ofNat (i.val % 17 + 1)
    modulus := 2 ^ 256 - 1 }

def runRatReconVec (input : ReconVecInput) : UInt64 :=
  hashOption hashRatVec <|
    ratReconVec? input.residues input.modulus 17 1

structure LoopInput where
  width : Nat
  supply : Array Nat

instance : Hashable LoopInput where
  hash input := input.supply.foldl
    (fun acc modulus => mixWord acc (hash modulus)) (hash input.width)

def prepLoop (depth : Nat) : LoopInput :=
  { width := 8, supply := moduli depth }

def runCrtLoop (input : LoopInput) : UInt64 :=
  let image (modulus : Nat) : Option (Vector Int input.width) :=
    some (Vector.ofFn fun i =>
      residue (modulus % 997 + i.val) modulus 41)
  let accept (_state : CrtVec input.width) : Option Nat := none
  hash (crtLoop image accept input.supply input.supply.size)

/-! Scientific registrations. -/

/- One division reduces a `2b`-bit integer modulo a `b`-bit modulus. The
The `b * sqrt b` complexity model is the Karatsuba-range surrogate for GMP's multiplication
cost `M(b)`, which bounds this balanced division on the declared ladder. -/
setup_benchmark runSymMod bits => bits * Nat.sqrt bits
  with prep := prepSymMod
  where {
    paramSchedule := .custom #[64, 128, 256, 512, 1024, 2048, 4096, 8192,
      16384, 32768, 65536]
    maxSecondsPerCall := 4.0
    targetInnerNanos := 200000000
    signalFloorMultiplier := 1.0
    verdictWarmupFraction := 0.35
    slopeTolerance := 0.25
    outerTrials := 3
  }

/- After `j` fixed-word moduli, the accumulator has `O(j)` words and one push
does `O(j)` large-integer work. Summing over `j < k` gives `O(k²)`. -/
setup_benchmark runScalarCrt k => k * k
  with prep := prepScalarCrt
  where {
    paramSchedule := .custom #[4, 8, 16, 32, 64, 128, 256, 512, 1024,
      2048, 4096, 8192]
    maxSecondsPerCall := 12.0
    targetInnerNanos := 200000000
    signalFloorMultiplier := 1.0
    verdictWarmupFraction := 0.8
    slopeTolerance := 0.25
    outerTrials := 3
  }

/- Cost model: building a `CrtPlan` validates every modulus pair, giving a
quadratic upper bound in `k`, then precomputes a balanced product/inverse tree.
This cold target keeps construction separate from warm reconstruction. -/
setup_benchmark runCrtPlanBuild k => k * k
  with prep := prepScalarCrt
  where {
    paramSchedule := .custom #[4, 8, 16, 32, 64, 128, 256, 512, 1024,
      2048, 4096]
    maxSecondsPerCall := 12.0
    targetInnerNanos := 200000000
    signalFloorMultiplier := 1.0
    outerTrials := 3
    tags := #["crt", "balanced", "cold-plan"]
  }

/- With the plan already built, every scalar lane follows the balanced tree.
The quadratic model is a conservative upper bound on the fixed-word modulus
ladder and shares every rung with the incremental comparator. -/
setup_benchmark runBatchScalarCrt k => k * k
  with prep := prepBatchScalar
  where {
    paramSchedule := .custom #[4, 8, 16, 32, 64, 128, 256, 512, 1024,
      2048, 4096]
    maxSecondsPerCall := 12.0
    targetInnerNanos := 200000000
    signalFloorMultiplier := 1.0
    outerTrials := 3
    tags := #["crt", "balanced", "scalar", "warm-plan"]
  }

/- At fixed depth, `CrtVec.push` computes one inverse and performs a constant
number of fixed-size multiply-adds per coordinate, hence `O(n)`. -/
setup_benchmark runVectorCrtWidth n => n
  with prep := prepVectorCrtWidth
  where {
    paramSchedule := .custom #[1, 4, 16, 64, 256, 1024, 2048, 4096]
    maxSecondsPerCall := 6.0
    targetInnerNanos := 200000000
    signalFloorMultiplier := 1.0
    verdictWarmupFraction := 0.6
    slopeTolerance := 0.25
    outerTrials := 3
  }

/- At fixed depth the cached balanced tree performs a constant number of
fixed-size operations per coefficient lane, so reconstruction is linear in
the convolution width. -/
setup_benchmark runBatchVectorCrtWidth n => n
  with prep := prepBatchVectorWidth
  where {
    paramSchedule := .custom #[1, 4, 16, 64, 256, 1024, 2048, 4096]
    maxSecondsPerCall := 6.0
    targetInnerNanos := 200000000
    signalFloorMultiplier := 1.0
    outerTrials := 3
    tags := #["crt", "balanced", "vector", "warm-plan"]
  }

/- With width fixed, the vector accumulation has the same sum of linearly
growing accumulator sizes as scalar CRT, so its depth model is `O(k²)`. -/
setup_benchmark runVectorCrtDepth k => k * k
  with prep := prepVectorCrtDepth
  where {
    paramSchedule := .custom #[4, 8, 16, 32, 64, 128, 256, 512, 1024,
      2048, 4096, 8192]
    maxSecondsPerCall := 12.0
    targetInnerNanos := 200000000
    signalFloorMultiplier := 1.0
    verdictWarmupFraction := 0.8
    slopeTolerance := 0.25
    outerTrials := 3
  }

/- Fibonacci inputs make the truncated Euclidean recurrence take linearly
many divisions on numbers of up to `b` bits. Under the SPEC's schoolbook
word model this is `O(b²)`. -/
setup_benchmark runEuclid b => b * b
  with prep := prepReconLate
  where {
    paramSchedule := .custom #[64, 128, 256, 512, 1024, 2048, 4096, 8192,
      16384, 32768, 65536, 100000, 131072, 196608, 262144]
    maxSecondsPerCall := 12.0
    targetInnerNanos := 200000000
    signalFloorMultiplier := 1.0
    verdictWarmupFraction := 0.65
    slopeTolerance := 0.25
    outerTrials := 3
  }

/- `ratRecon?` is the same truncated Euclidean run followed by bounded-size
normalization and checks, retaining the `O(b²)` textbook model. -/
setup_benchmark runRatReconLate b => b * b
  with prep := prepReconLate
  where {
    paramSchedule := .custom #[64, 128, 256, 512, 1024, 2048, 4096, 8192,
      16384, 32768, 65536, 100000, 131072, 196608, 262144]
    maxSecondsPerCall := 12.0
    targetInnerNanos := 200000000
    signalFloorMultiplier := 1.0
    verdictWarmupFraction := 0.65
    slopeTolerance := 0.25
    outerTrials := 3
  }

/- Failure performs the complete Euclidean run and the final checks, so the
same `O(b²)` model applies. -/
setup_benchmark runRatReconFailure b => b * b
  with prep := prepReconFailure
  where {
    paramSchedule := .custom #[64, 128, 256, 512, 1024, 2048, 4096, 8192,
      16384, 32768, 65536, 100000, 131072, 196608, 262144]
    maxSecondsPerCall := 12.0
    targetInnerNanos := 200000000
    signalFloorMultiplier := 1.0
    verdictWarmupFraction := 0.65
    slopeTolerance := 0.25
    outerTrials := 3
  }

/- On this early-success family the wide wrapper is dominated by the integer
square root. The `b * sqrt b` complexity model is the benchmark's Karatsuba-range
surrogate for the GMP multiplication cost in Newton division. -/
setup_benchmark runRatReconWide b => b * Nat.sqrt b
  with prep := prepReconEarly
  where {
    paramSchedule := .custom #[64, 128, 256, 512, 1024, 2048, 4096, 8192,
      16384, 32768, 65536, 100000, 131072, 196608, 262144]
    maxSecondsPerCall := 12.0
    targetInnerNanos := 200000000
    signalFloorMultiplier := 1.0
    verdictWarmupFraction := 0.5
    slopeTolerance := 0.25
    outerTrials := 3
  }

/- The maximal-quotient heuristic traverses the same Euclidean remainder
chain and retains the same `O(b²)` textbook upper bound. -/
setup_benchmark runRatReconMaxQuot b => b * b
  with prep := prepReconLate
  where {
    paramSchedule := .custom #[64, 128, 256, 512, 1024, 2048, 4096, 8192,
      16384, 32768, 65536, 100000, 131072, 196608, 262144]
    maxSecondsPerCall := 12.0
    targetInnerNanos := 200000000
    signalFloorMultiplier := 1.0
    verdictWarmupFraction := 0.65
    slopeTolerance := 0.25
    outerTrials := 3
  }

/- The constructed witness is exactly twice the modulus. Checking it uses a
same-size division with a bounded quotient and scans `O(b)` input bits. -/
setup_benchmark runRatReconCheck b => b
  with prep := prepReconCheck
  where {
    paramSchedule := .custom #[64, 128, 256, 512, 1024, 2048, 4096, 8192,
      16384, 32768, 65536]
    maxSecondsPerCall := 4.0
    targetInnerNanos := 200000000
    signalFloorMultiplier := 1.0
    verdictWarmupFraction := 0.65
    slopeTolerance := 0.25
    outerTrials := 3
  }

/- With the 256-bit modulus fixed, the common-denominator fast path performs
constant-size modular arithmetic once per coordinate, hence `O(n)`. -/
setup_benchmark runRatReconVec n => n
  with prep := prepReconVec
  where {
    paramSchedule := .custom #[1, 4, 16, 64, 256, 1024, 2048, 4096]
    maxSecondsPerCall := 6.0
    targetInnerNanos := 200000000
    signalFloorMultiplier := 1.0
    verdictWarmupFraction := 0.6
    slopeTolerance := 0.25
    outerTrials := 3
  }

/- `crtLoop` performs one fixed-width vector push per accepted modulus. The
accumulated modulus grows linearly, and summing those costs gives `O(k²)`. -/
setup_benchmark runCrtLoop k => k * k
  with prep := prepLoop
  where {
    paramSchedule := .custom #[4, 8, 16, 32, 64, 128, 256, 512, 1024,
      2048, 4096, 8192]
    maxSecondsPerCall := 12.0
    targetInnerNanos := 200000000
    signalFloorMultiplier := 1.0
    verdictWarmupFraction := 0.8
    slopeTolerance := 0.25
    outerTrials := 3
  }

end Hex.ModularBench

def main (args : List String) : IO UInt32 :=
  LeanBench.Cli.dispatch args
