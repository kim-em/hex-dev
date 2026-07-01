/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexLLLBench.Inputs
import all HexLLLBench.Inputs

public section

namespace Hex.LLLBench
def runFirstShortVectorRandomBoundedNormSq60 : Unit → IO Int := fun _ => do
  return runFirstShortVectorNormSq
    (← getCachedInput randomBoundedInput60Ref (fun _ => prepRandomBoundedInput 60))

def runIsabelleRandomBoundedNormSq60 : Unit → IO Int := fun _ => do
  runIsabelleShortVectorNormSq "random-bounded-60"
    (← getCachedInput randomBoundedInput60Ref (fun _ => prepRandomBoundedInput 60))

def runFirstShortVectorRandomBoundedNormSq75 : Unit → IO Int := fun _ => do
  return runFirstShortVectorNormSq
    (← getCachedInput randomBoundedInput75Ref (fun _ => prepRandomBoundedInput 75))

def runIsabelleRandomBoundedNormSq75 : Unit → IO Int := fun _ => do
  runIsabelleShortVectorNormSq "random-bounded-75"
    (← getCachedInput randomBoundedInput75Ref (fun _ => prepRandomBoundedInput 75))

def runFirstShortVectorRandomBoundedNormSq90 : Unit → IO Int := fun _ => do
  return runFirstShortVectorNormSq
    (← getCachedInput randomBoundedInput90Ref (fun _ => prepRandomBoundedInput 90))

def runIsabelleRandomBoundedNormSq90 : Unit → IO Int := fun _ => do
  runIsabelleShortVectorNormSq "random-bounded-90"
    (← getCachedInput randomBoundedInput90Ref (fun _ => prepRandomBoundedInput 90))

def runFirstShortVectorRandomBoundedNormSq120 : Unit → IO Int := fun _ => do
  return runFirstShortVectorNormSq
    (← getCachedInput randomBoundedInput120Ref (fun _ => prepRandomBoundedInput 120))

def runIsabelleRandomBoundedNormSq120 : Unit → IO Int := fun _ => do
  runIsabelleShortVectorNormSq "random-bounded-120"
    (← getCachedInput randomBoundedInput120Ref (fun _ => prepRandomBoundedInput 120))

def runFirstShortVectorRandomBoundedNormSq150 : Unit → IO Int := fun _ => do
  return runFirstShortVectorNormSq
    (← getCachedInput randomBoundedInput150Ref (fun _ => prepRandomBoundedInput 150))

def runIsabelleRandomBoundedNormSq150 : Unit → IO Int := fun _ => do
  runIsabelleShortVectorNormSq "random-bounded-150"
    (← getCachedInput randomBoundedInput150Ref (fun _ => prepRandomBoundedInput 150))

def runFirstShortVectorRandomBoundedNormSq180 : Unit → IO Int := fun _ => do
  return runFirstShortVectorNormSq
    (← getCachedInput randomBoundedInput180Ref (fun _ => prepRandomBoundedInput 180))

def runIsabelleRandomBoundedNormSq180 : Unit → IO Int := fun _ => do
  runIsabelleShortVectorNormSq "random-bounded-180"
    (← getCachedInput randomBoundedInput180Ref (fun _ => prepRandomBoundedInput 180))

def runFirstShortVectorHarshCubicNormSq15 : Unit → IO Int := fun _ => do
  return runFirstShortVectorNormSq
    (← getCachedInput harshCubicInput15Ref (fun _ => prepHarshCubicInput 15))

def runIsabelleHarshCubicNormSq15 : Unit → IO Int := fun _ => do
  runIsabelleShortVectorNormSq "harsh-cubic-15"
    (← getCachedInput harshCubicInput15Ref (fun _ => prepHarshCubicInput 15))

def runFirstShortVectorHarshCubicNormSq20 : Unit → IO Int := fun _ => do
  return runFirstShortVectorNormSq
    (← getCachedInput harshCubicInput20Ref (fun _ => prepHarshCubicInput 20))

def runIsabelleHarshCubicNormSq20 : Unit → IO Int := fun _ => do
  runIsabelleShortVectorNormSq "harsh-cubic-20"
    (← getCachedInput harshCubicInput20Ref (fun _ => prepHarshCubicInput 20))

def runFirstShortVectorHarshCubicNormSq25 : Unit → IO Int := fun _ => do
  return runFirstShortVectorNormSq
    (← getCachedInput harshCubicInput25Ref (fun _ => prepHarshCubicInput 25))

def runIsabelleHarshCubicNormSq25 : Unit → IO Int := fun _ => do
  runIsabelleShortVectorNormSq "harsh-cubic-25"
    (← getCachedInput harshCubicInput25Ref (fun _ => prepHarshCubicInput 25))

def runFirstShortVectorHarshCubicNormSq30 : Unit → IO Int := fun _ => do
  return runFirstShortVectorNormSq
    (← getCachedInput harshCubicInput30Ref (fun _ => prepHarshCubicInput 30))

def runIsabelleHarshCubicNormSq30 : Unit → IO Int := fun _ => do
  runIsabelleShortVectorNormSq "harsh-cubic-30"
    (← getCachedInput harshCubicInput30Ref (fun _ => prepHarshCubicInput 30))

def runFirstShortVectorHarshCubicNormSq35 : Unit → IO Int := fun _ => do
  return runFirstShortVectorNormSq
    (← getCachedInput harshCubicInput35Ref (fun _ => prepHarshCubicInput 35))

def runIsabelleHarshCubicNormSq35 : Unit → IO Int := fun _ => do
  runIsabelleShortVectorNormSq "harsh-cubic-35"
    (← getCachedInput harshCubicInput35Ref (fun _ => prepHarshCubicInput 35))

def runFirstShortVectorHarshCubicNormSq40 : Unit → IO Int := fun _ => do
  return runFirstShortVectorNormSq
    (← getCachedInput harshCubicInput40Ref (fun _ => prepHarshCubicInput 40))

def runIsabelleHarshCubicNormSq40 : Unit → IO Int := fun _ => do
  runIsabelleShortVectorNormSq "harsh-cubic-40"
    (← getCachedInput harshCubicInput40Ref (fun _ => prepHarshCubicInput 40))

def runFirstShortVectorHarshCubicNormSq45 : Unit → IO Int := fun _ => do
  return runFirstShortVectorNormSq
    (← getCachedInput harshCubicInput45Ref (fun _ => prepHarshCubicInput 45))

def runIsabelleHarshCubicNormSq45 : Unit → IO Int := fun _ => do
  runIsabelleShortVectorNormSq "harsh-cubic-45"
    (← getCachedInput harshCubicInput45Ref (fun _ => prepHarshCubicInput 45))

def runFirstShortVectorHarshCubicNormSq50 : Unit → IO Int := fun _ => do
  return runFirstShortVectorNormSq
    (← getCachedInput harshCubicInput50Ref (fun _ => prepHarshCubicInput 50))

def runIsabelleHarshCubicNormSq50 : Unit → IO Int := fun _ => do
  runIsabelleShortVectorNormSq "harsh-cubic-50"
    (← getCachedInput harshCubicInput50Ref (fun _ => prepHarshCubicInput 50))

def runFirstShortVectorHarshCubicNormSq55 : Unit → IO Int := fun _ => do
  return runFirstShortVectorNormSq
    (← getCachedInput harshCubicInput55Ref (fun _ => prepHarshCubicInput 55))

def runIsabelleHarshCubicNormSq55 : Unit → IO Int := fun _ => do
  runIsabelleShortVectorNormSq "harsh-cubic-55"
    (← getCachedInput harshCubicInput55Ref (fun _ => prepHarshCubicInput 55))

def runFirstShortVectorHarshCubicNormSq60 : Unit → IO Int := fun _ => do
  return runFirstShortVectorNormSq
    (← getCachedInput harshCubicInput60Ref (fun _ => prepHarshCubicInput 60))

def runIsabelleHarshCubicNormSq60 : Unit → IO Int := fun _ => do
  runIsabelleShortVectorNormSq "harsh-cubic-60"
    (← getCachedInput harshCubicInput60Ref (fun _ => prepHarshCubicInput 60))

def runFirstShortVectorHarshCubicNormSq65 : Unit → IO Int := fun _ => do
  return runFirstShortVectorNormSq
    (← getCachedInput harshCubicInput65Ref (fun _ => prepHarshCubicInput 65))

def runIsabelleHarshCubicNormSq65 : Unit → IO Int := fun _ => do
  runIsabelleShortVectorNormSq "harsh-cubic-65"
    (← getCachedInput harshCubicInput65Ref (fun _ => prepHarshCubicInput 65))

/-- Isabelle-certified per-request process floor: time a trivial 2×2 request
through `svp_certified`. The median is the fixed fork+startup overhead the
comparator plot subtracts from the Isabelle-certified curve, so the
adjustment uses a committed measurement rather than a hardcoded constant. -/
def runIsabelleCertifiedProcessFloorNormSq : Unit → IO Int := fun _ => do
  runIsabelleCertifiedShortVectorNormSq "process-floor" processFloorInput

def runIsabelleCertifiedRandomBoundedNormSq30 : Unit → IO Int := fun _ => do
  runIsabelleCertifiedShortVectorNormSq "random-bounded-30"
    (← getCachedInput randomBoundedInput30Ref (fun _ => prepRandomBoundedInput 30))

def runIsabelleCertifiedRandomBoundedNormSq45 : Unit → IO Int := fun _ => do
  runIsabelleCertifiedShortVectorNormSq "random-bounded-45"
    (← getCachedInput randomBoundedInput45Ref (fun _ => prepRandomBoundedInput 45))

def runIsabelleCertifiedRandomBoundedNormSq60 : Unit → IO Int := fun _ => do
  runIsabelleCertifiedShortVectorNormSq "random-bounded-60"
    (← getCachedInput randomBoundedInput60Ref (fun _ => prepRandomBoundedInput 60))

def runIsabelleCertifiedRandomBoundedNormSq75 : Unit → IO Int := fun _ => do
  runIsabelleCertifiedShortVectorNormSq "random-bounded-75"
    (← getCachedInput randomBoundedInput75Ref (fun _ => prepRandomBoundedInput 75))

def runIsabelleCertifiedRandomBoundedNormSq90 : Unit → IO Int := fun _ => do
  runIsabelleCertifiedShortVectorNormSq "random-bounded-90"
    (← getCachedInput randomBoundedInput90Ref (fun _ => prepRandomBoundedInput 90))

def runIsabelleCertifiedRandomBoundedNormSq120 : Unit → IO Int := fun _ => do
  runIsabelleCertifiedShortVectorNormSq "random-bounded-120"
    (← getCachedInput randomBoundedInput120Ref (fun _ => prepRandomBoundedInput 120))

def runIsabelleCertifiedRandomBoundedNormSq150 : Unit → IO Int := fun _ => do
  runIsabelleCertifiedShortVectorNormSq "random-bounded-150"
    (← getCachedInput randomBoundedInput150Ref (fun _ => prepRandomBoundedInput 150))

def runIsabelleCertifiedRandomBoundedNormSq180 : Unit → IO Int := fun _ => do
  runIsabelleCertifiedShortVectorNormSq "random-bounded-180"
    (← getCachedInput randomBoundedInput180Ref (fun _ => prepRandomBoundedInput 180))

def runIsabelleCertifiedHarshCubicNormSq15 : Unit → IO Int := fun _ => do
  runIsabelleCertifiedShortVectorNormSq "harsh-cubic-15"
    (← getCachedInput harshCubicInput15Ref (fun _ => prepHarshCubicInput 15))

def runIsabelleCertifiedHarshCubicNormSq20 : Unit → IO Int := fun _ => do
  runIsabelleCertifiedShortVectorNormSq "harsh-cubic-20"
    (← getCachedInput harshCubicInput20Ref (fun _ => prepHarshCubicInput 20))

def runIsabelleCertifiedHarshCubicNormSq25 : Unit → IO Int := fun _ => do
  runIsabelleCertifiedShortVectorNormSq "harsh-cubic-25"
    (← getCachedInput harshCubicInput25Ref (fun _ => prepHarshCubicInput 25))

def runIsabelleCertifiedHarshCubicNormSq30 : Unit → IO Int := fun _ => do
  runIsabelleCertifiedShortVectorNormSq "harsh-cubic-30"
    (← getCachedInput harshCubicInput30Ref (fun _ => prepHarshCubicInput 30))

def runIsabelleCertifiedHarshCubicNormSq35 : Unit → IO Int := fun _ => do
  runIsabelleCertifiedShortVectorNormSq "harsh-cubic-35"
    (← getCachedInput harshCubicInput35Ref (fun _ => prepHarshCubicInput 35))

def runIsabelleCertifiedHarshCubicNormSq40 : Unit → IO Int := fun _ => do
  runIsabelleCertifiedShortVectorNormSq "harsh-cubic-40"
    (← getCachedInput harshCubicInput40Ref (fun _ => prepHarshCubicInput 40))

def runIsabelleCertifiedHarshCubicNormSq45 : Unit → IO Int := fun _ => do
  runIsabelleCertifiedShortVectorNormSq "harsh-cubic-45"
    (← getCachedInput harshCubicInput45Ref (fun _ => prepHarshCubicInput 45))

def runIsabelleCertifiedHarshCubicNormSq50 : Unit → IO Int := fun _ => do
  runIsabelleCertifiedShortVectorNormSq "harsh-cubic-50"
    (← getCachedInput harshCubicInput50Ref (fun _ => prepHarshCubicInput 50))

def runIsabelleCertifiedHarshCubicNormSq55 : Unit → IO Int := fun _ => do
  runIsabelleCertifiedShortVectorNormSq "harsh-cubic-55"
    (← getCachedInput harshCubicInput55Ref (fun _ => prepHarshCubicInput 55))

def runIsabelleCertifiedHarshCubicNormSq60 : Unit → IO Int := fun _ => do
  runIsabelleCertifiedShortVectorNormSq "harsh-cubic-60"
    (← getCachedInput harshCubicInput60Ref (fun _ => prepHarshCubicInput 60))

def runIsabelleCertifiedHarshCubicNormSq65 : Unit → IO Int := fun _ => do
  runIsabelleCertifiedShortVectorNormSq "harsh-cubic-65"
    (← getCachedInput harshCubicInput65Ref (fun _ => prepHarshCubicInput 65))

/-- Parametric benchmark target: LCG random-bounded bases. -/
def runFirstShortVectorRandomBoundedChecksum (input : FirstShortVectorInput) : Int :=
  runFirstShortVectorChecksum input

/-- Parametric benchmark target: harsh-cubic bases. -/
def runFirstShortVectorHarshCubicChecksum (input : FirstShortVectorInput) : Int :=
  runFirstShortVectorChecksum input

def firstShortVectorRandomBoundedNormSqHash (n : Nat) : UInt64 :=
  Hashable.hash (runFirstShortVectorNormSq (prepRandomBoundedInput n))

def firstShortVectorHarshCubicNormSqHash (n : Nat) : UInt64 :=
  Hashable.hash (runFirstShortVectorNormSq (prepHarshCubicInput n))

/- Complexity derivation: `LLLState.ofBasis` builds the Gram matrix for a
square BZ recombination-style basis with `rows = cols = n + 3`, then runs the
shared fraction-free Bareiss-shaped pass used by `GramSchmidt.Int.data`.
The dominant work is `rows^2 * cols`
integer multiply-adds for Gram construction plus one cubic elimination over
the `rows x rows` Gram matrix. Hadamard bounds each leading Gram determinant's
bit-width by `O(k * (log rows + log cols + 2 log B))`; this bounded-coefficient
fixture keeps the bit-width factor uniform in the declared operation count. -/
setup_benchmark runOfBasisBzRecombinationChecksum n =>
    ofBasisBzRecombinationComplexity n
  with prep := prepOfBasisBzRecombinationInput
  where {
    paramFloor := 24
    paramCeiling := 72
    paramSchedule := .custom #[24, 36, 48, 60, 72]
    maxSecondsPerCall := 8.0
    signalFloorMultiplier := 1.0
  }

/- Complexity derivation: the random-bounded family uses a square
`rows = cols = n + 3` basis with entries in `[-30, 30]`. `ofBasis` first forms
all `rows^2` dot products of length `rows`, then computes `d` and `ν` in one
Bareiss-style pass over that Gram matrix. Hadamard
gives `O(k * (log rows + log 30))` pivot bit-width, so the registration
declares the cubic algebraic surface rather than the host-specific bigint
constant. -/
setup_benchmark runOfBasisRandomBoundedChecksum n =>
    ofBasisRandomBoundedComplexity n
  with prep := prepOfBasisRandomBoundedInput
  where {
    paramFloor := 48
    paramCeiling := 144
    paramSchedule := .custom #[48, 72, 96, 120, 144]
    maxSecondsPerCall := 12.0
    signalFloorMultiplier := 1.0
  }

/- Complexity derivation: the harsh-cubic family uses the same square
`rows = cols = n + 3` constructor path as random-bounded, but fixture entries
have bit-length `3 * rows + O(1)`. The same Hadamard bound makes Bareiss pivot
bit-width grow linearly with `rows` on top of the Gram construction and the two
cubic elimination passes, so the declared model multiplies the algebraic
`ofBasisComplexity rows rows` surface by `rows`. -/
setup_benchmark runOfBasisHarshCubicChecksum n =>
    ofBasisHarshCubicComplexity n
  with prep := prepOfBasisHarshCubicInput
  where {
    paramFloor := 12
    paramCeiling := 36
    paramSchedule := .custom #[12, 18, 24, 30, 36]
    maxSecondsPerCall := 30.0
    targetInnerNanos := 1_000_000_000
    signalFloorMultiplier := 1.0
  }

/- Complexity derivation: `prepStateInput n` gives `rows = n + 3` and
`cols = 2 * (n + 3) + 1`. A single targeted reduction updates one basis row
over `cols` entries and one coefficient prefix bounded by `rows`. -/
setup_benchmark runSizeReduceColumnChecksum n => sizeReduceColumnComplexity n
  with prep := prepStateInput
  where {
    paramFloor := 96
    paramCeiling := 160
    paramSchedule := .custom #[96, 128, 160]
    maxSecondsPerCall := 3.0
    signalFloorMultiplier := 1.0
  }

/- Complexity derivation: full size reduction of the final prepared row
performs one targeted row update for each earlier row, so the model is
`rows * cols` for basis entries plus the triangular coefficient-prefix surface,
bounded here by `rows^2`. -/
setup_benchmark runSizeReduceChecksum n => sizeReduceComplexity n
  with prep := prepStateInput
  where {
    paramFloor := 128
    paramCeiling := 160
    paramSchedule := .custom #[128, 144, 160]
    maxSecondsPerCall := 30.0
    signalFloorMultiplier := 1.0
  }

/- Complexity derivation: an adjacent swap exchanges two basis rows over
`cols` entries, rewrites one determinant, swaps the lower coefficient prefix,
and updates the two affected coefficient columns for rows above the pivot; all
terms are linear in rows. -/
setup_benchmark runSwapStepChecksum n => swapStepComplexity n
  with prep := prepStateInput
  where {
    paramFloor := 96
    paramCeiling := 160
    paramSchedule := .custom #[96, 128, 160]
    maxSecondsPerCall := 3.0
    signalFloorMultiplier := 1.0
  }

/- Complexity derivation: `gramSchmidtCoeff` reads one stored `ν[k][j]` entry
and one stored `d[j+1]` denominator, then performs a single rational division
whose denominator bit-width grows linearly with the prepared row parameter.
The elevated cap covers state preparation at the smallest scientific rung on
high-spawn-floor hosts; it is not part of the measured body. -/
setup_benchmark runGramSchmidtCoeffChecksum n => gramSchmidtCoeffComplexity n
  with prep := prepStateInput
  where {
    paramFloor := 32
    paramCeiling := 128
    paramSchedule := .custom #[32, 64, 96, 128]
    maxSecondsPerCall := 30.0
    targetInnerNanos := 2_000_000_000
    signalFloorMultiplier := 1.0
  }

/- Complexity derivation: `potential` folds once over the prepared state's
determinant prefix. The fixture has `rows = n + 3`, so the prefix length is
`n + 2`; each stored Gram determinant has row-dependent bit width, and the
running product's bit width grows across the prefix. The resulting executable
integer-arithmetic surface is cubic in `rows`. -/
setup_benchmark runPotential n => potentialComplexity n
  with prep := prepStateInput
  where {
    paramFloor := 192
    paramCeiling := 216
    paramSchedule := .custom #[192, 208, 216]
    maxSecondsPerCall := 8.0
    targetInnerNanos := 1_000_000_000
    signalFloorMultiplier := 1.0
  }

/- Fixed Phase-4 family: BZ-shaped triangular basis with three lifted local
factors, matching the conformance fixture in `HexLLL/EmitFixtures.lean`. This
fixed target records the downstream hot path inherited from
Berlekamp-Zassenhaus recombination. -/
setup_fixed_benchmark runFirstShortVectorBZRecombinationChecksum where {
    repeats := 5
    maxSecondsPerCall := 6.0
    expectedHash := some (Hashable.hash (runFirstShortVectorChecksum bzRecombinationInput))
  }

/- Fixed bottom-rung Lean/fpLLL comparison for the BZ recombination family.
The fpLLL target is informational and FFI-call based via fplll-ffi; scheduled
and release bench runs use
`compare runFirstShortVectorBZRecombinationChecksum runFpLLLFirstShortVectorBZRecombinationChecksum`
to record its ratio. -/
setup_fixed_benchmark runFpLLLFirstShortVectorBZRecombinationChecksum where {
    repeats := 5
    minTotalSeconds := 1.0
    maxSecondsPerCall := 20.0
    expectedHash := some 0x20001
    warmupFirstIter := true
  }

/- Fixed Lean/fpLLL comparison for the random-bounded family across the
post-HO-18 densified ladder. -/
setup_fixed_benchmark runFirstShortVectorRandomBounded30Checksum where {
    repeats := 5
    maxSecondsPerCall := 20.0
    expectedHash := some (Hashable.hash (runFirstShortVectorChecksum (prepRandomBoundedInput 30)))
  }

setup_fixed_benchmark runFpLLLFirstShortVectorRandomBounded30Checksum where {
    repeats := 5
    minTotalSeconds := 1.0
    maxSecondsPerCall := 20.0
    expectedHash := some 0x4
    warmupFirstIter := true
  }

setup_fixed_benchmark runFpLLLFirstShortVectorRandomBounded45Checksum where {
    repeats := 5
    minTotalSeconds := 1.0
    maxSecondsPerCall := 20.0
    warmupFirstIter := true
  }

setup_fixed_benchmark runFpLLLFirstShortVectorRandomBounded60Checksum where {
    repeats := 5
    minTotalSeconds := 1.0
    maxSecondsPerCall := 30.0
    warmupFirstIter := true
  }

setup_fixed_benchmark runFpLLLFirstShortVectorRandomBounded75Checksum where {
    repeats := 5
    minTotalSeconds := 1.0
    maxSecondsPerCall := 30.0
    warmupFirstIter := true
  }

setup_fixed_benchmark runFpLLLFirstShortVectorRandomBounded90Checksum where {
    repeats := 5
    minTotalSeconds := 1.0
    maxSecondsPerCall := 40.0
    warmupFirstIter := true
  }

setup_fixed_benchmark runFpLLLFirstShortVectorRandomBounded120Checksum where {
    repeats := 5
    minTotalSeconds := 1.0
    maxSecondsPerCall := 60.0
    warmupFirstIter := true
  }

setup_fixed_benchmark runFpLLLFirstShortVectorRandomBounded150Checksum where {
    repeats := 5
    minTotalSeconds := 1.0
    maxSecondsPerCall := 90.0
    warmupFirstIter := true
  }

setup_fixed_benchmark runFpLLLFirstShortVectorRandomBounded180Checksum where {
    repeats := 5
    minTotalSeconds := 1.0
    maxSecondsPerCall := 120.0
    warmupFirstIter := true
  }

/- Certified-path fixed registrations for the random-bounded ladder. The
`runCertifiedFirstShortVector*` targets measure fpLLL candidate production plus
`certCheck`; the paired `runCertifiedChecker*` targets cache one fpLLL payload
and re-run only Lean's checker after warmup. -/
setup_fixed_benchmark runDispatchedFirstShortVectorRandomBounded30Checksum where {
    repeats := 3
    maxSecondsPerCall := 20.0
    expectedHash := some (Hashable.hash (runFirstShortVectorChecksum (prepRandomBoundedInput 30)))
  }

setup_fixed_benchmark runCertifiedFirstShortVectorRandomBounded30Checksum where {
    repeats := 3
    minTotalSeconds := 1.0
    maxSecondsPerCall := 20.0
    warmupFirstIter := true
  }

setup_fixed_benchmark runCertifiedCheckerRandomBounded30Checksum where {
    repeats := 3
    maxSecondsPerCall := 20.0
    warmupFirstIter := true
  }

setup_fixed_benchmark runCertifiedFirstShortVectorRandomBounded45Checksum where {
    repeats := 3
    minTotalSeconds := 1.0
    maxSecondsPerCall := 30.0
    warmupFirstIter := true
  }

setup_fixed_benchmark runCertifiedCheckerRandomBounded45Checksum where {
    repeats := 3
    maxSecondsPerCall := 20.0
    warmupFirstIter := true
  }

setup_fixed_benchmark runCertifiedFirstShortVectorRandomBounded60Checksum where {
    repeats := 3
    minTotalSeconds := 1.0
    maxSecondsPerCall := 40.0
    warmupFirstIter := true
  }

setup_fixed_benchmark runCertifiedCheckerRandomBounded60Checksum where {
    repeats := 3
    maxSecondsPerCall := 30.0
    warmupFirstIter := true
  }

setup_fixed_benchmark runCertifiedFirstShortVectorRandomBounded75Checksum where {
    repeats := 3
    minTotalSeconds := 1.0
    maxSecondsPerCall := 50.0
    warmupFirstIter := true
  }

setup_fixed_benchmark runCertifiedCheckerRandomBounded75Checksum where {
    repeats := 3
    maxSecondsPerCall := 40.0
    warmupFirstIter := true
  }

setup_fixed_benchmark runCertifiedFirstShortVectorRandomBounded90Checksum where {
    repeats := 3
    minTotalSeconds := 1.0
    maxSecondsPerCall := 60.0
    warmupFirstIter := true
  }

setup_fixed_benchmark runCertifiedCheckerRandomBounded90Checksum where {
    repeats := 3
    maxSecondsPerCall := 50.0
    warmupFirstIter := true
  }

setup_fixed_benchmark runCertifiedFirstShortVectorRandomBounded120Checksum where {
    repeats := 3
    minTotalSeconds := 1.0
    maxSecondsPerCall := 90.0
    warmupFirstIter := true
  }

setup_fixed_benchmark runCertifiedCheckerRandomBounded120Checksum where {
    repeats := 3
    maxSecondsPerCall := 80.0
    warmupFirstIter := true
  }

setup_fixed_benchmark runCertifiedFirstShortVectorRandomBounded150Checksum where {
    repeats := 3
    minTotalSeconds := 1.0
    maxSecondsPerCall := 120.0
    warmupFirstIter := true
  }

setup_fixed_benchmark runCertifiedCheckerRandomBounded150Checksum where {
    repeats := 3
    maxSecondsPerCall := 120.0
    warmupFirstIter := true
  }

setup_fixed_benchmark runCertifiedFirstShortVectorRandomBounded180Checksum where {
    repeats := 3
    minTotalSeconds := 1.0
    maxSecondsPerCall := 180.0
    warmupFirstIter := true
  }

setup_fixed_benchmark runCertifiedCheckerRandomBounded180Checksum where {
    repeats := 3
    maxSecondsPerCall := 180.0
    warmupFirstIter := true
  }

/- Fixed bottom-rung Lean/fpLLL comparison for the harsh-cubic family at
`n = 15`, the first rung of the scientific parametric ladder. The fpLLL
comparison also follows the full harsh-cubic comparator ladder. -/
setup_fixed_benchmark runFirstShortVectorHarshCubic15Checksum where {
    repeats := 5
    maxSecondsPerCall := 20.0
    expectedHash := some (Hashable.hash (runFirstShortVectorChecksum (prepHarshCubicInput 15)))
  }

setup_fixed_benchmark runFpLLLFirstShortVectorHarshCubic15Checksum where {
    repeats := 5
    minTotalSeconds := 1.0
    maxSecondsPerCall := 20.0
    expectedHash := some 0x6ccfd453f897ff98
    warmupFirstIter := true
  }

setup_fixed_benchmark runFpLLLFirstShortVectorHarshCubic20Checksum where {
    repeats := 5
    minTotalSeconds := 1.0
    maxSecondsPerCall := 20.0
    warmupFirstIter := true
  }

setup_fixed_benchmark runFpLLLFirstShortVectorHarshCubic25Checksum where {
    repeats := 5
    minTotalSeconds := 1.0
    maxSecondsPerCall := 20.0
    warmupFirstIter := true
  }

setup_fixed_benchmark runFpLLLFirstShortVectorHarshCubic30Checksum where {
    repeats := 5
    minTotalSeconds := 1.0
    maxSecondsPerCall := 20.0
    warmupFirstIter := true
  }

setup_fixed_benchmark runFpLLLFirstShortVectorHarshCubic35Checksum where {
    repeats := 5
    minTotalSeconds := 1.0
    maxSecondsPerCall := 20.0
    warmupFirstIter := true
  }

setup_fixed_benchmark runFpLLLFirstShortVectorHarshCubic40Checksum where {
    repeats := 5
    minTotalSeconds := 1.0
    maxSecondsPerCall := 20.0
    warmupFirstIter := true
  }

setup_fixed_benchmark runFpLLLFirstShortVectorHarshCubic45Checksum where {
    repeats := 5
    minTotalSeconds := 1.0
    maxSecondsPerCall := 20.0
    warmupFirstIter := true
  }

setup_fixed_benchmark runFpLLLFirstShortVectorHarshCubic50Checksum where {
    repeats := 5
    minTotalSeconds := 1.0
    maxSecondsPerCall := 20.0
    warmupFirstIter := true
  }

setup_fixed_benchmark runFpLLLFirstShortVectorHarshCubic55Checksum where {
    repeats := 5
    minTotalSeconds := 1.0
    maxSecondsPerCall := 20.0
    warmupFirstIter := true
  }

setup_fixed_benchmark runFpLLLFirstShortVectorHarshCubic60Checksum where {
    repeats := 5
    maxSecondsPerCall := 20.0
    warmupFirstIter := true
  }

setup_fixed_benchmark runFpLLLFirstShortVectorHarshCubic65Checksum where {
    repeats := 5
    maxSecondsPerCall := 20.0
    warmupFirstIter := true
  }

/- Certified-path fixed registrations for the harsh-cubic ladder. -/
setup_fixed_benchmark runDispatchedFirstShortVectorHarshCubic15Checksum where {
    repeats := 3
    maxSecondsPerCall := 20.0
    expectedHash := some (Hashable.hash (runFirstShortVectorChecksum (prepHarshCubicInput 15)))
  }

setup_fixed_benchmark runCertifiedFirstShortVectorHarshCubic15Checksum where {
    repeats := 3
    minTotalSeconds := 1.0
    maxSecondsPerCall := 20.0
    warmupFirstIter := true
  }

setup_fixed_benchmark runCertifiedCheckerHarshCubic15Checksum where {
    repeats := 3
    maxSecondsPerCall := 20.0
    warmupFirstIter := true
  }

setup_fixed_benchmark runCertifiedFirstShortVectorHarshCubic20Checksum where {
    repeats := 3
    minTotalSeconds := 1.0
    maxSecondsPerCall := 20.0
    warmupFirstIter := true
  }

setup_fixed_benchmark runCertifiedCheckerHarshCubic20Checksum where {
    repeats := 3
    maxSecondsPerCall := 20.0
    warmupFirstIter := true
  }

setup_fixed_benchmark runCertifiedFirstShortVectorHarshCubic25Checksum where {
    repeats := 3
    minTotalSeconds := 1.0
    maxSecondsPerCall := 20.0
    warmupFirstIter := true
  }

setup_fixed_benchmark runCertifiedCheckerHarshCubic25Checksum where {
    repeats := 3
    maxSecondsPerCall := 20.0
    warmupFirstIter := true
  }

setup_fixed_benchmark runCertifiedFirstShortVectorHarshCubic30Checksum where {
    repeats := 3
    minTotalSeconds := 1.0
    maxSecondsPerCall := 20.0
    warmupFirstIter := true
  }

setup_fixed_benchmark runCertifiedCheckerHarshCubic30Checksum where {
    repeats := 3
    maxSecondsPerCall := 20.0
    warmupFirstIter := true
  }

setup_fixed_benchmark runCertifiedFirstShortVectorHarshCubic35Checksum where {
    repeats := 3
    minTotalSeconds := 1.0
    maxSecondsPerCall := 20.0
    warmupFirstIter := true
  }

setup_fixed_benchmark runCertifiedCheckerHarshCubic35Checksum where {
    repeats := 3
    maxSecondsPerCall := 20.0
    warmupFirstIter := true
  }

setup_fixed_benchmark runCertifiedFirstShortVectorHarshCubic40Checksum where {
    repeats := 3
    minTotalSeconds := 1.0
    maxSecondsPerCall := 20.0
    warmupFirstIter := true
  }

setup_fixed_benchmark runCertifiedCheckerHarshCubic40Checksum where {
    repeats := 3
    maxSecondsPerCall := 20.0
    warmupFirstIter := true
  }

setup_fixed_benchmark runCertifiedFirstShortVectorHarshCubic45Checksum where {
    repeats := 3
    minTotalSeconds := 1.0
    maxSecondsPerCall := 20.0
    warmupFirstIter := true
  }

setup_fixed_benchmark runCertifiedCheckerHarshCubic45Checksum where {
    repeats := 3
    maxSecondsPerCall := 20.0
    warmupFirstIter := true
  }

setup_fixed_benchmark runCertifiedFirstShortVectorHarshCubic50Checksum where {
    repeats := 3
    minTotalSeconds := 1.0
    maxSecondsPerCall := 20.0
    warmupFirstIter := true
  }

setup_fixed_benchmark runCertifiedCheckerHarshCubic50Checksum where {
    repeats := 3
    maxSecondsPerCall := 20.0
    warmupFirstIter := true
  }

setup_fixed_benchmark runCertifiedFirstShortVectorHarshCubic55Checksum where {
    repeats := 3
    minTotalSeconds := 1.0
    maxSecondsPerCall := 20.0
    warmupFirstIter := true
  }

setup_fixed_benchmark runCertifiedCheckerHarshCubic55Checksum where {
    repeats := 3
    maxSecondsPerCall := 20.0
    warmupFirstIter := true
  }

setup_fixed_benchmark runCertifiedFirstShortVectorHarshCubic60Checksum where {
    repeats := 3
    minTotalSeconds := 1.0
    maxSecondsPerCall := 20.0
    warmupFirstIter := true
  }

setup_fixed_benchmark runCertifiedCheckerHarshCubic60Checksum where {
    repeats := 3
    maxSecondsPerCall := 20.0
    warmupFirstIter := true
  }

setup_fixed_benchmark runCertifiedFirstShortVectorHarshCubic65Checksum where {
    repeats := 3
    minTotalSeconds := 1.0
    maxSecondsPerCall := 20.0
    warmupFirstIter := true
  }

setup_fixed_benchmark runCertifiedCheckerHarshCubic65Checksum where {
    repeats := 3
    maxSecondsPerCall := 20.0
    warmupFirstIter := true
  }

/- One certified check per rung of both ladders; the observed value pins the
reducedness-decision tally to "9 rungs dispatched to the interval checker
(harsh-cubic n ≥ 30, random-bounded n ≥ 180), 10 to the exact checker by
the size predictor, zero indecision fallbacks". -/
setup_fixed_benchmark runCertifiedCheckerIntervalTally where {
    repeats := 1
    maxSecondsPerCall := 120.0
    expectedHash := some (Hashable.hash (((9 * 65537 + 10) * 65537 : Int)))
  }

/- Complexity derivation: random-bounded inputs have square dimension `n` and
entries generated by the committed LCG seed with `|entry| <= 30`. This
near-orthogonal fixture has few Lovasz swaps, so the public `firstShortVector`
entry point is dominated by `LLLState.ofBasis` plus triangular size reduction
rather than by the textbook worst-case swap count. The `Nat.log2 (n + 1)`
factor records the slow determinant/coefficient bit-width growth in the exact
integer state. -/
setup_benchmark runFirstShortVectorRandomBoundedChecksum n =>
    firstShortVectorRandomBoundedComplexity n
  with prep := prepRandomBoundedInput
  where {
    paramFloor := 30
    paramCeiling := 180
    paramSchedule := .custom #[30, 45, 60, 75, 90, 120, 150, 180]
    maxSecondsPerCall := 20.0
    targetInnerNanos := 1_000_000_000
    signalFloorMultiplier := 1.0
  }

/- Complexity derivation: harsh-cubic inputs have square dimension `n` and
entry bit-length approximately `3.3 * n`, following the verified-Isabelle
paper regime named in `phase4.input_families`. The committed fixture is still
near-orthogonal rather than worst-case LLL; it exercises the quartic row-
operation surface and repeated logarithmic coefficient-growth factors from the
exact-integer row operations, while the separate
`runOfBasisHarshCubicChecksum` target keeps the initial Gram-Schmidt
construction attributable. -/
setup_benchmark runFirstShortVectorHarshCubicChecksum n =>
    firstShortVectorHarshCubicComplexity n
  with prep := prepHarshCubicInput
  where {
    paramFloor := 15
    paramCeiling := 55
    paramSchedule := .custom #[15, 20, 25, 30, 35, 40, 45, 50, 55]
    maxSecondsPerCall := 20.0
    targetInnerNanos := 1_000_000_000
    signalFloorMultiplier := 1.0
  }

/- Fixed external-comparator registrations. The paired Lean and Isabelle
targets return the squared norm of the first LLL vector so `compare` can join
on a semantic scalar, not an implementation-specific reduced-basis encoding. -/
setup_fixed_benchmark runFirstShortVectorBZRecombinationNormSq where {
    repeats := 3
    maxSecondsPerCall := 60.0
    expectedHash := some (Hashable.hash (runFirstShortVectorNormSq bzRecombinationInput))
  }

setup_fixed_benchmark runIsabelleBZRecombinationNormSq where {
    repeats := 3
    minTotalSeconds := 1.0
    maxSecondsPerCall := 60.0
    expectedHash := some (Hashable.hash (runFirstShortVectorNormSq bzRecombinationInput))
    warmupFirstIter := true
  }

setup_fixed_benchmark runFirstShortVectorRandomBoundedNormSq30 where {
    repeats := 3
    maxSecondsPerCall := 20.0
    expectedHash := some (firstShortVectorRandomBoundedNormSqHash 30)
  }

setup_fixed_benchmark runIsabelleRandomBoundedNormSq30 where {
    repeats := 3
    minTotalSeconds := 1.0
    maxSecondsPerCall := 20.0
    expectedHash := some (firstShortVectorRandomBoundedNormSqHash 30)
    warmupFirstIter := true
  }

setup_fixed_benchmark runFirstShortVectorRandomBoundedNormSq45 where {
    repeats := 3
    maxSecondsPerCall := 20.0
    expectedHash := some (firstShortVectorRandomBoundedNormSqHash 45)
  }

setup_fixed_benchmark runIsabelleRandomBoundedNormSq45 where {
    repeats := 3
    minTotalSeconds := 1.0
    maxSecondsPerCall := 20.0
    expectedHash := some (firstShortVectorRandomBoundedNormSqHash 45)
    warmupFirstIter := true
  }

setup_fixed_benchmark runFirstShortVectorRandomBoundedNormSq60 where {
    repeats := 3
    maxSecondsPerCall := 30.0
    expectedHash := some (firstShortVectorRandomBoundedNormSqHash 60)
  }

setup_fixed_benchmark runIsabelleRandomBoundedNormSq60 where {
    repeats := 3
    minTotalSeconds := 1.0
    maxSecondsPerCall := 30.0
    expectedHash := some (firstShortVectorRandomBoundedNormSqHash 60)
    warmupFirstIter := true
  }

setup_fixed_benchmark runFirstShortVectorRandomBoundedNormSq75 where {
    repeats := 3
    maxSecondsPerCall := 30.0
    expectedHash := some (firstShortVectorRandomBoundedNormSqHash 75)
  }

setup_fixed_benchmark runIsabelleRandomBoundedNormSq75 where {
    repeats := 3
    minTotalSeconds := 1.0
    maxSecondsPerCall := 30.0
    expectedHash := some (firstShortVectorRandomBoundedNormSqHash 75)
    warmupFirstIter := true
  }

setup_fixed_benchmark runFirstShortVectorRandomBoundedNormSq90 where {
    repeats := 3
    maxSecondsPerCall := 40.0
    expectedHash := some (firstShortVectorRandomBoundedNormSqHash 90)
  }

setup_fixed_benchmark runIsabelleRandomBoundedNormSq90 where {
    repeats := 3
    minTotalSeconds := 1.0
    maxSecondsPerCall := 40.0
    expectedHash := some (firstShortVectorRandomBoundedNormSqHash 90)
    warmupFirstIter := true
  }

setup_fixed_benchmark runFirstShortVectorRandomBoundedNormSq120 where {
    repeats := 3
    maxSecondsPerCall := 60.0
    expectedHash := some (firstShortVectorRandomBoundedNormSqHash 120)
  }

setup_fixed_benchmark runIsabelleRandomBoundedNormSq120 where {
    repeats := 3
    minTotalSeconds := 1.0
    maxSecondsPerCall := 60.0
    expectedHash := some (firstShortVectorRandomBoundedNormSqHash 120)
    warmupFirstIter := true
  }

setup_fixed_benchmark runFirstShortVectorRandomBoundedNormSq150 where {
    repeats := 3
    maxSecondsPerCall := 90.0
    expectedHash := some (firstShortVectorRandomBoundedNormSqHash 150)
  }

setup_fixed_benchmark runIsabelleRandomBoundedNormSq150 where {
    repeats := 3
    minTotalSeconds := 1.0
    maxSecondsPerCall := 90.0
    expectedHash := some (firstShortVectorRandomBoundedNormSqHash 150)
    warmupFirstIter := true
  }

setup_fixed_benchmark runFirstShortVectorRandomBoundedNormSq180 where {
    repeats := 3
    maxSecondsPerCall := 120.0
    expectedHash := some (firstShortVectorRandomBoundedNormSqHash 180)
  }

setup_fixed_benchmark runIsabelleRandomBoundedNormSq180 where {
    repeats := 3
    minTotalSeconds := 1.0
    maxSecondsPerCall := 120.0
    expectedHash := some (firstShortVectorRandomBoundedNormSqHash 180)
    warmupFirstIter := true
  }

setup_fixed_benchmark runFirstShortVectorHarshCubicNormSq15 where {
    repeats := 3
    maxSecondsPerCall := 20.0
    expectedHash := some (firstShortVectorHarshCubicNormSqHash 15)
  }

setup_fixed_benchmark runIsabelleHarshCubicNormSq15 where {
    repeats := 3
    minTotalSeconds := 1.0
    maxSecondsPerCall := 90.0
    expectedHash := some (firstShortVectorHarshCubicNormSqHash 15)
    warmupFirstIter := true
  }

setup_fixed_benchmark runFirstShortVectorHarshCubicNormSq20 where {
    repeats := 3
    maxSecondsPerCall := 20.0
    expectedHash := some (firstShortVectorHarshCubicNormSqHash 20)
  }

setup_fixed_benchmark runIsabelleHarshCubicNormSq20 where {
    repeats := 3
    minTotalSeconds := 1.0
    maxSecondsPerCall := 90.0
    expectedHash := some (firstShortVectorHarshCubicNormSqHash 20)
    warmupFirstIter := true
  }

setup_fixed_benchmark runFirstShortVectorHarshCubicNormSq25 where {
    repeats := 3
    maxSecondsPerCall := 30.0
    expectedHash := some (firstShortVectorHarshCubicNormSqHash 25)
  }

setup_fixed_benchmark runIsabelleHarshCubicNormSq25 where {
    repeats := 3
    minTotalSeconds := 1.0
    maxSecondsPerCall := 90.0
    expectedHash := some (firstShortVectorHarshCubicNormSqHash 25)
    warmupFirstIter := true
  }

setup_fixed_benchmark runFirstShortVectorHarshCubicNormSq30 where {
    repeats := 3
    maxSecondsPerCall := 40.0
    expectedHash := some (firstShortVectorHarshCubicNormSqHash 30)
  }

setup_fixed_benchmark runIsabelleHarshCubicNormSq30 where {
    repeats := 3
    minTotalSeconds := 1.0
    maxSecondsPerCall := 40.0
    expectedHash := some (firstShortVectorHarshCubicNormSqHash 30)
    warmupFirstIter := true
  }

setup_fixed_benchmark runFirstShortVectorHarshCubicNormSq35 where {
    repeats := 3
    maxSecondsPerCall := 40.0
    expectedHash := some (firstShortVectorHarshCubicNormSqHash 35)
  }

setup_fixed_benchmark runIsabelleHarshCubicNormSq35 where {
    repeats := 3
    minTotalSeconds := 1.0
    maxSecondsPerCall := 60.0
    expectedHash := some (firstShortVectorHarshCubicNormSqHash 35)
    warmupFirstIter := true
  }

setup_fixed_benchmark runFirstShortVectorHarshCubicNormSq40 where {
    repeats := 3
    maxSecondsPerCall := 50.0
    expectedHash := some (firstShortVectorHarshCubicNormSqHash 40)
  }

setup_fixed_benchmark runIsabelleHarshCubicNormSq40 where {
    repeats := 3
    minTotalSeconds := 1.0
    maxSecondsPerCall := 60.0
    expectedHash := some (firstShortVectorHarshCubicNormSqHash 40)
    warmupFirstIter := true
  }

setup_fixed_benchmark runFirstShortVectorHarshCubicNormSq45 where {
    repeats := 3
    maxSecondsPerCall := 60.0
    expectedHash := some (firstShortVectorHarshCubicNormSqHash 45)
  }

setup_fixed_benchmark runIsabelleHarshCubicNormSq45 where {
    repeats := 3
    minTotalSeconds := 1.0
    maxSecondsPerCall := 60.0
    expectedHash := some (firstShortVectorHarshCubicNormSqHash 45)
    warmupFirstIter := true
  }

setup_fixed_benchmark runFirstShortVectorHarshCubicNormSq50 where {
    repeats := 3
    maxSecondsPerCall := 60.0
    expectedHash := some (firstShortVectorHarshCubicNormSqHash 50)
  }

setup_fixed_benchmark runIsabelleHarshCubicNormSq50 where {
    repeats := 3
    minTotalSeconds := 1.0
    maxSecondsPerCall := 60.0
    expectedHash := some (firstShortVectorHarshCubicNormSqHash 50)
    warmupFirstIter := true
  }

setup_fixed_benchmark runFirstShortVectorHarshCubicNormSq55 where {
    repeats := 3
    maxSecondsPerCall := 60.0
    expectedHash := some (firstShortVectorHarshCubicNormSqHash 55)
  }

setup_fixed_benchmark runIsabelleHarshCubicNormSq55 where {
    repeats := 3
    minTotalSeconds := 1.0
    maxSecondsPerCall := 60.0
    expectedHash := some (firstShortVectorHarshCubicNormSqHash 55)
    warmupFirstIter := true
  }

setup_fixed_benchmark runFirstShortVectorHarshCubicNormSq60 where {
    repeats := 3
    maxSecondsPerCall := 60.0
    expectedHash := some (firstShortVectorHarshCubicNormSqHash 60)
  }

setup_fixed_benchmark runIsabelleHarshCubicNormSq60 where {
    repeats := 3
    maxSecondsPerCall := 60.0
    expectedHash := some (firstShortVectorHarshCubicNormSqHash 60)
    warmupFirstIter := true
  }

setup_fixed_benchmark runFirstShortVectorHarshCubicNormSq65 where {
    repeats := 3
    maxSecondsPerCall := 60.0
    expectedHash := some (firstShortVectorHarshCubicNormSqHash 65)
  }

setup_fixed_benchmark runNativeFirstShortVectorRandomBoundedNormSq30 where {
    repeats := 3
    maxSecondsPerCall := 20.0
    expectedHash := some (firstShortVectorRandomBoundedNormSqHash 30)
  }

setup_fixed_benchmark runNativeFirstShortVectorRandomBoundedNormSq45 where {
    repeats := 3
    maxSecondsPerCall := 20.0
    expectedHash := some (firstShortVectorRandomBoundedNormSqHash 45)
  }

setup_fixed_benchmark runNativeFirstShortVectorRandomBoundedNormSq60 where {
    repeats := 3
    maxSecondsPerCall := 30.0
    expectedHash := some (firstShortVectorRandomBoundedNormSqHash 60)
  }

setup_fixed_benchmark runNativeFirstShortVectorRandomBoundedNormSq75 where {
    repeats := 3
    maxSecondsPerCall := 30.0
    expectedHash := some (firstShortVectorRandomBoundedNormSqHash 75)
  }

setup_fixed_benchmark runNativeFirstShortVectorRandomBoundedNormSq90 where {
    repeats := 3
    maxSecondsPerCall := 40.0
    expectedHash := some (firstShortVectorRandomBoundedNormSqHash 90)
  }

setup_fixed_benchmark runNativeFirstShortVectorRandomBoundedNormSq120 where {
    repeats := 3
    maxSecondsPerCall := 60.0
    expectedHash := some (firstShortVectorRandomBoundedNormSqHash 120)
  }

setup_fixed_benchmark runNativeFirstShortVectorRandomBoundedNormSq150 where {
    repeats := 3
    maxSecondsPerCall := 90.0
    expectedHash := some (firstShortVectorRandomBoundedNormSqHash 150)
  }

setup_fixed_benchmark runNativeFirstShortVectorRandomBoundedNormSq180 where {
    repeats := 3
    maxSecondsPerCall := 120.0
    expectedHash := some (firstShortVectorRandomBoundedNormSqHash 180)
  }

setup_fixed_benchmark runNativeFirstShortVectorHarshCubicNormSq15 where {
    repeats := 3
    maxSecondsPerCall := 20.0
    expectedHash := some (firstShortVectorHarshCubicNormSqHash 15)
  }

setup_fixed_benchmark runNativeFirstShortVectorHarshCubicNormSq20 where {
    repeats := 3
    maxSecondsPerCall := 20.0
    expectedHash := some (firstShortVectorHarshCubicNormSqHash 20)
  }

setup_fixed_benchmark runNativeFirstShortVectorHarshCubicNormSq25 where {
    repeats := 3
    maxSecondsPerCall := 30.0
    expectedHash := some (firstShortVectorHarshCubicNormSqHash 25)
  }

setup_fixed_benchmark runNativeFirstShortVectorHarshCubicNormSq30 where {
    repeats := 3
    maxSecondsPerCall := 40.0
    expectedHash := some (firstShortVectorHarshCubicNormSqHash 30)
  }

setup_fixed_benchmark runNativeFirstShortVectorHarshCubicNormSq35 where {
    repeats := 3
    maxSecondsPerCall := 40.0
    expectedHash := some (firstShortVectorHarshCubicNormSqHash 35)
  }

setup_fixed_benchmark runNativeFirstShortVectorHarshCubicNormSq40 where {
    repeats := 3
    maxSecondsPerCall := 50.0
    expectedHash := some (firstShortVectorHarshCubicNormSqHash 40)
  }

setup_fixed_benchmark runNativeFirstShortVectorHarshCubicNormSq45 where {
    repeats := 3
    maxSecondsPerCall := 60.0
    expectedHash := some (firstShortVectorHarshCubicNormSqHash 45)
  }

setup_fixed_benchmark runNativeFirstShortVectorHarshCubicNormSq50 where {
    repeats := 3
    maxSecondsPerCall := 60.0
    expectedHash := some (firstShortVectorHarshCubicNormSqHash 50)
  }

setup_fixed_benchmark runNativeFirstShortVectorHarshCubicNormSq55 where {
    repeats := 3
    maxSecondsPerCall := 60.0
    expectedHash := some (firstShortVectorHarshCubicNormSqHash 55)
  }

setup_fixed_benchmark runNativeFirstShortVectorHarshCubicNormSq60 where {
    repeats := 3
    maxSecondsPerCall := 60.0
    expectedHash := some (firstShortVectorHarshCubicNormSqHash 60)
  }

setup_fixed_benchmark runNativeFirstShortVectorHarshCubicNormSq65 where {
    repeats := 3
    maxSecondsPerCall := 60.0
    expectedHash := some (firstShortVectorHarshCubicNormSqHash 65)
  }


setup_fixed_benchmark runIsabelleHarshCubicNormSq65 where {
    repeats := 3
    maxSecondsPerCall := 60.0
    expectedHash := some (firstShortVectorHarshCubicNormSqHash 65)
    warmupFirstIter := true
  }

/- Verified-Isabelle certified-LLL registrations. These use the Zenodo
`svp_certified` driver, which invokes the `fplll` binary per request and then
checks the two-transform certificate before returning the squared norm. -/
setup_fixed_benchmark runIsabelleCertifiedProcessFloorNormSq where {
    repeats := 5
    minTotalSeconds := 1.0
    maxSecondsPerCall := 90.0
    expectedHash := none
    warmupFirstIter := true
  }

setup_fixed_benchmark runIsabelleCertifiedRandomBoundedNormSq30 where {
    repeats := 3
    minTotalSeconds := 1.0
    maxSecondsPerCall := 20.0
    expectedHash := some (firstShortVectorRandomBoundedNormSqHash 30)
    warmupFirstIter := true
  }

setup_fixed_benchmark runIsabelleCertifiedRandomBoundedNormSq45 where {
    repeats := 3
    minTotalSeconds := 1.0
    maxSecondsPerCall := 20.0
    expectedHash := some (firstShortVectorRandomBoundedNormSqHash 45)
    warmupFirstIter := true
  }

setup_fixed_benchmark runIsabelleCertifiedRandomBoundedNormSq60 where {
    repeats := 3
    minTotalSeconds := 1.0
    maxSecondsPerCall := 30.0
    expectedHash := some (firstShortVectorRandomBoundedNormSqHash 60)
    warmupFirstIter := true
  }

setup_fixed_benchmark runIsabelleCertifiedRandomBoundedNormSq75 where {
    repeats := 3
    minTotalSeconds := 1.0
    maxSecondsPerCall := 30.0
    expectedHash := some (firstShortVectorRandomBoundedNormSqHash 75)
    warmupFirstIter := true
  }

setup_fixed_benchmark runIsabelleCertifiedRandomBoundedNormSq90 where {
    repeats := 3
    minTotalSeconds := 1.0
    maxSecondsPerCall := 40.0
    expectedHash := some (firstShortVectorRandomBoundedNormSqHash 90)
    warmupFirstIter := true
  }

setup_fixed_benchmark runIsabelleCertifiedRandomBoundedNormSq120 where {
    repeats := 3
    minTotalSeconds := 1.0
    maxSecondsPerCall := 60.0
    expectedHash := some (firstShortVectorRandomBoundedNormSqHash 120)
    warmupFirstIter := true
  }

setup_fixed_benchmark runIsabelleCertifiedRandomBoundedNormSq150 where {
    repeats := 3
    minTotalSeconds := 1.0
    maxSecondsPerCall := 90.0
    expectedHash := some (firstShortVectorRandomBoundedNormSqHash 150)
    warmupFirstIter := true
  }

setup_fixed_benchmark runIsabelleCertifiedRandomBoundedNormSq180 where {
    repeats := 3
    minTotalSeconds := 1.0
    maxSecondsPerCall := 120.0
    expectedHash := some (firstShortVectorRandomBoundedNormSqHash 180)
    warmupFirstIter := true
  }

setup_fixed_benchmark runIsabelleCertifiedHarshCubicNormSq15 where {
    repeats := 3
    minTotalSeconds := 1.0
    maxSecondsPerCall := 90.0
    expectedHash := some (firstShortVectorHarshCubicNormSqHash 15)
    warmupFirstIter := true
  }

setup_fixed_benchmark runIsabelleCertifiedHarshCubicNormSq20 where {
    repeats := 3
    minTotalSeconds := 1.0
    maxSecondsPerCall := 90.0
    expectedHash := some (firstShortVectorHarshCubicNormSqHash 20)
    warmupFirstIter := true
  }

setup_fixed_benchmark runIsabelleCertifiedHarshCubicNormSq25 where {
    repeats := 3
    minTotalSeconds := 1.0
    maxSecondsPerCall := 90.0
    expectedHash := some (firstShortVectorHarshCubicNormSqHash 25)
    warmupFirstIter := true
  }

setup_fixed_benchmark runIsabelleCertifiedHarshCubicNormSq30 where {
    repeats := 3
    minTotalSeconds := 1.0
    maxSecondsPerCall := 40.0
    expectedHash := some (firstShortVectorHarshCubicNormSqHash 30)
    warmupFirstIter := true
  }

setup_fixed_benchmark runIsabelleCertifiedHarshCubicNormSq35 where {
    repeats := 3
    minTotalSeconds := 1.0
    maxSecondsPerCall := 60.0
    expectedHash := some (firstShortVectorHarshCubicNormSqHash 35)
    warmupFirstIter := true
  }

setup_fixed_benchmark runIsabelleCertifiedHarshCubicNormSq40 where {
    repeats := 3
    minTotalSeconds := 1.0
    maxSecondsPerCall := 60.0
    expectedHash := some (firstShortVectorHarshCubicNormSqHash 40)
    warmupFirstIter := true
  }

setup_fixed_benchmark runIsabelleCertifiedHarshCubicNormSq45 where {
    repeats := 3
    minTotalSeconds := 1.0
    maxSecondsPerCall := 60.0
    expectedHash := some (firstShortVectorHarshCubicNormSqHash 45)
    warmupFirstIter := true
  }

setup_fixed_benchmark runIsabelleCertifiedHarshCubicNormSq50 where {
    repeats := 3
    minTotalSeconds := 1.0
    maxSecondsPerCall := 60.0
    expectedHash := some (firstShortVectorHarshCubicNormSqHash 50)
    warmupFirstIter := true
  }

setup_fixed_benchmark runIsabelleCertifiedHarshCubicNormSq55 where {
    repeats := 3
    minTotalSeconds := 1.0
    maxSecondsPerCall := 60.0
    expectedHash := some (firstShortVectorHarshCubicNormSqHash 55)
    warmupFirstIter := true
  }

setup_fixed_benchmark runIsabelleCertifiedHarshCubicNormSq60 where {
    repeats := 3
    maxSecondsPerCall := 60.0
    expectedHash := some (firstShortVectorHarshCubicNormSqHash 60)
    warmupFirstIter := true
  }

setup_fixed_benchmark runIsabelleCertifiedHarshCubicNormSq65 where {
    repeats := 3
    maxSecondsPerCall := 60.0
    expectedHash := some (firstShortVectorHarshCubicNormSqHash 65)
    warmupFirstIter := true
  }


-- BEGIN Ajtai family targets (generated)
/-! ## Ajtai-style worst-case `lll.firstShortVector` targets. -/

initialize ajtaiInput8Ref : IO.Ref (Option FirstShortVectorInput) ← IO.mkRef none

def runFirstShortVectorAjtaiNormSq8 : Unit → IO Int := fun _ => do
  return runFirstShortVectorNormSq (← getCachedInput ajtaiInput8Ref (fun _ => prepAjtaiInput 8))

def runNativeFirstShortVectorAjtaiNormSq8 : Unit → IO Int := fun _ => do
  return runNativeFirstShortVectorNormSq (← getCachedInput ajtaiInput8Ref (fun _ => prepAjtaiInput 8))

def runIsabelleAjtaiNormSq8 : Unit → IO Int := fun _ => do
  runIsabelleShortVectorNormSq "ajtai-8" (← getCachedInput ajtaiInput8Ref (fun _ => prepAjtaiInput 8))

def runIsabelleCertifiedAjtaiNormSq8 : Unit → IO Int := fun _ => do
  runIsabelleCertifiedShortVectorNormSq "ajtai-8" (← getCachedInput ajtaiInput8Ref (fun _ => prepAjtaiInput 8))

def runFpLLLFirstShortVectorAjtai8Checksum : Unit → IO Int := fun _ => do
  runFpLLLFirstShortVectorChecksum (← getCachedInput ajtaiInput8Ref (fun _ => prepAjtaiInput 8))

def runCertifiedFirstShortVectorAjtai8Checksum : Unit → IO Int := fun _ => do
  runCertifiedFirstShortVectorChecksum (← getCachedInput ajtaiInput8Ref (fun _ => prepAjtaiInput 8))

setup_fixed_benchmark runFirstShortVectorAjtaiNormSq8 where {
    repeats := 3
    minTotalSeconds := 1.0
    maxSecondsPerCall := 90.0
    warmupFirstIter := true
  }

setup_fixed_benchmark runNativeFirstShortVectorAjtaiNormSq8 where {
    repeats := 3
    minTotalSeconds := 1.0
    maxSecondsPerCall := 90.0
    warmupFirstIter := true
  }

setup_fixed_benchmark runIsabelleAjtaiNormSq8 where {
    repeats := 3
    minTotalSeconds := 1.0
    maxSecondsPerCall := 90.0
    warmupFirstIter := true
  }

setup_fixed_benchmark runIsabelleCertifiedAjtaiNormSq8 where {
    repeats := 3
    minTotalSeconds := 1.0
    maxSecondsPerCall := 90.0
    warmupFirstIter := true
  }

setup_fixed_benchmark runFpLLLFirstShortVectorAjtai8Checksum where {
    repeats := 5
    minTotalSeconds := 1.0
    maxSecondsPerCall := 30.0
    warmupFirstIter := true
  }

setup_fixed_benchmark runCertifiedFirstShortVectorAjtai8Checksum where {
    repeats := 3
    minTotalSeconds := 1.0
    maxSecondsPerCall := 30.0
    warmupFirstIter := true
  }

initialize ajtaiInput12Ref : IO.Ref (Option FirstShortVectorInput) ← IO.mkRef none

def runFirstShortVectorAjtaiNormSq12 : Unit → IO Int := fun _ => do
  return runFirstShortVectorNormSq (← getCachedInput ajtaiInput12Ref (fun _ => prepAjtaiInput 12))

def runNativeFirstShortVectorAjtaiNormSq12 : Unit → IO Int := fun _ => do
  return runNativeFirstShortVectorNormSq (← getCachedInput ajtaiInput12Ref (fun _ => prepAjtaiInput 12))

def runIsabelleAjtaiNormSq12 : Unit → IO Int := fun _ => do
  runIsabelleShortVectorNormSq "ajtai-12" (← getCachedInput ajtaiInput12Ref (fun _ => prepAjtaiInput 12))

def runIsabelleCertifiedAjtaiNormSq12 : Unit → IO Int := fun _ => do
  runIsabelleCertifiedShortVectorNormSq "ajtai-12" (← getCachedInput ajtaiInput12Ref (fun _ => prepAjtaiInput 12))

def runFpLLLFirstShortVectorAjtai12Checksum : Unit → IO Int := fun _ => do
  runFpLLLFirstShortVectorChecksum (← getCachedInput ajtaiInput12Ref (fun _ => prepAjtaiInput 12))

def runCertifiedFirstShortVectorAjtai12Checksum : Unit → IO Int := fun _ => do
  runCertifiedFirstShortVectorChecksum (← getCachedInput ajtaiInput12Ref (fun _ => prepAjtaiInput 12))

setup_fixed_benchmark runFirstShortVectorAjtaiNormSq12 where {
    repeats := 3
    minTotalSeconds := 1.0
    maxSecondsPerCall := 90.0
    warmupFirstIter := true
  }

setup_fixed_benchmark runNativeFirstShortVectorAjtaiNormSq12 where {
    repeats := 3
    minTotalSeconds := 1.0
    maxSecondsPerCall := 90.0
    warmupFirstIter := true
  }

setup_fixed_benchmark runIsabelleAjtaiNormSq12 where {
    repeats := 3
    minTotalSeconds := 1.0
    maxSecondsPerCall := 90.0
    warmupFirstIter := true
  }

setup_fixed_benchmark runIsabelleCertifiedAjtaiNormSq12 where {
    repeats := 3
    minTotalSeconds := 1.0
    maxSecondsPerCall := 90.0
    warmupFirstIter := true
  }

setup_fixed_benchmark runFpLLLFirstShortVectorAjtai12Checksum where {
    repeats := 5
    minTotalSeconds := 1.0
    maxSecondsPerCall := 30.0
    warmupFirstIter := true
  }

setup_fixed_benchmark runCertifiedFirstShortVectorAjtai12Checksum where {
    repeats := 3
    minTotalSeconds := 1.0
    maxSecondsPerCall := 30.0
    warmupFirstIter := true
  }

initialize ajtaiInput16Ref : IO.Ref (Option FirstShortVectorInput) ← IO.mkRef none

def runFirstShortVectorAjtaiNormSq16 : Unit → IO Int := fun _ => do
  return runFirstShortVectorNormSq (← getCachedInput ajtaiInput16Ref (fun _ => prepAjtaiInput 16))

def runNativeFirstShortVectorAjtaiNormSq16 : Unit → IO Int := fun _ => do
  return runNativeFirstShortVectorNormSq (← getCachedInput ajtaiInput16Ref (fun _ => prepAjtaiInput 16))

def runIsabelleAjtaiNormSq16 : Unit → IO Int := fun _ => do
  runIsabelleShortVectorNormSq "ajtai-16" (← getCachedInput ajtaiInput16Ref (fun _ => prepAjtaiInput 16))

def runIsabelleCertifiedAjtaiNormSq16 : Unit → IO Int := fun _ => do
  runIsabelleCertifiedShortVectorNormSq "ajtai-16" (← getCachedInput ajtaiInput16Ref (fun _ => prepAjtaiInput 16))

def runFpLLLFirstShortVectorAjtai16Checksum : Unit → IO Int := fun _ => do
  runFpLLLFirstShortVectorChecksum (← getCachedInput ajtaiInput16Ref (fun _ => prepAjtaiInput 16))

def runCertifiedFirstShortVectorAjtai16Checksum : Unit → IO Int := fun _ => do
  runCertifiedFirstShortVectorChecksum (← getCachedInput ajtaiInput16Ref (fun _ => prepAjtaiInput 16))

setup_fixed_benchmark runFirstShortVectorAjtaiNormSq16 where {
    repeats := 3
    minTotalSeconds := 1.0
    maxSecondsPerCall := 90.0
    warmupFirstIter := true
  }

setup_fixed_benchmark runNativeFirstShortVectorAjtaiNormSq16 where {
    repeats := 3
    minTotalSeconds := 1.0
    maxSecondsPerCall := 90.0
    warmupFirstIter := true
  }

setup_fixed_benchmark runIsabelleAjtaiNormSq16 where {
    repeats := 3
    minTotalSeconds := 1.0
    maxSecondsPerCall := 90.0
    warmupFirstIter := true
  }

setup_fixed_benchmark runIsabelleCertifiedAjtaiNormSq16 where {
    repeats := 3
    minTotalSeconds := 1.0
    maxSecondsPerCall := 90.0
    warmupFirstIter := true
  }

setup_fixed_benchmark runFpLLLFirstShortVectorAjtai16Checksum where {
    repeats := 5
    minTotalSeconds := 1.0
    maxSecondsPerCall := 30.0
    warmupFirstIter := true
  }

setup_fixed_benchmark runCertifiedFirstShortVectorAjtai16Checksum where {
    repeats := 3
    minTotalSeconds := 1.0
    maxSecondsPerCall := 30.0
    warmupFirstIter := true
  }

initialize ajtaiInput20Ref : IO.Ref (Option FirstShortVectorInput) ← IO.mkRef none

def runFirstShortVectorAjtaiNormSq20 : Unit → IO Int := fun _ => do
  return runFirstShortVectorNormSq (← getCachedInput ajtaiInput20Ref (fun _ => prepAjtaiInput 20))

def runNativeFirstShortVectorAjtaiNormSq20 : Unit → IO Int := fun _ => do
  return runNativeFirstShortVectorNormSq (← getCachedInput ajtaiInput20Ref (fun _ => prepAjtaiInput 20))

def runIsabelleAjtaiNormSq20 : Unit → IO Int := fun _ => do
  runIsabelleShortVectorNormSq "ajtai-20" (← getCachedInput ajtaiInput20Ref (fun _ => prepAjtaiInput 20))

def runIsabelleCertifiedAjtaiNormSq20 : Unit → IO Int := fun _ => do
  runIsabelleCertifiedShortVectorNormSq "ajtai-20" (← getCachedInput ajtaiInput20Ref (fun _ => prepAjtaiInput 20))

def runFpLLLFirstShortVectorAjtai20Checksum : Unit → IO Int := fun _ => do
  runFpLLLFirstShortVectorChecksum (← getCachedInput ajtaiInput20Ref (fun _ => prepAjtaiInput 20))

def runCertifiedFirstShortVectorAjtai20Checksum : Unit → IO Int := fun _ => do
  runCertifiedFirstShortVectorChecksum (← getCachedInput ajtaiInput20Ref (fun _ => prepAjtaiInput 20))

setup_fixed_benchmark runFirstShortVectorAjtaiNormSq20 where {
    repeats := 3
    minTotalSeconds := 1.0
    maxSecondsPerCall := 90.0
    warmupFirstIter := true
  }

setup_fixed_benchmark runNativeFirstShortVectorAjtaiNormSq20 where {
    repeats := 3
    minTotalSeconds := 1.0
    maxSecondsPerCall := 90.0
    warmupFirstIter := true
  }

setup_fixed_benchmark runIsabelleAjtaiNormSq20 where {
    repeats := 3
    minTotalSeconds := 1.0
    maxSecondsPerCall := 90.0
    warmupFirstIter := true
  }

setup_fixed_benchmark runIsabelleCertifiedAjtaiNormSq20 where {
    repeats := 3
    minTotalSeconds := 1.0
    maxSecondsPerCall := 90.0
    warmupFirstIter := true
  }

setup_fixed_benchmark runFpLLLFirstShortVectorAjtai20Checksum where {
    repeats := 5
    minTotalSeconds := 1.0
    maxSecondsPerCall := 30.0
    warmupFirstIter := true
  }

setup_fixed_benchmark runCertifiedFirstShortVectorAjtai20Checksum where {
    repeats := 3
    minTotalSeconds := 1.0
    maxSecondsPerCall := 30.0
    warmupFirstIter := true
  }

initialize ajtaiInput24Ref : IO.Ref (Option FirstShortVectorInput) ← IO.mkRef none

def runFirstShortVectorAjtaiNormSq24 : Unit → IO Int := fun _ => do
  return runFirstShortVectorNormSq (← getCachedInput ajtaiInput24Ref (fun _ => prepAjtaiInput 24))

def runNativeFirstShortVectorAjtaiNormSq24 : Unit → IO Int := fun _ => do
  return runNativeFirstShortVectorNormSq (← getCachedInput ajtaiInput24Ref (fun _ => prepAjtaiInput 24))

def runIsabelleAjtaiNormSq24 : Unit → IO Int := fun _ => do
  runIsabelleShortVectorNormSq "ajtai-24" (← getCachedInput ajtaiInput24Ref (fun _ => prepAjtaiInput 24))

def runIsabelleCertifiedAjtaiNormSq24 : Unit → IO Int := fun _ => do
  runIsabelleCertifiedShortVectorNormSq "ajtai-24" (← getCachedInput ajtaiInput24Ref (fun _ => prepAjtaiInput 24))

def runFpLLLFirstShortVectorAjtai24Checksum : Unit → IO Int := fun _ => do
  runFpLLLFirstShortVectorChecksum (← getCachedInput ajtaiInput24Ref (fun _ => prepAjtaiInput 24))

def runCertifiedFirstShortVectorAjtai24Checksum : Unit → IO Int := fun _ => do
  runCertifiedFirstShortVectorChecksum (← getCachedInput ajtaiInput24Ref (fun _ => prepAjtaiInput 24))

setup_fixed_benchmark runFirstShortVectorAjtaiNormSq24 where {
    repeats := 3
    minTotalSeconds := 1.0
    maxSecondsPerCall := 90.0
    warmupFirstIter := true
  }

setup_fixed_benchmark runNativeFirstShortVectorAjtaiNormSq24 where {
    repeats := 3
    minTotalSeconds := 1.0
    maxSecondsPerCall := 90.0
    warmupFirstIter := true
  }

setup_fixed_benchmark runIsabelleAjtaiNormSq24 where {
    repeats := 3
    minTotalSeconds := 1.0
    maxSecondsPerCall := 90.0
    warmupFirstIter := true
  }

setup_fixed_benchmark runIsabelleCertifiedAjtaiNormSq24 where {
    repeats := 3
    minTotalSeconds := 1.0
    maxSecondsPerCall := 90.0
    warmupFirstIter := true
  }

setup_fixed_benchmark runFpLLLFirstShortVectorAjtai24Checksum where {
    repeats := 5
    minTotalSeconds := 1.0
    maxSecondsPerCall := 30.0
    warmupFirstIter := true
  }

setup_fixed_benchmark runCertifiedFirstShortVectorAjtai24Checksum where {
    repeats := 3
    minTotalSeconds := 1.0
    maxSecondsPerCall := 30.0
    warmupFirstIter := true
  }

initialize ajtaiInput28Ref : IO.Ref (Option FirstShortVectorInput) ← IO.mkRef none

def runFirstShortVectorAjtaiNormSq28 : Unit → IO Int := fun _ => do
  return runFirstShortVectorNormSq (← getCachedInput ajtaiInput28Ref (fun _ => prepAjtaiInput 28))

def runNativeFirstShortVectorAjtaiNormSq28 : Unit → IO Int := fun _ => do
  return runNativeFirstShortVectorNormSq (← getCachedInput ajtaiInput28Ref (fun _ => prepAjtaiInput 28))

def runIsabelleAjtaiNormSq28 : Unit → IO Int := fun _ => do
  runIsabelleShortVectorNormSq "ajtai-28" (← getCachedInput ajtaiInput28Ref (fun _ => prepAjtaiInput 28))

def runIsabelleCertifiedAjtaiNormSq28 : Unit → IO Int := fun _ => do
  runIsabelleCertifiedShortVectorNormSq "ajtai-28" (← getCachedInput ajtaiInput28Ref (fun _ => prepAjtaiInput 28))

def runFpLLLFirstShortVectorAjtai28Checksum : Unit → IO Int := fun _ => do
  runFpLLLFirstShortVectorChecksum (← getCachedInput ajtaiInput28Ref (fun _ => prepAjtaiInput 28))

def runCertifiedFirstShortVectorAjtai28Checksum : Unit → IO Int := fun _ => do
  runCertifiedFirstShortVectorChecksum (← getCachedInput ajtaiInput28Ref (fun _ => prepAjtaiInput 28))

setup_fixed_benchmark runFirstShortVectorAjtaiNormSq28 where {
    repeats := 3
    minTotalSeconds := 1.0
    maxSecondsPerCall := 90.0
    warmupFirstIter := true
  }

setup_fixed_benchmark runNativeFirstShortVectorAjtaiNormSq28 where {
    repeats := 3
    minTotalSeconds := 1.0
    maxSecondsPerCall := 90.0
    warmupFirstIter := true
  }

setup_fixed_benchmark runIsabelleAjtaiNormSq28 where {
    repeats := 3
    minTotalSeconds := 1.0
    maxSecondsPerCall := 90.0
    warmupFirstIter := true
  }

setup_fixed_benchmark runIsabelleCertifiedAjtaiNormSq28 where {
    repeats := 3
    minTotalSeconds := 1.0
    maxSecondsPerCall := 90.0
    warmupFirstIter := true
  }

setup_fixed_benchmark runFpLLLFirstShortVectorAjtai28Checksum where {
    repeats := 5
    minTotalSeconds := 1.0
    maxSecondsPerCall := 30.0
    warmupFirstIter := true
  }

setup_fixed_benchmark runCertifiedFirstShortVectorAjtai28Checksum where {
    repeats := 3
    minTotalSeconds := 1.0
    maxSecondsPerCall := 30.0
    warmupFirstIter := true
  }

initialize ajtaiInput32Ref : IO.Ref (Option FirstShortVectorInput) ← IO.mkRef none

def runFirstShortVectorAjtaiNormSq32 : Unit → IO Int := fun _ => do
  return runFirstShortVectorNormSq (← getCachedInput ajtaiInput32Ref (fun _ => prepAjtaiInput 32))

def runNativeFirstShortVectorAjtaiNormSq32 : Unit → IO Int := fun _ => do
  return runNativeFirstShortVectorNormSq (← getCachedInput ajtaiInput32Ref (fun _ => prepAjtaiInput 32))

def runIsabelleAjtaiNormSq32 : Unit → IO Int := fun _ => do
  runIsabelleShortVectorNormSq "ajtai-32" (← getCachedInput ajtaiInput32Ref (fun _ => prepAjtaiInput 32))

def runIsabelleCertifiedAjtaiNormSq32 : Unit → IO Int := fun _ => do
  runIsabelleCertifiedShortVectorNormSq "ajtai-32" (← getCachedInput ajtaiInput32Ref (fun _ => prepAjtaiInput 32))

def runFpLLLFirstShortVectorAjtai32Checksum : Unit → IO Int := fun _ => do
  runFpLLLFirstShortVectorChecksum (← getCachedInput ajtaiInput32Ref (fun _ => prepAjtaiInput 32))

def runCertifiedFirstShortVectorAjtai32Checksum : Unit → IO Int := fun _ => do
  runCertifiedFirstShortVectorChecksum (← getCachedInput ajtaiInput32Ref (fun _ => prepAjtaiInput 32))

setup_fixed_benchmark runFirstShortVectorAjtaiNormSq32 where {
    repeats := 3
    minTotalSeconds := 1.0
    maxSecondsPerCall := 90.0
    warmupFirstIter := true
  }

setup_fixed_benchmark runNativeFirstShortVectorAjtaiNormSq32 where {
    repeats := 3
    minTotalSeconds := 1.0
    maxSecondsPerCall := 90.0
    warmupFirstIter := true
  }

setup_fixed_benchmark runIsabelleAjtaiNormSq32 where {
    repeats := 3
    minTotalSeconds := 1.0
    maxSecondsPerCall := 90.0
    warmupFirstIter := true
  }

setup_fixed_benchmark runIsabelleCertifiedAjtaiNormSq32 where {
    repeats := 3
    minTotalSeconds := 1.0
    maxSecondsPerCall := 90.0
    warmupFirstIter := true
  }

setup_fixed_benchmark runFpLLLFirstShortVectorAjtai32Checksum where {
    repeats := 5
    minTotalSeconds := 1.0
    maxSecondsPerCall := 30.0
    warmupFirstIter := true
  }

setup_fixed_benchmark runCertifiedFirstShortVectorAjtai32Checksum where {
    repeats := 3
    minTotalSeconds := 1.0
    maxSecondsPerCall := 30.0
    warmupFirstIter := true
  }

initialize ajtaiInput36Ref : IO.Ref (Option FirstShortVectorInput) ← IO.mkRef none

def runFirstShortVectorAjtaiNormSq36 : Unit → IO Int := fun _ => do
  return runFirstShortVectorNormSq (← getCachedInput ajtaiInput36Ref (fun _ => prepAjtaiInput 36))

def runNativeFirstShortVectorAjtaiNormSq36 : Unit → IO Int := fun _ => do
  return runNativeFirstShortVectorNormSq (← getCachedInput ajtaiInput36Ref (fun _ => prepAjtaiInput 36))

def runIsabelleAjtaiNormSq36 : Unit → IO Int := fun _ => do
  runIsabelleShortVectorNormSq "ajtai-36" (← getCachedInput ajtaiInput36Ref (fun _ => prepAjtaiInput 36))

def runIsabelleCertifiedAjtaiNormSq36 : Unit → IO Int := fun _ => do
  runIsabelleCertifiedShortVectorNormSq "ajtai-36" (← getCachedInput ajtaiInput36Ref (fun _ => prepAjtaiInput 36))

def runFpLLLFirstShortVectorAjtai36Checksum : Unit → IO Int := fun _ => do
  runFpLLLFirstShortVectorChecksum (← getCachedInput ajtaiInput36Ref (fun _ => prepAjtaiInput 36))

def runCertifiedFirstShortVectorAjtai36Checksum : Unit → IO Int := fun _ => do
  runCertifiedFirstShortVectorChecksum (← getCachedInput ajtaiInput36Ref (fun _ => prepAjtaiInput 36))

setup_fixed_benchmark runFirstShortVectorAjtaiNormSq36 where {
    repeats := 3
    minTotalSeconds := 1.0
    maxSecondsPerCall := 90.0
    warmupFirstIter := true
  }

setup_fixed_benchmark runNativeFirstShortVectorAjtaiNormSq36 where {
    repeats := 3
    minTotalSeconds := 1.0
    maxSecondsPerCall := 90.0
    warmupFirstIter := true
  }

setup_fixed_benchmark runIsabelleAjtaiNormSq36 where {
    repeats := 3
    minTotalSeconds := 1.0
    maxSecondsPerCall := 90.0
    warmupFirstIter := true
  }

setup_fixed_benchmark runIsabelleCertifiedAjtaiNormSq36 where {
    repeats := 3
    minTotalSeconds := 1.0
    maxSecondsPerCall := 90.0
    warmupFirstIter := true
  }

setup_fixed_benchmark runFpLLLFirstShortVectorAjtai36Checksum where {
    repeats := 5
    minTotalSeconds := 1.0
    maxSecondsPerCall := 30.0
    warmupFirstIter := true
  }

setup_fixed_benchmark runCertifiedFirstShortVectorAjtai36Checksum where {
    repeats := 3
    minTotalSeconds := 1.0
    maxSecondsPerCall := 30.0
    warmupFirstIter := true
  }

-- END Ajtai family targets


-- BEGIN Qary family targets (generated)
/-! ## qary `lll.firstShortVector` targets. -/

initialize qaryInput16Ref : IO.Ref (Option FirstShortVectorInput) ← IO.mkRef none

def runFirstShortVectorQaryNormSq16 : Unit → IO Int := fun _ => do
  return runFirstShortVectorNormSq (← getCachedInput qaryInput16Ref (fun _ => prepQaryInput 16))

def runNativeFirstShortVectorQaryNormSq16 : Unit → IO Int := fun _ => do
  return runNativeFirstShortVectorNormSq (← getCachedInput qaryInput16Ref (fun _ => prepQaryInput 16))

def runIsabelleQaryNormSq16 : Unit → IO Int := fun _ => do
  runIsabelleShortVectorNormSq "qary-16" (← getCachedInput qaryInput16Ref (fun _ => prepQaryInput 16))

def runIsabelleCertifiedQaryNormSq16 : Unit → IO Int := fun _ => do
  runIsabelleCertifiedShortVectorNormSq "qary-16" (← getCachedInput qaryInput16Ref (fun _ => prepQaryInput 16))

def runFpLLLFirstShortVectorQary16Checksum : Unit → IO Int := fun _ => do
  runFpLLLFirstShortVectorChecksum (← getCachedInput qaryInput16Ref (fun _ => prepQaryInput 16))

def runCertifiedFirstShortVectorQary16Checksum : Unit → IO Int := fun _ => do
  runCertifiedFirstShortVectorChecksum (← getCachedInput qaryInput16Ref (fun _ => prepQaryInput 16))

setup_fixed_benchmark runFirstShortVectorQaryNormSq16 where {
    repeats := 3
    minTotalSeconds := 1.0
    maxSecondsPerCall := 90.0
    warmupFirstIter := true
  }

setup_fixed_benchmark runNativeFirstShortVectorQaryNormSq16 where {
    repeats := 3
    minTotalSeconds := 1.0
    maxSecondsPerCall := 90.0
    warmupFirstIter := true
  }

setup_fixed_benchmark runIsabelleQaryNormSq16 where {
    repeats := 3
    minTotalSeconds := 1.0
    maxSecondsPerCall := 90.0
    warmupFirstIter := true
  }

setup_fixed_benchmark runIsabelleCertifiedQaryNormSq16 where {
    repeats := 3
    minTotalSeconds := 1.0
    maxSecondsPerCall := 90.0
    warmupFirstIter := true
  }

setup_fixed_benchmark runFpLLLFirstShortVectorQary16Checksum where {
    repeats := 5
    minTotalSeconds := 1.0
    maxSecondsPerCall := 30.0
    warmupFirstIter := true
  }

setup_fixed_benchmark runCertifiedFirstShortVectorQary16Checksum where {
    repeats := 3
    minTotalSeconds := 1.0
    maxSecondsPerCall := 30.0
    warmupFirstIter := true
  }

initialize qaryInput24Ref : IO.Ref (Option FirstShortVectorInput) ← IO.mkRef none

def runFirstShortVectorQaryNormSq24 : Unit → IO Int := fun _ => do
  return runFirstShortVectorNormSq (← getCachedInput qaryInput24Ref (fun _ => prepQaryInput 24))

def runNativeFirstShortVectorQaryNormSq24 : Unit → IO Int := fun _ => do
  return runNativeFirstShortVectorNormSq (← getCachedInput qaryInput24Ref (fun _ => prepQaryInput 24))

def runIsabelleQaryNormSq24 : Unit → IO Int := fun _ => do
  runIsabelleShortVectorNormSq "qary-24" (← getCachedInput qaryInput24Ref (fun _ => prepQaryInput 24))

def runIsabelleCertifiedQaryNormSq24 : Unit → IO Int := fun _ => do
  runIsabelleCertifiedShortVectorNormSq "qary-24" (← getCachedInput qaryInput24Ref (fun _ => prepQaryInput 24))

def runFpLLLFirstShortVectorQary24Checksum : Unit → IO Int := fun _ => do
  runFpLLLFirstShortVectorChecksum (← getCachedInput qaryInput24Ref (fun _ => prepQaryInput 24))

def runCertifiedFirstShortVectorQary24Checksum : Unit → IO Int := fun _ => do
  runCertifiedFirstShortVectorChecksum (← getCachedInput qaryInput24Ref (fun _ => prepQaryInput 24))

setup_fixed_benchmark runFirstShortVectorQaryNormSq24 where {
    repeats := 3
    minTotalSeconds := 1.0
    maxSecondsPerCall := 90.0
    warmupFirstIter := true
  }

setup_fixed_benchmark runNativeFirstShortVectorQaryNormSq24 where {
    repeats := 3
    minTotalSeconds := 1.0
    maxSecondsPerCall := 90.0
    warmupFirstIter := true
  }

setup_fixed_benchmark runIsabelleQaryNormSq24 where {
    repeats := 3
    minTotalSeconds := 1.0
    maxSecondsPerCall := 90.0
    warmupFirstIter := true
  }

setup_fixed_benchmark runIsabelleCertifiedQaryNormSq24 where {
    repeats := 3
    minTotalSeconds := 1.0
    maxSecondsPerCall := 90.0
    warmupFirstIter := true
  }

setup_fixed_benchmark runFpLLLFirstShortVectorQary24Checksum where {
    repeats := 5
    minTotalSeconds := 1.0
    maxSecondsPerCall := 30.0
    warmupFirstIter := true
  }

setup_fixed_benchmark runCertifiedFirstShortVectorQary24Checksum where {
    repeats := 3
    minTotalSeconds := 1.0
    maxSecondsPerCall := 30.0
    warmupFirstIter := true
  }

initialize qaryInput32Ref : IO.Ref (Option FirstShortVectorInput) ← IO.mkRef none

def runFirstShortVectorQaryNormSq32 : Unit → IO Int := fun _ => do
  return runFirstShortVectorNormSq (← getCachedInput qaryInput32Ref (fun _ => prepQaryInput 32))

def runNativeFirstShortVectorQaryNormSq32 : Unit → IO Int := fun _ => do
  return runNativeFirstShortVectorNormSq (← getCachedInput qaryInput32Ref (fun _ => prepQaryInput 32))

def runIsabelleQaryNormSq32 : Unit → IO Int := fun _ => do
  runIsabelleShortVectorNormSq "qary-32" (← getCachedInput qaryInput32Ref (fun _ => prepQaryInput 32))

def runIsabelleCertifiedQaryNormSq32 : Unit → IO Int := fun _ => do
  runIsabelleCertifiedShortVectorNormSq "qary-32" (← getCachedInput qaryInput32Ref (fun _ => prepQaryInput 32))

def runFpLLLFirstShortVectorQary32Checksum : Unit → IO Int := fun _ => do
  runFpLLLFirstShortVectorChecksum (← getCachedInput qaryInput32Ref (fun _ => prepQaryInput 32))

def runCertifiedFirstShortVectorQary32Checksum : Unit → IO Int := fun _ => do
  runCertifiedFirstShortVectorChecksum (← getCachedInput qaryInput32Ref (fun _ => prepQaryInput 32))

setup_fixed_benchmark runFirstShortVectorQaryNormSq32 where {
    repeats := 3
    minTotalSeconds := 1.0
    maxSecondsPerCall := 90.0
    warmupFirstIter := true
  }

setup_fixed_benchmark runNativeFirstShortVectorQaryNormSq32 where {
    repeats := 3
    minTotalSeconds := 1.0
    maxSecondsPerCall := 90.0
    warmupFirstIter := true
  }

setup_fixed_benchmark runIsabelleQaryNormSq32 where {
    repeats := 3
    minTotalSeconds := 1.0
    maxSecondsPerCall := 90.0
    warmupFirstIter := true
  }

setup_fixed_benchmark runIsabelleCertifiedQaryNormSq32 where {
    repeats := 3
    minTotalSeconds := 1.0
    maxSecondsPerCall := 90.0
    warmupFirstIter := true
  }

setup_fixed_benchmark runFpLLLFirstShortVectorQary32Checksum where {
    repeats := 5
    minTotalSeconds := 1.0
    maxSecondsPerCall := 30.0
    warmupFirstIter := true
  }

setup_fixed_benchmark runCertifiedFirstShortVectorQary32Checksum where {
    repeats := 3
    minTotalSeconds := 1.0
    maxSecondsPerCall := 30.0
    warmupFirstIter := true
  }

initialize qaryInput40Ref : IO.Ref (Option FirstShortVectorInput) ← IO.mkRef none

def runFirstShortVectorQaryNormSq40 : Unit → IO Int := fun _ => do
  return runFirstShortVectorNormSq (← getCachedInput qaryInput40Ref (fun _ => prepQaryInput 40))

def runNativeFirstShortVectorQaryNormSq40 : Unit → IO Int := fun _ => do
  return runNativeFirstShortVectorNormSq (← getCachedInput qaryInput40Ref (fun _ => prepQaryInput 40))

def runIsabelleQaryNormSq40 : Unit → IO Int := fun _ => do
  runIsabelleShortVectorNormSq "qary-40" (← getCachedInput qaryInput40Ref (fun _ => prepQaryInput 40))

def runIsabelleCertifiedQaryNormSq40 : Unit → IO Int := fun _ => do
  runIsabelleCertifiedShortVectorNormSq "qary-40" (← getCachedInput qaryInput40Ref (fun _ => prepQaryInput 40))

def runFpLLLFirstShortVectorQary40Checksum : Unit → IO Int := fun _ => do
  runFpLLLFirstShortVectorChecksum (← getCachedInput qaryInput40Ref (fun _ => prepQaryInput 40))

def runCertifiedFirstShortVectorQary40Checksum : Unit → IO Int := fun _ => do
  runCertifiedFirstShortVectorChecksum (← getCachedInput qaryInput40Ref (fun _ => prepQaryInput 40))

setup_fixed_benchmark runFirstShortVectorQaryNormSq40 where {
    repeats := 3
    minTotalSeconds := 1.0
    maxSecondsPerCall := 90.0
    warmupFirstIter := true
  }

setup_fixed_benchmark runNativeFirstShortVectorQaryNormSq40 where {
    repeats := 3
    minTotalSeconds := 1.0
    maxSecondsPerCall := 90.0
    warmupFirstIter := true
  }

setup_fixed_benchmark runIsabelleQaryNormSq40 where {
    repeats := 3
    minTotalSeconds := 1.0
    maxSecondsPerCall := 90.0
    warmupFirstIter := true
  }

setup_fixed_benchmark runIsabelleCertifiedQaryNormSq40 where {
    repeats := 3
    minTotalSeconds := 1.0
    maxSecondsPerCall := 90.0
    warmupFirstIter := true
  }

setup_fixed_benchmark runFpLLLFirstShortVectorQary40Checksum where {
    repeats := 5
    minTotalSeconds := 1.0
    maxSecondsPerCall := 30.0
    warmupFirstIter := true
  }

setup_fixed_benchmark runCertifiedFirstShortVectorQary40Checksum where {
    repeats := 3
    minTotalSeconds := 1.0
    maxSecondsPerCall := 30.0
    warmupFirstIter := true
  }

initialize qaryInput48Ref : IO.Ref (Option FirstShortVectorInput) ← IO.mkRef none

def runFirstShortVectorQaryNormSq48 : Unit → IO Int := fun _ => do
  return runFirstShortVectorNormSq (← getCachedInput qaryInput48Ref (fun _ => prepQaryInput 48))

def runNativeFirstShortVectorQaryNormSq48 : Unit → IO Int := fun _ => do
  return runNativeFirstShortVectorNormSq (← getCachedInput qaryInput48Ref (fun _ => prepQaryInput 48))

def runIsabelleQaryNormSq48 : Unit → IO Int := fun _ => do
  runIsabelleShortVectorNormSq "qary-48" (← getCachedInput qaryInput48Ref (fun _ => prepQaryInput 48))

def runIsabelleCertifiedQaryNormSq48 : Unit → IO Int := fun _ => do
  runIsabelleCertifiedShortVectorNormSq "qary-48" (← getCachedInput qaryInput48Ref (fun _ => prepQaryInput 48))

def runFpLLLFirstShortVectorQary48Checksum : Unit → IO Int := fun _ => do
  runFpLLLFirstShortVectorChecksum (← getCachedInput qaryInput48Ref (fun _ => prepQaryInput 48))

def runCertifiedFirstShortVectorQary48Checksum : Unit → IO Int := fun _ => do
  runCertifiedFirstShortVectorChecksum (← getCachedInput qaryInput48Ref (fun _ => prepQaryInput 48))

setup_fixed_benchmark runFirstShortVectorQaryNormSq48 where {
    repeats := 3
    minTotalSeconds := 1.0
    maxSecondsPerCall := 90.0
    warmupFirstIter := true
  }

setup_fixed_benchmark runNativeFirstShortVectorQaryNormSq48 where {
    repeats := 3
    minTotalSeconds := 1.0
    maxSecondsPerCall := 90.0
    warmupFirstIter := true
  }

setup_fixed_benchmark runIsabelleQaryNormSq48 where {
    repeats := 3
    minTotalSeconds := 1.0
    maxSecondsPerCall := 90.0
    warmupFirstIter := true
  }

setup_fixed_benchmark runIsabelleCertifiedQaryNormSq48 where {
    repeats := 3
    minTotalSeconds := 1.0
    maxSecondsPerCall := 90.0
    warmupFirstIter := true
  }

setup_fixed_benchmark runFpLLLFirstShortVectorQary48Checksum where {
    repeats := 5
    minTotalSeconds := 1.0
    maxSecondsPerCall := 30.0
    warmupFirstIter := true
  }

setup_fixed_benchmark runCertifiedFirstShortVectorQary48Checksum where {
    repeats := 3
    minTotalSeconds := 1.0
    maxSecondsPerCall := 30.0
    warmupFirstIter := true
  }

-- END Qary family targets

-- BEGIN Ntru family targets (generated)
/-! ## ntru `lll.firstShortVector` targets. -/

initialize ntruInput8Ref : IO.Ref (Option FirstShortVectorInput) ← IO.mkRef none

def runFirstShortVectorNtruNormSq8 : Unit → IO Int := fun _ => do
  return runFirstShortVectorNormSq (← getCachedInput ntruInput8Ref (fun _ => prepNtruInput 8))

def runNativeFirstShortVectorNtruNormSq8 : Unit → IO Int := fun _ => do
  return runNativeFirstShortVectorNormSq (← getCachedInput ntruInput8Ref (fun _ => prepNtruInput 8))

def runIsabelleNtruNormSq8 : Unit → IO Int := fun _ => do
  runIsabelleShortVectorNormSq "ntru-8" (← getCachedInput ntruInput8Ref (fun _ => prepNtruInput 8))

def runIsabelleCertifiedNtruNormSq8 : Unit → IO Int := fun _ => do
  runIsabelleCertifiedShortVectorNormSq "ntru-8" (← getCachedInput ntruInput8Ref (fun _ => prepNtruInput 8))

def runFpLLLFirstShortVectorNtru8Checksum : Unit → IO Int := fun _ => do
  runFpLLLFirstShortVectorChecksum (← getCachedInput ntruInput8Ref (fun _ => prepNtruInput 8))

def runCertifiedFirstShortVectorNtru8Checksum : Unit → IO Int := fun _ => do
  runCertifiedFirstShortVectorChecksum (← getCachedInput ntruInput8Ref (fun _ => prepNtruInput 8))

setup_fixed_benchmark runFirstShortVectorNtruNormSq8 where {
    repeats := 3
    minTotalSeconds := 1.0
    maxSecondsPerCall := 90.0
    warmupFirstIter := true
  }

setup_fixed_benchmark runNativeFirstShortVectorNtruNormSq8 where {
    repeats := 3
    minTotalSeconds := 1.0
    maxSecondsPerCall := 90.0
    warmupFirstIter := true
  }

setup_fixed_benchmark runIsabelleNtruNormSq8 where {
    repeats := 3
    minTotalSeconds := 1.0
    maxSecondsPerCall := 90.0
    warmupFirstIter := true
  }

setup_fixed_benchmark runIsabelleCertifiedNtruNormSq8 where {
    repeats := 3
    minTotalSeconds := 1.0
    maxSecondsPerCall := 90.0
    warmupFirstIter := true
  }

setup_fixed_benchmark runFpLLLFirstShortVectorNtru8Checksum where {
    repeats := 5
    minTotalSeconds := 1.0
    maxSecondsPerCall := 30.0
    warmupFirstIter := true
  }

setup_fixed_benchmark runCertifiedFirstShortVectorNtru8Checksum where {
    repeats := 3
    minTotalSeconds := 1.0
    maxSecondsPerCall := 30.0
    warmupFirstIter := true
  }

initialize ntruInput12Ref : IO.Ref (Option FirstShortVectorInput) ← IO.mkRef none

def runFirstShortVectorNtruNormSq12 : Unit → IO Int := fun _ => do
  return runFirstShortVectorNormSq (← getCachedInput ntruInput12Ref (fun _ => prepNtruInput 12))

def runNativeFirstShortVectorNtruNormSq12 : Unit → IO Int := fun _ => do
  return runNativeFirstShortVectorNormSq (← getCachedInput ntruInput12Ref (fun _ => prepNtruInput 12))

def runIsabelleNtruNormSq12 : Unit → IO Int := fun _ => do
  runIsabelleShortVectorNormSq "ntru-12" (← getCachedInput ntruInput12Ref (fun _ => prepNtruInput 12))

def runIsabelleCertifiedNtruNormSq12 : Unit → IO Int := fun _ => do
  runIsabelleCertifiedShortVectorNormSq "ntru-12" (← getCachedInput ntruInput12Ref (fun _ => prepNtruInput 12))

def runFpLLLFirstShortVectorNtru12Checksum : Unit → IO Int := fun _ => do
  runFpLLLFirstShortVectorChecksum (← getCachedInput ntruInput12Ref (fun _ => prepNtruInput 12))

def runCertifiedFirstShortVectorNtru12Checksum : Unit → IO Int := fun _ => do
  runCertifiedFirstShortVectorChecksum (← getCachedInput ntruInput12Ref (fun _ => prepNtruInput 12))

setup_fixed_benchmark runFirstShortVectorNtruNormSq12 where {
    repeats := 3
    minTotalSeconds := 1.0
    maxSecondsPerCall := 90.0
    warmupFirstIter := true
  }

setup_fixed_benchmark runNativeFirstShortVectorNtruNormSq12 where {
    repeats := 3
    minTotalSeconds := 1.0
    maxSecondsPerCall := 90.0
    warmupFirstIter := true
  }

setup_fixed_benchmark runIsabelleNtruNormSq12 where {
    repeats := 3
    minTotalSeconds := 1.0
    maxSecondsPerCall := 90.0
    warmupFirstIter := true
  }

setup_fixed_benchmark runIsabelleCertifiedNtruNormSq12 where {
    repeats := 3
    minTotalSeconds := 1.0
    maxSecondsPerCall := 90.0
    warmupFirstIter := true
  }

setup_fixed_benchmark runFpLLLFirstShortVectorNtru12Checksum where {
    repeats := 5
    minTotalSeconds := 1.0
    maxSecondsPerCall := 30.0
    warmupFirstIter := true
  }

setup_fixed_benchmark runCertifiedFirstShortVectorNtru12Checksum where {
    repeats := 3
    minTotalSeconds := 1.0
    maxSecondsPerCall := 30.0
    warmupFirstIter := true
  }

initialize ntruInput16Ref : IO.Ref (Option FirstShortVectorInput) ← IO.mkRef none

def runFirstShortVectorNtruNormSq16 : Unit → IO Int := fun _ => do
  return runFirstShortVectorNormSq (← getCachedInput ntruInput16Ref (fun _ => prepNtruInput 16))

def runNativeFirstShortVectorNtruNormSq16 : Unit → IO Int := fun _ => do
  return runNativeFirstShortVectorNormSq (← getCachedInput ntruInput16Ref (fun _ => prepNtruInput 16))

def runIsabelleNtruNormSq16 : Unit → IO Int := fun _ => do
  runIsabelleShortVectorNormSq "ntru-16" (← getCachedInput ntruInput16Ref (fun _ => prepNtruInput 16))

def runIsabelleCertifiedNtruNormSq16 : Unit → IO Int := fun _ => do
  runIsabelleCertifiedShortVectorNormSq "ntru-16" (← getCachedInput ntruInput16Ref (fun _ => prepNtruInput 16))

def runFpLLLFirstShortVectorNtru16Checksum : Unit → IO Int := fun _ => do
  runFpLLLFirstShortVectorChecksum (← getCachedInput ntruInput16Ref (fun _ => prepNtruInput 16))

def runCertifiedFirstShortVectorNtru16Checksum : Unit → IO Int := fun _ => do
  runCertifiedFirstShortVectorChecksum (← getCachedInput ntruInput16Ref (fun _ => prepNtruInput 16))

setup_fixed_benchmark runFirstShortVectorNtruNormSq16 where {
    repeats := 3
    minTotalSeconds := 1.0
    maxSecondsPerCall := 90.0
    warmupFirstIter := true
  }

setup_fixed_benchmark runNativeFirstShortVectorNtruNormSq16 where {
    repeats := 3
    minTotalSeconds := 1.0
    maxSecondsPerCall := 90.0
    warmupFirstIter := true
  }

setup_fixed_benchmark runIsabelleNtruNormSq16 where {
    repeats := 3
    minTotalSeconds := 1.0
    maxSecondsPerCall := 90.0
    warmupFirstIter := true
  }

setup_fixed_benchmark runIsabelleCertifiedNtruNormSq16 where {
    repeats := 3
    minTotalSeconds := 1.0
    maxSecondsPerCall := 90.0
    warmupFirstIter := true
  }

setup_fixed_benchmark runFpLLLFirstShortVectorNtru16Checksum where {
    repeats := 5
    minTotalSeconds := 1.0
    maxSecondsPerCall := 30.0
    warmupFirstIter := true
  }

setup_fixed_benchmark runCertifiedFirstShortVectorNtru16Checksum where {
    repeats := 3
    minTotalSeconds := 1.0
    maxSecondsPerCall := 30.0
    warmupFirstIter := true
  }

initialize ntruInput20Ref : IO.Ref (Option FirstShortVectorInput) ← IO.mkRef none

def runFirstShortVectorNtruNormSq20 : Unit → IO Int := fun _ => do
  return runFirstShortVectorNormSq (← getCachedInput ntruInput20Ref (fun _ => prepNtruInput 20))

def runNativeFirstShortVectorNtruNormSq20 : Unit → IO Int := fun _ => do
  return runNativeFirstShortVectorNormSq (← getCachedInput ntruInput20Ref (fun _ => prepNtruInput 20))

def runIsabelleNtruNormSq20 : Unit → IO Int := fun _ => do
  runIsabelleShortVectorNormSq "ntru-20" (← getCachedInput ntruInput20Ref (fun _ => prepNtruInput 20))

def runIsabelleCertifiedNtruNormSq20 : Unit → IO Int := fun _ => do
  runIsabelleCertifiedShortVectorNormSq "ntru-20" (← getCachedInput ntruInput20Ref (fun _ => prepNtruInput 20))

def runFpLLLFirstShortVectorNtru20Checksum : Unit → IO Int := fun _ => do
  runFpLLLFirstShortVectorChecksum (← getCachedInput ntruInput20Ref (fun _ => prepNtruInput 20))

def runCertifiedFirstShortVectorNtru20Checksum : Unit → IO Int := fun _ => do
  runCertifiedFirstShortVectorChecksum (← getCachedInput ntruInput20Ref (fun _ => prepNtruInput 20))

setup_fixed_benchmark runFirstShortVectorNtruNormSq20 where {
    repeats := 3
    minTotalSeconds := 1.0
    maxSecondsPerCall := 90.0
    warmupFirstIter := true
  }

setup_fixed_benchmark runNativeFirstShortVectorNtruNormSq20 where {
    repeats := 3
    minTotalSeconds := 1.0
    maxSecondsPerCall := 90.0
    warmupFirstIter := true
  }

setup_fixed_benchmark runIsabelleNtruNormSq20 where {
    repeats := 3
    minTotalSeconds := 1.0
    maxSecondsPerCall := 90.0
    warmupFirstIter := true
  }

setup_fixed_benchmark runIsabelleCertifiedNtruNormSq20 where {
    repeats := 3
    minTotalSeconds := 1.0
    maxSecondsPerCall := 90.0
    warmupFirstIter := true
  }

setup_fixed_benchmark runFpLLLFirstShortVectorNtru20Checksum where {
    repeats := 5
    minTotalSeconds := 1.0
    maxSecondsPerCall := 30.0
    warmupFirstIter := true
  }

setup_fixed_benchmark runCertifiedFirstShortVectorNtru20Checksum where {
    repeats := 3
    minTotalSeconds := 1.0
    maxSecondsPerCall := 30.0
    warmupFirstIter := true
  }

initialize ntruInput24Ref : IO.Ref (Option FirstShortVectorInput) ← IO.mkRef none

def runFirstShortVectorNtruNormSq24 : Unit → IO Int := fun _ => do
  return runFirstShortVectorNormSq (← getCachedInput ntruInput24Ref (fun _ => prepNtruInput 24))

def runNativeFirstShortVectorNtruNormSq24 : Unit → IO Int := fun _ => do
  return runNativeFirstShortVectorNormSq (← getCachedInput ntruInput24Ref (fun _ => prepNtruInput 24))

def runIsabelleNtruNormSq24 : Unit → IO Int := fun _ => do
  runIsabelleShortVectorNormSq "ntru-24" (← getCachedInput ntruInput24Ref (fun _ => prepNtruInput 24))

def runIsabelleCertifiedNtruNormSq24 : Unit → IO Int := fun _ => do
  runIsabelleCertifiedShortVectorNormSq "ntru-24" (← getCachedInput ntruInput24Ref (fun _ => prepNtruInput 24))

def runFpLLLFirstShortVectorNtru24Checksum : Unit → IO Int := fun _ => do
  runFpLLLFirstShortVectorChecksum (← getCachedInput ntruInput24Ref (fun _ => prepNtruInput 24))

def runCertifiedFirstShortVectorNtru24Checksum : Unit → IO Int := fun _ => do
  runCertifiedFirstShortVectorChecksum (← getCachedInput ntruInput24Ref (fun _ => prepNtruInput 24))

setup_fixed_benchmark runFirstShortVectorNtruNormSq24 where {
    repeats := 3
    minTotalSeconds := 1.0
    maxSecondsPerCall := 90.0
    warmupFirstIter := true
  }

setup_fixed_benchmark runNativeFirstShortVectorNtruNormSq24 where {
    repeats := 3
    minTotalSeconds := 1.0
    maxSecondsPerCall := 90.0
    warmupFirstIter := true
  }

setup_fixed_benchmark runIsabelleNtruNormSq24 where {
    repeats := 3
    minTotalSeconds := 1.0
    maxSecondsPerCall := 90.0
    warmupFirstIter := true
  }

setup_fixed_benchmark runIsabelleCertifiedNtruNormSq24 where {
    repeats := 3
    minTotalSeconds := 1.0
    maxSecondsPerCall := 90.0
    warmupFirstIter := true
  }

setup_fixed_benchmark runFpLLLFirstShortVectorNtru24Checksum where {
    repeats := 5
    minTotalSeconds := 1.0
    maxSecondsPerCall := 30.0
    warmupFirstIter := true
  }

setup_fixed_benchmark runCertifiedFirstShortVectorNtru24Checksum where {
    repeats := 3
    minTotalSeconds := 1.0
    maxSecondsPerCall := 30.0
    warmupFirstIter := true
  }

-- END Ntru family targets

-- BEGIN Knapsack family targets (generated)
/-! ## knapsack `lll.firstShortVector` targets. -/

initialize knapsackInput16Ref : IO.Ref (Option FirstShortVectorInput) ← IO.mkRef none

def runFirstShortVectorKnapsackNormSq16 : Unit → IO Int := fun _ => do
  return runFirstShortVectorNormSq (← getCachedInput knapsackInput16Ref (fun _ => prepKnapsackInput 16))

def runNativeFirstShortVectorKnapsackNormSq16 : Unit → IO Int := fun _ => do
  return runNativeFirstShortVectorNormSq (← getCachedInput knapsackInput16Ref (fun _ => prepKnapsackInput 16))

def runIsabelleKnapsackNormSq16 : Unit → IO Int := fun _ => do
  runIsabelleShortVectorNormSq "knapsack-16" (← getCachedInput knapsackInput16Ref (fun _ => prepKnapsackInput 16))

def runIsabelleCertifiedKnapsackNormSq16 : Unit → IO Int := fun _ => do
  runIsabelleCertifiedShortVectorNormSq "knapsack-16" (← getCachedInput knapsackInput16Ref (fun _ => prepKnapsackInput 16))

def runFpLLLFirstShortVectorKnapsack16Checksum : Unit → IO Int := fun _ => do
  runFpLLLFirstShortVectorChecksum (← getCachedInput knapsackInput16Ref (fun _ => prepKnapsackInput 16))

def runCertifiedFirstShortVectorKnapsack16Checksum : Unit → IO Int := fun _ => do
  runCertifiedFirstShortVectorChecksum (← getCachedInput knapsackInput16Ref (fun _ => prepKnapsackInput 16))

setup_fixed_benchmark runFirstShortVectorKnapsackNormSq16 where {
    repeats := 3
    minTotalSeconds := 1.0
    maxSecondsPerCall := 90.0
    warmupFirstIter := true
  }

setup_fixed_benchmark runNativeFirstShortVectorKnapsackNormSq16 where {
    repeats := 3
    minTotalSeconds := 1.0
    maxSecondsPerCall := 90.0
    warmupFirstIter := true
  }

setup_fixed_benchmark runIsabelleKnapsackNormSq16 where {
    repeats := 3
    minTotalSeconds := 1.0
    maxSecondsPerCall := 90.0
    warmupFirstIter := true
  }

setup_fixed_benchmark runIsabelleCertifiedKnapsackNormSq16 where {
    repeats := 3
    minTotalSeconds := 1.0
    maxSecondsPerCall := 90.0
    warmupFirstIter := true
  }

setup_fixed_benchmark runFpLLLFirstShortVectorKnapsack16Checksum where {
    repeats := 5
    minTotalSeconds := 1.0
    maxSecondsPerCall := 30.0
    warmupFirstIter := true
  }

setup_fixed_benchmark runCertifiedFirstShortVectorKnapsack16Checksum where {
    repeats := 3
    minTotalSeconds := 1.0
    maxSecondsPerCall := 30.0
    warmupFirstIter := true
  }

initialize knapsackInput24Ref : IO.Ref (Option FirstShortVectorInput) ← IO.mkRef none

def runFirstShortVectorKnapsackNormSq24 : Unit → IO Int := fun _ => do
  return runFirstShortVectorNormSq (← getCachedInput knapsackInput24Ref (fun _ => prepKnapsackInput 24))

def runNativeFirstShortVectorKnapsackNormSq24 : Unit → IO Int := fun _ => do
  return runNativeFirstShortVectorNormSq (← getCachedInput knapsackInput24Ref (fun _ => prepKnapsackInput 24))

def runIsabelleKnapsackNormSq24 : Unit → IO Int := fun _ => do
  runIsabelleShortVectorNormSq "knapsack-24" (← getCachedInput knapsackInput24Ref (fun _ => prepKnapsackInput 24))

def runIsabelleCertifiedKnapsackNormSq24 : Unit → IO Int := fun _ => do
  runIsabelleCertifiedShortVectorNormSq "knapsack-24" (← getCachedInput knapsackInput24Ref (fun _ => prepKnapsackInput 24))

def runFpLLLFirstShortVectorKnapsack24Checksum : Unit → IO Int := fun _ => do
  runFpLLLFirstShortVectorChecksum (← getCachedInput knapsackInput24Ref (fun _ => prepKnapsackInput 24))

def runCertifiedFirstShortVectorKnapsack24Checksum : Unit → IO Int := fun _ => do
  runCertifiedFirstShortVectorChecksum (← getCachedInput knapsackInput24Ref (fun _ => prepKnapsackInput 24))

setup_fixed_benchmark runFirstShortVectorKnapsackNormSq24 where {
    repeats := 3
    minTotalSeconds := 1.0
    maxSecondsPerCall := 90.0
    warmupFirstIter := true
  }

setup_fixed_benchmark runNativeFirstShortVectorKnapsackNormSq24 where {
    repeats := 3
    minTotalSeconds := 1.0
    maxSecondsPerCall := 90.0
    warmupFirstIter := true
  }

setup_fixed_benchmark runIsabelleKnapsackNormSq24 where {
    repeats := 3
    minTotalSeconds := 1.0
    maxSecondsPerCall := 90.0
    warmupFirstIter := true
  }

setup_fixed_benchmark runIsabelleCertifiedKnapsackNormSq24 where {
    repeats := 3
    minTotalSeconds := 1.0
    maxSecondsPerCall := 90.0
    warmupFirstIter := true
  }

setup_fixed_benchmark runFpLLLFirstShortVectorKnapsack24Checksum where {
    repeats := 5
    minTotalSeconds := 1.0
    maxSecondsPerCall := 30.0
    warmupFirstIter := true
  }

setup_fixed_benchmark runCertifiedFirstShortVectorKnapsack24Checksum where {
    repeats := 3
    minTotalSeconds := 1.0
    maxSecondsPerCall := 30.0
    warmupFirstIter := true
  }

initialize knapsackInput32Ref : IO.Ref (Option FirstShortVectorInput) ← IO.mkRef none

def runFirstShortVectorKnapsackNormSq32 : Unit → IO Int := fun _ => do
  return runFirstShortVectorNormSq (← getCachedInput knapsackInput32Ref (fun _ => prepKnapsackInput 32))

def runNativeFirstShortVectorKnapsackNormSq32 : Unit → IO Int := fun _ => do
  return runNativeFirstShortVectorNormSq (← getCachedInput knapsackInput32Ref (fun _ => prepKnapsackInput 32))

def runIsabelleKnapsackNormSq32 : Unit → IO Int := fun _ => do
  runIsabelleShortVectorNormSq "knapsack-32" (← getCachedInput knapsackInput32Ref (fun _ => prepKnapsackInput 32))

def runIsabelleCertifiedKnapsackNormSq32 : Unit → IO Int := fun _ => do
  runIsabelleCertifiedShortVectorNormSq "knapsack-32" (← getCachedInput knapsackInput32Ref (fun _ => prepKnapsackInput 32))

def runFpLLLFirstShortVectorKnapsack32Checksum : Unit → IO Int := fun _ => do
  runFpLLLFirstShortVectorChecksum (← getCachedInput knapsackInput32Ref (fun _ => prepKnapsackInput 32))

def runCertifiedFirstShortVectorKnapsack32Checksum : Unit → IO Int := fun _ => do
  runCertifiedFirstShortVectorChecksum (← getCachedInput knapsackInput32Ref (fun _ => prepKnapsackInput 32))

setup_fixed_benchmark runFirstShortVectorKnapsackNormSq32 where {
    repeats := 3
    minTotalSeconds := 1.0
    maxSecondsPerCall := 90.0
    warmupFirstIter := true
  }

setup_fixed_benchmark runNativeFirstShortVectorKnapsackNormSq32 where {
    repeats := 3
    minTotalSeconds := 1.0
    maxSecondsPerCall := 90.0
    warmupFirstIter := true
  }

setup_fixed_benchmark runIsabelleKnapsackNormSq32 where {
    repeats := 3
    minTotalSeconds := 1.0
    maxSecondsPerCall := 90.0
    warmupFirstIter := true
  }

setup_fixed_benchmark runIsabelleCertifiedKnapsackNormSq32 where {
    repeats := 3
    minTotalSeconds := 1.0
    maxSecondsPerCall := 90.0
    warmupFirstIter := true
  }

setup_fixed_benchmark runFpLLLFirstShortVectorKnapsack32Checksum where {
    repeats := 5
    minTotalSeconds := 1.0
    maxSecondsPerCall := 30.0
    warmupFirstIter := true
  }

setup_fixed_benchmark runCertifiedFirstShortVectorKnapsack32Checksum where {
    repeats := 3
    minTotalSeconds := 1.0
    maxSecondsPerCall := 30.0
    warmupFirstIter := true
  }

initialize knapsackInput40Ref : IO.Ref (Option FirstShortVectorInput) ← IO.mkRef none

def runFirstShortVectorKnapsackNormSq40 : Unit → IO Int := fun _ => do
  return runFirstShortVectorNormSq (← getCachedInput knapsackInput40Ref (fun _ => prepKnapsackInput 40))

def runNativeFirstShortVectorKnapsackNormSq40 : Unit → IO Int := fun _ => do
  return runNativeFirstShortVectorNormSq (← getCachedInput knapsackInput40Ref (fun _ => prepKnapsackInput 40))

def runIsabelleKnapsackNormSq40 : Unit → IO Int := fun _ => do
  runIsabelleShortVectorNormSq "knapsack-40" (← getCachedInput knapsackInput40Ref (fun _ => prepKnapsackInput 40))

def runIsabelleCertifiedKnapsackNormSq40 : Unit → IO Int := fun _ => do
  runIsabelleCertifiedShortVectorNormSq "knapsack-40" (← getCachedInput knapsackInput40Ref (fun _ => prepKnapsackInput 40))

def runFpLLLFirstShortVectorKnapsack40Checksum : Unit → IO Int := fun _ => do
  runFpLLLFirstShortVectorChecksum (← getCachedInput knapsackInput40Ref (fun _ => prepKnapsackInput 40))

def runCertifiedFirstShortVectorKnapsack40Checksum : Unit → IO Int := fun _ => do
  runCertifiedFirstShortVectorChecksum (← getCachedInput knapsackInput40Ref (fun _ => prepKnapsackInput 40))

setup_fixed_benchmark runFirstShortVectorKnapsackNormSq40 where {
    repeats := 3
    minTotalSeconds := 1.0
    maxSecondsPerCall := 90.0
    warmupFirstIter := true
  }

setup_fixed_benchmark runNativeFirstShortVectorKnapsackNormSq40 where {
    repeats := 3
    minTotalSeconds := 1.0
    maxSecondsPerCall := 90.0
    warmupFirstIter := true
  }

setup_fixed_benchmark runIsabelleKnapsackNormSq40 where {
    repeats := 3
    minTotalSeconds := 1.0
    maxSecondsPerCall := 90.0
    warmupFirstIter := true
  }

setup_fixed_benchmark runIsabelleCertifiedKnapsackNormSq40 where {
    repeats := 3
    minTotalSeconds := 1.0
    maxSecondsPerCall := 90.0
    warmupFirstIter := true
  }

setup_fixed_benchmark runFpLLLFirstShortVectorKnapsack40Checksum where {
    repeats := 5
    minTotalSeconds := 1.0
    maxSecondsPerCall := 30.0
    warmupFirstIter := true
  }

setup_fixed_benchmark runCertifiedFirstShortVectorKnapsack40Checksum where {
    repeats := 3
    minTotalSeconds := 1.0
    maxSecondsPerCall := 30.0
    warmupFirstIter := true
  }

initialize knapsackInput48Ref : IO.Ref (Option FirstShortVectorInput) ← IO.mkRef none

def runFirstShortVectorKnapsackNormSq48 : Unit → IO Int := fun _ => do
  return runFirstShortVectorNormSq (← getCachedInput knapsackInput48Ref (fun _ => prepKnapsackInput 48))

def runNativeFirstShortVectorKnapsackNormSq48 : Unit → IO Int := fun _ => do
  return runNativeFirstShortVectorNormSq (← getCachedInput knapsackInput48Ref (fun _ => prepKnapsackInput 48))

def runIsabelleKnapsackNormSq48 : Unit → IO Int := fun _ => do
  runIsabelleShortVectorNormSq "knapsack-48" (← getCachedInput knapsackInput48Ref (fun _ => prepKnapsackInput 48))

def runIsabelleCertifiedKnapsackNormSq48 : Unit → IO Int := fun _ => do
  runIsabelleCertifiedShortVectorNormSq "knapsack-48" (← getCachedInput knapsackInput48Ref (fun _ => prepKnapsackInput 48))

def runFpLLLFirstShortVectorKnapsack48Checksum : Unit → IO Int := fun _ => do
  runFpLLLFirstShortVectorChecksum (← getCachedInput knapsackInput48Ref (fun _ => prepKnapsackInput 48))

def runCertifiedFirstShortVectorKnapsack48Checksum : Unit → IO Int := fun _ => do
  runCertifiedFirstShortVectorChecksum (← getCachedInput knapsackInput48Ref (fun _ => prepKnapsackInput 48))

setup_fixed_benchmark runFirstShortVectorKnapsackNormSq48 where {
    repeats := 3
    minTotalSeconds := 1.0
    maxSecondsPerCall := 90.0
    warmupFirstIter := true
  }

setup_fixed_benchmark runNativeFirstShortVectorKnapsackNormSq48 where {
    repeats := 3
    minTotalSeconds := 1.0
    maxSecondsPerCall := 90.0
    warmupFirstIter := true
  }

setup_fixed_benchmark runIsabelleKnapsackNormSq48 where {
    repeats := 3
    minTotalSeconds := 1.0
    maxSecondsPerCall := 90.0
    warmupFirstIter := true
  }

setup_fixed_benchmark runIsabelleCertifiedKnapsackNormSq48 where {
    repeats := 3
    minTotalSeconds := 1.0
    maxSecondsPerCall := 90.0
    warmupFirstIter := true
  }

setup_fixed_benchmark runFpLLLFirstShortVectorKnapsack48Checksum where {
    repeats := 5
    minTotalSeconds := 1.0
    maxSecondsPerCall := 30.0
    warmupFirstIter := true
  }

setup_fixed_benchmark runCertifiedFirstShortVectorKnapsack48Checksum where {
    repeats := 3
    minTotalSeconds := 1.0
    maxSecondsPerCall := 30.0
    warmupFirstIter := true
  }

-- END Knapsack family targets

end Hex.LLLBench
