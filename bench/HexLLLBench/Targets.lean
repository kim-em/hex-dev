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

/-- Fallback-rate diagnostic for the steered native reducer: run
`firstShortVectorUnchecked` (i.e. `lllSteered`) once on every rung of both
ladders, then read `Hex.steeredTally`. Fails if any steered candidate failed
certification and fell back to the exact reducer (`fellBack ≠ 0`) — a fallback
inside the ladder would make the steered medians dishonest. Only rungs the
`Hex.steerWins` predictor routes to steering (n ≥ 30) bump the tally; the
smaller rungs run `lllNative` directly. The returned value encodes the tally
as `certified · 65537 + fellBack`. -/
def runSteeredFallbackTally : Unit → IO Int := fun _ => do
  Hex.resetSteeredTally
  let targets : List (Unit → IO Int) :=
    [runFirstShortVectorRandomBoundedNormSq30,
     runFirstShortVectorRandomBoundedNormSq45,
     runFirstShortVectorRandomBoundedNormSq60,
     runFirstShortVectorRandomBoundedNormSq75,
     runFirstShortVectorRandomBoundedNormSq90,
     runFirstShortVectorRandomBoundedNormSq120,
     runFirstShortVectorRandomBoundedNormSq150,
     runFirstShortVectorRandomBoundedNormSq180,
     runFirstShortVectorHarshCubicNormSq15,
     runFirstShortVectorHarshCubicNormSq20,
     runFirstShortVectorHarshCubicNormSq25,
     runFirstShortVectorHarshCubicNormSq30,
     runFirstShortVectorHarshCubicNormSq35,
     runFirstShortVectorHarshCubicNormSq40,
     runFirstShortVectorHarshCubicNormSq45,
     runFirstShortVectorHarshCubicNormSq50,
     runFirstShortVectorHarshCubicNormSq55,
     runFirstShortVectorHarshCubicNormSq60,
     runFirstShortVectorHarshCubicNormSq65]
  for t in targets do
    discard <| t ()
  let tally ← Hex.steeredTally
  if tally.fellBack != 0 then
    throw <| IO.userError
      s!"steered reducer fell back to the exact reducer on a bench rung: {repr tally}"
  return Int.ofNat tally.certified * 65537 + Int.ofNat tally.fellBack

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

/- Fallback-rate diagnostic: the steered reducer certified on every steered rung
of both ladders (`fellBack = 0`). The pinned hash records the `certified` count
(16 = the rungs `Hex.steerWins` routes to steering under the unified `n ≥ 30`
floor: harsh-cubic n ≥ 30 — 8 rungs — and random-bounded n ≥ 30 — 8 rungs,
n=30 now included after the `(δ + 3)/4` steering-margin fix); a fallback would
flip `fellBack` nonzero and throw before the hash is reached. -/
setup_fixed_benchmark runSteeredFallbackTally where {
    repeats := 1
    maxSecondsPerCall := 120.0
    expectedHash := some (Hashable.hash ((16 * 65537 : Int)))
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

end Hex.LLLBench
