/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import HexPrimalityBench.Inputs
import HexPrimality.PMinusOneFixtures
import HexPrimality.PMinusOneMeasure
import HexPrimality.PMinusOneParents
import LeanBench

/-!
Complete compiled Phase-4 evidence for `HexPrimality`.

The certificate families use the committed 31/61/123/256/511-bit
table-smooth ladder. The structurally different 512-bit policy boundary,
where search must discover the above-table factor `100297` with rho, is a
canonical fixed case. Other controlled ladders cover the runtime sieve and
table, Miller--Rabin, multiplicative order, Pollard p-1, Brent rho, bounded
and total decisions, checker replay, prime segments, and next-prime search.
Every randomized route uses the seed stored beside its hard input.
-/

namespace Hex.PrimalityBench

open Hex.Nat

/-- Run one Miller--Rabin base on the committed prime ladder. -/
def runMillerRabin (input : Input) : Nat :=
  if millerRabin input.n 2 then 1 else 0

/-- Run the complete fixed probable-prime base list. -/
def runProbablePrime (input : Input) : Nat :=
  if isProbablePrime input.n then 1 else 0

/-- Run the bounded decision end to end. -/
def runDecision (input : Input) : Nat :=
  match isPrime? input.n (Hex.Rand.ofSeed input.n) (defaultPrimeFuel input.n) with
  | .ok (true, _) => 1
  | .ok (false, _) => 0
  | .error _ => 2

/-- Run the total convenience decision, including its exact fallback route. -/
def runTotalDecision (input : Input) : Nat :=
  if isPrime input.n then 1 else 0

/-- Run certificate search alone, forcing the result tree shallowly. -/
def runCertSearch (input : Input) : Nat :=
  match primeCert? input.n (Hex.Rand.ofSeed input.n) (defaultPrimeFuel input.n) with
  | .ok (c, _) => c.raw.subject % 4294967296
  | .error f => f.attempts

/-- Replay the checker on the prepared certificate: the compiled twin of
the kernel obligation. -/
def runChecker (input : Input) : Nat :=
  if checkPrime input.cert then 1 else 0

/-- Generate and decode the residue-compressed runtime sieve below `bound`. -/
def runSieve (bound : Nat) : Nat :=
  (bitsToList (sieve bound (Nat.sqrt bound + 1)) bound).length

/-- Exercise `count` binary searches against the fixed complete table. -/
def runTableLookup (count : Nat) : Nat := Id.run do
  let mut checksum := 0
  for i in [0:count] do
    if isTablePrime ((i * 7919 + 17) % primeTableBound) then
      checksum := checksum + 1
  return checksum

/-- One modulus/base pair whose base is a primitive root. -/
structure OrderInput where
  modulus : Nat
  base : Nat

instance : Hashable OrderInput where
  hash input := hash input.modulus

instance : Inhabited OrderInput := ⟨⟨1009, 11⟩⟩

/-- Fixed primitive-root ladder; each order is exactly `modulus - 1`. -/
def prepOrder (modulus : Nat) : OrderInput :=
  match modulus with
  | 1009 => ⟨1009, 11⟩
  | 2003 => ⟨2003, 5⟩
  | 4001 => ⟨4001, 3⟩
  | 8009 => ⟨8009, 3⟩
  | 16001 => ⟨16001, 3⟩
  | _ => ⟨32003, 2⟩

/-- Compute multiplicative order on a full-order input. -/
def runOrder (input : OrderInput) : Nat :=
  orderOf input.base input.modulus

#guard (#[1009, 2003, 4001, 8009, 16001, 32003] : Array Nat).all fun p =>
  let input := prepOrder p
  orderOf input.base input.modulus == input.modulus - 1

/-- Run the counted p-1 boundary on a fixed 61-bit prime. A prime modulus
forces the stage to consume the whole smoothness ladder before returning. -/
def runPMinusOne (bound : Nat) : Nat :=
  let attempt := pMinusOneStage1Counted primalityInput61 2 bound
    (Hex.Rand.ofSeed 0x706d31)
  match attempt.result with
  | .noFactor => attempt.attempts
  | .factor d => d + attempt.attempts
  | .whole => attempt.attempts + 2

/-- One balanced semiprime and the fixed seed used by the rho search. -/
structure RhoInput where
  n : Nat
  seed : Nat

instance : Hashable RhoInput where
  hash input := hash input.n

instance : Inhabited RhoInput := ⟨⟨10011200327, 1⟩⟩

/-- Balanced semiprimes with least factors from 100,003 through 30,000,001. -/
def prepRho (factor : Nat) : RhoInput :=
  match factor with
  | 100003 => ⟨10011200327, 1⟩
  | 300007 => ⟨90034800763, 1⟩
  | 1000003 => ⟨1000120000351, 1⟩
  | 3000017 => ⟨9000444002227, 1⟩
  | 10000019 => ⟨100001400002299, 1⟩
  | _ => ⟨900003300000109, 1⟩

/-- Run the counted Brent-rho boundary, returning a checksum that forces the
factor and exact semantic-attempt count. -/
def runRho (input : RhoInput) : Nat :=
  match Internal.rhoFactorCounted? input.n (Hex.Rand.ofSeed input.seed) 8 with
  | .ok success => success.factor + success.attempts
  | .error failure => failure.attempts

#guard (#[100003, 300007, 1000003, 3000017, 10000019, 30000001] : Array Nat).all fun p =>
  let input := prepRho p
  match Internal.rhoFactorCounted? input.n (Hex.Rand.ofSeed input.seed) 8 with
  | .ok success => 1 < success.factor && success.factor < input.n &&
      input.n % success.factor == 0
  | .error _ => false

/-- Enumerate the primes below `n` and force the array. -/
def runSegment (n : Nat) : Nat :=
  (primesIn 0 n).size

/-- One exact prime-gap case below the committed table bound. -/
structure NextInput where
  start : Nat
  gap : Nat

instance : Hashable NextInput where
  hash input := hash input.start

instance : Inhabited NextInput := ⟨⟨7, 4⟩⟩

/-- Prime gaps of 4, 8, 16, 32, 48, and 64, all on the table route. -/
def prepNext (gap : Nat) : NextInput :=
  match gap with
  | 4 => ⟨7, 4⟩
  | 8 => ⟨89, 8⟩
  | 16 => ⟨1831, 16⟩
  | 32 => ⟨5591, 32⟩
  | 48 => ⟨28229, 48⟩
  | _ => ⟨89689, 64⟩

/-- Search across a committed exact prime gap. -/
def runNextPrime (input : NextInput) : Nat :=
  match nextPrime? input.start (Hex.Rand.ofSeed input.start) (input.gap + 1) with
  | .ok (p, _) => p - input.start
  | .error failure => failure.rejectedCandidates + failure.certAttempts

#guard (#[4, 8, 16, 32, 48, 64] : Array Nat).all fun gap =>
  runNextPrime (prepNext gap) == gap

/- A Miller--Rabin base performs `O(b)` modular squarings and one modular
exponentiation with `O(b)` multiplications on `b`-bit operands. Schoolbook
bit arithmetic therefore gives the independent `O(b³)` upper model; GMP's
subquadratic upper rungs may appear faster. -/
setup_benchmark runMillerRabin n => n * n * n
  with prep := prepInput
  where {
    paramFloor := 31
    paramCeiling := 511
    paramSchedule := .custom smoothSizeParams
    maxSecondsPerCall := 5.0
    targetInnerNanos := 100000000
    signalFloorMultiplier := 1.0
    slopeTolerance := 0.5
  }

/- `isProbablePrime` applies the fixed thirteen-base list, so it multiplies
the preceding Miller--Rabin cost by a constant and retains the `O(b³)`
schoolbook bit-cost model on this all-bases prime ladder. -/
setup_benchmark runProbablePrime n => n * n * n
  with prep := prepInput
  where {
    paramFloor := 31
    paramCeiling := 511
    paramSchedule := .custom smoothSizeParams
    maxSecondsPerCall := 5.0
    targetInnerNanos := 100000000
    signalFloorMultiplier := 1.0
    slopeTolerance := 0.5
  }

/- On the table-smooth prime ladder, bounded decision performs a fixed-base
probable-prime screen followed by certificate construction. Both use
`O(b)` modular multiplications per level on `b`-bit operands, so schoolbook
bit arithmetic gives the conservative `O(b³)` model. -/
setup_benchmark runDecision n => n * n * n
  with prep := prepInput
  where {
    paramFloor := 31
    paramCeiling := 511
    paramSchedule := .custom smoothSizeParams
    maxSecondsPerCall := 5.0
    targetInnerNanos := 100000000
    signalFloorMultiplier := 1.0
    slopeTolerance := 0.5
  }

/- The total wrapper runs the same bounded route on every successful rung and
adds only a constant projection; its family model is therefore the same
`O(b³)` schoolbook bound as `runDecision`. -/
setup_benchmark runTotalDecision n => n * n * n
  with prep := prepInput
  where {
    paramFloor := 31
    paramCeiling := 511
    paramSchedule := .custom smoothSizeParams
    maxSecondsPerCall := 5.0
    targetInnerNanos := 100000000
    signalFloorMultiplier := 1.0
    slopeTolerance := 0.5
  }

/- Certificate search on this rho-free family performs fixed-base screening,
table division, and witness exponentiation at each shrinking certificate
level. The conservative schoolbook bit-cost sum is `O(b³)`; the separate
512-bit fixed target owns the structurally different rho route. -/
setup_benchmark runCertSearch n => n * n * n
  with prep := prepInput
  where {
    paramFloor := 31
    paramCeiling := 511
    paramSchedule := .custom smoothSizeParams
    maxSecondsPerCall := 5.0
    targetInnerNanos := 100000000
    signalFloorMultiplier := 1.0
    slopeTolerance := 0.5
  }

/- One checker level performs a fixed number of modular exponentiations on
this committed family. Each uses `O(b)` schoolbook `O(b²)` multiplications,
giving the independent `O(b³)` bit-cost model. -/
setup_benchmark runChecker n => n * n * n
  with prep := prepInput
  where {
    paramFloor := 31
    paramCeiling := 511
    paramSchedule := .custom smoothSizeParams
    maxSecondsPerCall := 5.0
    targetInnerNanos := 100000000
    signalFloorMultiplier := 1.0
    slopeTolerance := 0.5
  }

/- The compressed sieve visits `Theta(√n)` candidate indices. Each marking
pass constructs and combines `n`-bit masks through a fixed 32-round doubling
scheme, so the representation-specific upper model is `O(n√n)` bit work;
decoding adds only `O(n)` bit tests. -/
setup_benchmark runSieve n => n * Nat.sqrt n
  where {
    paramFloor := 1000
    paramCeiling := 32000
    paramSchedule := .custom #[1000, 2000, 4000, 8000, 16000, 32000]
    maxSecondsPerCall := 5.0
    targetInnerNanos := 100000000
    signalFloorMultiplier := 1.0
    slopeTolerance := 0.6
  }

/- The table has fixed size 9,592, so each binary search performs a fixed
`O(log 9592)` number of comparisons. A batch of `n` independent downstream
lookups is therefore linear in `n`. -/
setup_benchmark runTableLookup n => n
  where {
    paramFloor := 4096
    paramCeiling := 65536
    paramSchedule := .custom #[4096, 8192, 16384, 32768, 65536]
    maxSecondsPerCall := 5.0
    targetInnerNanos := 100000000
    signalFloorMultiplier := 1.0
    slopeTolerance := 0.35
  }

/- Every primitive-root case has order `p - 1`, so `orderOf` performs
`Theta(p)` modular multiplications. All declared rungs are one-word moduli,
holding multiplication cost fixed and making the controlled family linear. -/
setup_benchmark runOrder n => n
  with prep := prepOrder
  where {
    paramFloor := 1009
    paramCeiling := 32003
    paramSchedule := .custom #[1009, 2003, 4001, 8009, 16001, 32003]
    maxSecondsPerCall := 5.0
    targetInnerNanos := 100000000
    signalFloorMultiplier := 1.0
    slopeTolerance := 0.4
  }

/- Stage 1 raises the fixed-base residue by the largest prime powers below
`B`. Their logarithms sum to `Theta(B)` (Chebyshev's function), while the
61-bit modulus fixes each modular-multiplication cost, so the ladder is
linear in the smoothness bound. -/
setup_benchmark runPMinusOne n => n
  where {
    paramFloor := 64
    paramCeiling := 8192
    paramSchedule := .custom #[64, 128, 256, 512, 1024, 2048, 4096, 8192]
    maxSecondsPerCall := 5.0
    targetInnerNanos := 100000000
    signalFloorMultiplier := 1.0
    slopeTolerance := 0.5
  }

/- Brent rho needs an expected `Theta(√p)` polynomial steps to expose a
least factor `p`. The balanced semiprime ladder stays within one machine
word, so modular arithmetic has fixed cost and `sqrt p` is the controlled
expected-work model for the fixed seeds. The first rung starts above Brent's
fixed-size gcd batch, avoiding a constant-overhead-only family. -/
setup_benchmark runRho n => Nat.sqrt n
  with prep := prepRho
  where {
    paramFloor := 100003
    paramCeiling := 30000001
    paramSchedule := .custom #[100003, 300007, 1000003, 3000017, 10000019, 30000001]
    maxSecondsPerCall := 5.0
    targetInnerNanos := 100000000
    signalFloorMultiplier := 1.0
    slopeTolerance := 0.8
  }

/- `primesIn` applies trial division to every candidate below `n`; one trial
decision performs `O(√n)` remainder tests, hence the `O(n√n)` operation
count on this initial-segment family. -/
setup_benchmark runSegment n => n * Nat.sqrt n
  where {
    paramFloor := 1000
    paramCeiling := 32000
    paramSchedule := .custom #[1000, 2000, 4000, 8000, 16000, 32000]
    maxSecondsPerCall := 5.0
    targetInnerNanos := 100000000
    signalFloorMultiplier := 1.0
    slopeTolerance := 0.5
  }

/- These committed gaps stay below `primeTableBound`, so each candidate is
decided by one fixed-size binary search. Searching across an exact gap of
length `n` is therefore linear in `n`. -/
setup_benchmark runNextPrime n => n
  with prep := prepNext
  where {
    paramFloor := 4
    paramCeiling := 64
    paramSchedule := .custom #[4, 8, 16, 32, 48, 64]
    maxSecondsPerCall := 5.0
    targetInnerNanos := 100000000
    signalFloorMultiplier := 1.0
    slopeTolerance := 0.4
  }

initialize policyInputRef : IO.Ref Input ← IO.mkRef (prepInput 512)

initialize pock3Ref : IO.Ref Input ←
  IO.mkRef ⟨199, .pock3 199 9 2 8 [(3, 0, .small 2), (2, 0, .small 3)]⟩

/-- Canonical bounded-decision policy boundary; an `IO.Ref` keeps the fixed
input out of compiler constant folding. -/
def runDecision512 (_ : Unit) : IO Nat := do
  return runDecision (← policyInputRef.get)

/-- Canonical rho-backed certificate-search policy boundary. -/
def runCertSearch512 (_ : Unit) : IO Nat := do
  return runCertSearch (← policyInputRef.get)

/-- Canonical compiled checker twin for the 512-bit kernel replay. -/
def runChecker512 (_ : Unit) : IO Nat := do
  return runChecker (← policyInputRef.get)

/-- Canonical cube-root Pocklington checker arm. -/
def runPock3Checker (_ : Unit) : IO Nat := do
  return if checkPrime (← pock3Ref.get).cert then 1 else 0

/- The exact 512-bit rho-backed route is a policy-boundary fixed case rather
than another rung of the table-smooth family. Its 5 s child deadline is over
100 times the current designated-host reference call. -/
setup_fixed_benchmark runDecision512 where {
  repeats := 5
  maxSecondsPerCall := 5.0
  expectedHash := some (Hashable.hash (1 : Nat))
}

/- Search at the exact 512-bit boundary has a distinct rho factorization
shape, so no honest one-parameter family exists below it. The 5 s absolute
budget is the accepted mode-3 policy ceiling. -/
setup_fixed_benchmark runCertSearch512 where {
  repeats := 5
  maxSecondsPerCall := 5.0
  expectedHash := some (Hashable.hash (primalityInput512 % 4294967296))
}

/- The prepared recursive certificate is the canonical checker input paired
with the 512-bit fresh-module replay; its 5 s budget includes ample reference
host headroom. -/
setup_fixed_benchmark runChecker512 where {
  repeats := 5
  maxSecondsPerCall := 5.0
  expectedHash := some (Hashable.hash (1 : Nat))
}

/- Pocklington-3 is a separate checker constructor but has only the canonical
199 certificate in the current public policy. This is a fixed structural
and performance anchor with a 2 s child deadline. -/
setup_fixed_benchmark runPock3Checker where {
  repeats := 5
  maxSecondsPerCall := 2.0
  expectedHash := some (Hashable.hash (1 : Nat))
}

private initialize curveRef : IO.Ref Input ← IO.mkRef {
  n := 2 ^ 255 - 19
  cert := Hex.Nat.PrimeCert.pock 57896044618658097711785492504343953926634992332820282019728792003956564819949
        [(2, 0,
            Hex.Nat.PrimeCert.pock3 74058212732561358302231226437062788676166966415465897661863160754340907
              2028478494862525422475607 22304740449229861598212 2028478494862525422475606
              [(2, 0, Hex.Nat.PrimeCert.small 2), (2, 0, Hex.Nat.PrimeCert.small 353),
                (2, 0, Hex.Nat.PrimeCert.small 57467),
                (2, 0,
                  Hex.Nat.PrimeCert.pock3 31757755568855353 4028945 289 4028944
                    [(5, 2, Hex.Nat.PrimeCert.small 2), (2, 0, Hex.Nat.PrimeCert.small 223),
                      (2, 0, Hex.Nat.PrimeCert.small 4153)])])] }

private initialize runtimeBoundRef : IO.Ref Nat ← IO.mkRef 524289

/-- Fixed mode-3 Curve25519 construction, including final compiled self-check. -/
def runConstruction (_ : Unit) : IO Nat := do
  let input ← curveRef.get
  match Construction.run input.n (Hex.Rand.ofSeed input.n) with
  | .ok s => return s.attempts
  | .error _ => return 0

/-- Fixed mode-3 compiled replay of the exact Curve25519 suggestion. -/
def runCurveChecker (_ : Unit) : IO Nat := do
  return if checkPrime (← curveRef.get).cert then 1 else 0

/-- Fixed mode-3 runtime enumeration through the construction bound. -/
def runRuntimePrimes (_ : Unit) : IO Nat := do
  return (primesBelow (← runtimeBoundRef.get)).length

-- These single structural targets do not form a scaling family. Deadlines
-- are operational limits; absolute timings describe the shared host.
setup_fixed_benchmark runConstruction where {
  repeats := 5
  maxSecondsPerCall := 5.0
  expectedHash := some (Hashable.hash (29 : Nat))
}

setup_fixed_benchmark runCurveChecker where {
  repeats := 5
  maxSecondsPerCall := 5.0
  expectedHash := some (Hashable.hash (1 : Nat))
}

setup_fixed_benchmark runRuntimePrimes where {
  repeats := 5
  maxSecondsPerCall := 5.0
  expectedHash := some (Hashable.hash (43390 : Nat))
}


namespace Stage2

/-- Enumeration and the saved residue are prepared outside the arithmetic timer. -/
structure Prepared where
  input : Input
  upper : Nat
  primes : List Nat

instance : Inhabited Prepared := ⟨⟨default, 0, []⟩⟩
instance : Hashable Prepared where
  hash p := hash (p.input.subject, p.upper)

def prepareMiss (bits q : Nat) : Prepared :=
  let q := if #[67, 127, 257, 509, 1021, 2039, 4093, 8191, 16381, 32749].contains q
    then q else 2039
  let input := (inputs.find? (fun i => i.bits == bits && i.q == q)).getD default
  ⟨input, q - 1, PMinusOne.primes 64 (q - 1)⟩

/-- Hash actual outcomes and work, including retained batch detail. The trace
walk adds O(L/32) work on this no-recovery family and cannot change its model. -/
def checksum (r : PMinusOne.Run) : Nat :=
  let value := match r.result with | .noFactor => 0 | .whole => 1 | .factor d => d
  r.events.foldl (fun acc e =>
    e.batches.foldl (fun acc b =>
      b.recovery.foldl (· + ·) (acc + b.firstPrime + b.lastPrime + b.length + b.gcd))
      (acc + e.candidates + e.giantAdvances + e.multiplications +
        e.setupGcds + e.batchGcds + e.recoveryGcds)) (3 * value + r.attempts)

def runPrepared (p : Prepared) (keepBatches : Bool) : Nat :=
  checksum (PMinusOne.fromPrepared p.input.subject p.input.x 64 p.upper p.primes
    (Hex.Rand.ofSeed 0) keepBatches)

/-- Exact multiplication count on a full miss: i₀ = floor(67/210) = 0, so
binary power costs zero. The fixed 210 babies remain in the model. -/
def operations (q : Nat) : Nat :=
  let ps := PMinusOne.primes 64 (q - 1)
  if ps.isEmpty then 0 else 210 + ps.getLast! / 210 + 2 * ps.length

#guard inputs.all fun input =>
  let p := prepareMiss input.bits input.q
  let full := PMinusOne.fromPrepared input.subject input.x 64 p.upper p.primes
    (Hex.Rand.ofSeed 0)
  let counters := PMinusOne.fromPrepared input.subject input.x 64 p.upper p.primes
    (Hex.Rand.ofSeed 0) false
  full.result == .noFactor && full.attempts == 1 && full.rand == counters.rand &&
  counters.result == full.result && counters.attempts == full.attempts &&
  full.events.map (fun e => { e with batches := [] }) == counters.events &&
  full.events[0]!.multiplications == operations input.q &&
  full.events[0]!.batchGcds == (p.primes.length + 31) / 32

namespace Bits64

def prepare (q : Nat) : Prepared := prepareMiss 64 q
def runTrace (p : Prepared) : Nat := runPrepared p true
def runCounters (p : Prepared) : Nat := runPrepared p false

-- Fixed operand-size tracks price the executed modular schedule separately
-- from the sieve. Small rungs are setup-amortization data, outside this fit.
setup_benchmark runTrace q => operations q
  with prep := prepare
  where {
    paramFloor := 2039
    paramCeiling := 32749
    paramSchedule := .custom #[2039, 4093, 8191, 16381, 32749]
    maxSecondsPerCall := 5.0
    targetInnerNanos := 100000000
    signalFloorMultiplier := 1.0
    slopeTolerance := 0.5
  }

setup_benchmark runCounters q => operations q
  with prep := prepare
  where {
    paramFloor := 2039
    paramCeiling := 32749
    paramSchedule := .custom #[2039, 4093, 8191, 16381, 32749]
    maxSecondsPerCall := 5.0
    targetInnerNanos := 100000000
    signalFloorMultiplier := 1.0
    slopeTolerance := 0.5
  }

end Bits64

namespace Bits128

def prepare (q : Nat) : Prepared := prepareMiss 128 q
def runTrace (p : Prepared) : Nat := runPrepared p true
def runCounters (p : Prepared) : Nat := runPrepared p false

-- Fixed operand-size tracks price the executed modular schedule separately
-- from the sieve. Small rungs are setup-amortization data, outside this fit.
setup_benchmark runTrace q => operations q
  with prep := prepare
  where {
    paramFloor := 2039
    paramCeiling := 32749
    paramSchedule := .custom #[2039, 4093, 8191, 16381, 32749]
    maxSecondsPerCall := 5.0
    targetInnerNanos := 100000000
    signalFloorMultiplier := 1.0
    slopeTolerance := 0.5
  }

setup_benchmark runCounters q => operations q
  with prep := prepare
  where {
    paramFloor := 2039
    paramCeiling := 32749
    paramSchedule := .custom #[2039, 4093, 8191, 16381, 32749]
    maxSecondsPerCall := 5.0
    targetInnerNanos := 100000000
    signalFloorMultiplier := 1.0
    slopeTolerance := 0.5
  }

end Bits128

namespace Bits256

def prepare (q : Nat) : Prepared := prepareMiss 256 q
def runTrace (p : Prepared) : Nat := runPrepared p true
def runCounters (p : Prepared) : Nat := runPrepared p false

-- Fixed operand-size tracks price the executed modular schedule separately
-- from the sieve. Small rungs are setup-amortization data, outside this fit.
setup_benchmark runTrace q => operations q
  with prep := prepare
  where {
    paramFloor := 2039
    paramCeiling := 32749
    paramSchedule := .custom #[2039, 4093, 8191, 16381, 32749]
    maxSecondsPerCall := 5.0
    targetInnerNanos := 100000000
    signalFloorMultiplier := 1.0
    slopeTolerance := 0.5
  }

setup_benchmark runCounters q => operations q
  with prep := prepare
  where {
    paramFloor := 2039
    paramCeiling := 32749
    paramSchedule := .custom #[2039, 4093, 8191, 16381, 32749]
    maxSecondsPerCall := 5.0
    targetInnerNanos := 100000000
    signalFloorMultiplier := 1.0
    slopeTolerance := 0.5
  }

end Bits256

namespace Bits512

def prepare (q : Nat) : Prepared := prepareMiss 512 q
def runTrace (p : Prepared) : Nat := runPrepared p true
def runCounters (p : Prepared) : Nat := runPrepared p false

-- Fixed operand-size tracks price the executed modular schedule separately
-- from the sieve. Small rungs are setup-amortization data, outside this fit.
setup_benchmark runTrace q => operations q
  with prep := prepare
  where {
    paramFloor := 2039
    paramCeiling := 32749
    paramSchedule := .custom #[2039, 4093, 8191, 16381, 32749]
    maxSecondsPerCall := 5.0
    targetInnerNanos := 100000000
    signalFloorMultiplier := 1.0
    slopeTolerance := 0.5
  }

setup_benchmark runCounters q => operations q
  with prep := prepare
  where {
    paramFloor := 2039
    paramCeiling := 32749
    paramSchedule := .custom #[2039, 4093, 8191, 16381, 32749]
    maxSecondsPerCall := 5.0
    targetInnerNanos := 100000000
    signalFloorMultiplier := 1.0
    slopeTolerance := 0.5
  }

end Bits512

/-- The existing modular-power dispatch with its word context prepared once.
Conversions remain inside each power; large moduli retain the Nat backend. -/
structure PreparedPower where
  power : Nat → Nat → Nat
  checksum : Nat
deriving Inhabited

@[noinline] def preparePower (n : Nat) : PreparedPower :=
  if n = 0 then ⟨fun _ _ => 0, 0⟩ else
    let word := UInt64.ofNat n
    if word.toNat = n then
      if odd : word % 2 = 1 then
        let ctx := MontCtx.mk word odd
        ⟨fun a e => (ctx.fromMont (HexArith.powMont ctx
          (ctx.toMont (UInt64.ofNat (a % word.toNat))) e)).toNat,
          ctx.p'.toNat + ctx.r2.toNat⟩
      else ⟨fun a e => HexArith.powModBits a e n, 0⟩
    else ⟨fun a e => HexArith.powModBits a e n, 0⟩

theorem preparePower_eq (n a e : Nat) :
    (preparePower n).power a e = HexArith.powMod a e n := by
  unfold preparePower HexArith.powMod
  split
  · rfl
  · dsimp only
    split
    · split <;> rfl
    · rfl

def preparedSmooth (power : PreparedPower) (bound : Nat) : List Nat → Nat → Nat
  | [], x => x
  | q :: qs, x =>
      if q ≤ smoothBound bound then
        preparedSmooth power bound qs (power.power x (PMinusOne.primePower q bound))
      else x

theorem preparedSmooth_eq (n bound : Nat) (ps : List Nat) (x : Nat) :
    preparedSmooth (preparePower n) bound ps x = PMinusOne.smoothPower n x bound ps := by
  induction ps generalizing x with
  | nil => rfl
  | cons q qs ih =>
    change (if q ≤ smoothBound bound then
      preparedSmooth (preparePower n) bound qs
        ((preparePower n).power x (PMinusOne.primePower q bound)) else x) =
      (if q ≤ smoothBound bound then
        PMinusOne.smoothPower n (HexArith.powModNat x (PMinusOne.primePower q bound) n)
          bound qs else x)
    split
    · rw [preparePower_eq, HexArith.powMod_eq_powModNat]
      exact ih _
    · rfl

-- Match the independently certified saved residues, including word and
-- arbitrary-precision moduli, before measuring the prepared boundary.
#guard inputs.all fun input =>
  preparedSmooth (preparePower input.subject) 64 (primesBelow 65) (2 % input.subject) == input.x

structure PhaseInput where
  n : Nat
  x : Nat
  lower : Nat
  upper : Nat
  firstPrimes : List Nat
  interval : List Nat
  trace : Bool
  power : PreparedPower
deriving Inhabited

@[noinline] def phase (name : String) (p : PhaseInput) : Hex.PMinusOneMeasure.Result :=
  let r := Hex.Rand.ofSeed 0
  match name with
  | "setup" =>
      { outcome := "setup"
        value := 2 % p.n + Nat.gcd 2 p.n + (primesBelow (p.lower + 1)).length +
          (PMinusOne.primes p.lower p.upper).length }
  | "enumeration" =>
      { outcome := "enumeration", value := (PMinusOne.primes p.lower p.upper).length }
  | "stage1" =>
      let x := PMinusOne.smoothPower p.n (2 % p.n) p.lower p.firstPrimes
      { outcome := "stage1-gcd", value := Nat.gcd ((x + p.n - 1) % p.n) p.n }
  | "preparation" =>
      { outcome := "preparation"
        value := 2 % p.n + Nat.gcd 2 p.n + (primesBelow (p.lower + 1)).length +
          (PMinusOne.primes p.lower p.upper).length + (preparePower p.n).checksum }
  | "prepared-stage1" =>
      let x := preparedSmooth p.power p.lower p.firstPrimes (2 % p.n)
      { outcome := "stage1-gcd", value := Nat.gcd ((x + p.n - 1) % p.n) p.n }
  | "prepared" => Hex.PMinusOneMeasure.fromRun <|
      PMinusOne.fromPrepared p.n p.x p.lower p.upper p.interval r p.trace
  | "continuation" => Hex.PMinusOneMeasure.fromRun <|
      PMinusOne.stage2Counted p.n p.x p.lower p.upper r
  | _ => Hex.PMinusOneMeasure.fromRun <|
      PMinusOne.searchCounted p.n 2 p.lower p.upper r

initialize phaseInput : IO.Ref PhaseInput ← IO.mkRef <|
  let p := prepareMiss 128 32749
  ⟨p.input.subject, p.input.x, 64, p.upper, primesBelow 65, p.primes, true,
    preparePower p.input.subject⟩

initialize phaseResult : IO.Ref (Option Hex.PMinusOneMeasure.Result) ← IO.mkRef none

def measurePhase (name : String) : IO Nat := do
  let result := phase name (← phaseInput.get)
  phaseResult.set (some result)
  return result.value + result.attempts + (result.events.foldl (fun n e =>
    match e with
    | .pMinusOne e => n + e.candidates + e.multiplications
    | .route _ _ => n) 0)

def runSetup (_ : Unit) : IO Nat := measurePhase "setup"
def runEnumeration (_ : Unit) : IO Nat := measurePhase "enumeration"
def runStage1 (_ : Unit) : IO Nat := measurePhase "stage1"
def runPreparation (_ : Unit) : IO Nat := measurePhase "preparation"
def runPreparedStage1 (_ : Unit) : IO Nat := measurePhase "prepared-stage1"
def runPreparedPhase (_ : Unit) : IO Nat := measurePhase "prepared"
def runContinuation (_ : Unit) : IO Nat := measurePhase "continuation"
def runTotal (_ : Unit) : IO Nat := measurePhase "total"

-- Fixed canonical phases expose setup amortization and backend boundaries.
-- Operand-size scaling belongs to the separate operation-model registrations.
setup_fixed_benchmark runSetup where { repeats := 3, maxSecondsPerCall := 10.0 }
setup_fixed_benchmark runEnumeration where { repeats := 3, maxSecondsPerCall := 10.0 }
setup_fixed_benchmark runStage1 where { repeats := 3, maxSecondsPerCall := 10.0 }
setup_fixed_benchmark runPreparation where { repeats := 3, maxSecondsPerCall := 10.0 }
setup_fixed_benchmark runPreparedStage1 where { repeats := 3, maxSecondsPerCall := 10.0 }
setup_fixed_benchmark runPreparedPhase where { repeats := 3, maxSecondsPerCall := 10.0 }
setup_fixed_benchmark runContinuation where { repeats := 3, maxSecondsPerCall := 10.0 }
setup_fixed_benchmark runTotal where { repeats := 3, maxSecondsPerCall := 10.0 }

/-- Diagnostics are serialized after the lean-bench timing boundary. -/
def emitResult (ref : IO.Ref (Option Hex.PMinusOneMeasure.Result)) : IO Unit := do
  if let some result ← ref.get then
    IO.println (Lean.Json.mkObj [("type", Lean.toJson "result"), ("result", result.json)]).compress

def probe (args : List String) : IO UInt32 := do
  match args with
  | [name, n, x, lower, upper, minNanos, trace] =>
      let n := n.toNat!
      let lower := lower.toNat!
      let upper := upper.toNat!
      phaseInput.set (PhaseInput.mk n x.toNat! lower upper
        (primesBelow (lower + 1)) (PMinusOne.primes lower upper) (trace == "true")
        (preparePower n))
      let target := match name with
        | "setup" => `Hex.PrimalityBench.Stage2.runSetup
        | "enumeration" => `Hex.PrimalityBench.Stage2.runEnumeration
        | "stage1" => `Hex.PrimalityBench.Stage2.runStage1
        | "preparation" => `Hex.PrimalityBench.Stage2.runPreparation
        | "prepared-stage1" => `Hex.PrimalityBench.Stage2.runPreparedStage1
        | "prepared" => `Hex.PrimalityBench.Stage2.runPreparedPhase
        | "continuation" => `Hex.PrimalityBench.Stage2.runContinuation
        | _ => `Hex.PrimalityBench.Stage2.runTotal
      let code ← LeanBench.runFixedChildMode target 0 minNanos.toNat!
      emitResult phaseResult
      return code
  | _ => throw (IO.userError "stage2-probe PHASE N X B1 B2 MIN_NANOS TRACE")

initialize constructionInput : IO.Ref (Nat × Nat × Bool × Nat) ← IO.mkRef (97, 0, false, 512)
initialize constructionResult : IO.Ref (Option Hex.PMinusOneMeasure.Result) ← IO.mkRef none

def runConstruction (_ : Unit) : IO Nat := do
  let (n, seed, enabled, maxBits) ← constructionInput.get
  let result := Hex.PMinusOneMeasure.construct n seed enabled maxBits
  constructionResult.set (some result)
  return if result.checked then result.value else 0

setup_fixed_benchmark runConstruction where { repeats := 3, maxSecondsPerCall := 600.0 }

def constructProbe (args : List String) : IO UInt32 := do
  match args with
  | [n, seed, enabled] | [n, seed, enabled, _] =>
      let maxBits := (args[3]?.bind String.toNat?).getD 512
      constructionInput.set (n.toNat!, seed.toNat!, enabled == "true", maxBits)
      let code ← LeanBench.runFixedChildMode `Hex.PrimalityBench.Stage2.runConstruction 0 0
      emitResult constructionResult
      return code
  | _ => throw (IO.userError "stage2-construct N SEED ENABLED [MAX_BITS]")

end Stage2

end Hex.PrimalityBench

def main (args : List String) : IO UInt32 :=
  match args with
  | "stage2-probe" :: args => Hex.PrimalityBench.Stage2.probe args
  | "stage2-construct" :: args => Hex.PrimalityBench.Stage2.constructProbe args
  | _ => LeanBench.Cli.dispatch args
