/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import HexPrimality.Inputs
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

end Hex.PrimalityBench

def main (args : List String) : IO UInt32 := LeanBench.Cli.dispatch args
