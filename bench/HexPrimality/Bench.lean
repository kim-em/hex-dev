/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import HexPrimality
import LeanBench

/-!
Benchmark registrations for `HexPrimality`.

Three certificate families run over a fixed ladder of primes of 31, 61,
123, 256, and 511 bits whose `n - 1` is `k · 2^m` with `k` factoring over
the committed table, so partial factorization is deterministic trial
division and no rho variance enters the decision or checker rows:

* `runDecision` runs the bounded decision `isPrime?` end to end;
* `runCertSearch` runs `primeCert?` alone (the SPEC keeps this family
  separate: its cost is dominated by search and says the least about the
  library);
* `runChecker` replays `checkPrime` on the prepared certificate — the
  compiled twin of the kernel-replay obligation, whose kernel-side cost
  the `HexPrimalityKernelProbe` build-only module measures.

`runSegment` prices `primesIn` over `[0, n)` natively. The named external
comparator (PrimeCert) is informational and cannot run in this repository
while the toolchains differ; see `libraries.yml` and the SPEC's
benchmarking section.
-/

namespace Hex.PrimalityBench

open Hex.Nat

/-- One prepared decision/certificate input. -/
structure Input where
  n : Nat
  cert : PrimeCert

instance : Hashable Input where
  hash i := hash i.n

instance : Inhabited Input :=
  ⟨{ n := 0, cert := .small 0 }⟩

/-- The 31-bit rung: `2^31 - 1`. -/
def cert31 : PrimeCert :=
  .pock 2147483647
    [(1745337962, 0, .small 2), (1371693800, 1, .small 3),
     (1615909500, 0, .small 7), (447824900, 0, .small 11),
     (505209180, 0, .small 31), (1783259301, 0, .small 151),
     (904659249, 0, .small 331)]

/-- The 61-bit rung: `27 · 2^56 + 1`. -/
def cert61 : PrimeCert :=
  .pock 1945555039024054273
    [(891154892214722695, 55, .small 2), (110189291828549774, 2, .small 3)]

/-- The 123-bit rung: `7 · 2^120 + 1`. -/
def cert123 : PrimeCert :=
  .pock 9304595970494411110326649421962412033
    [(14072917602864530050, 119, .small 2),
     (13757245211066428521, 0, .small 7)]

/-- The 256-bit rung: `207 · 2^248 + 1`. -/
def cert256 : PrimeCert :=
  .pock 93628759656736142393278101159368737990730026663232799828780155818898507169793
    [(8195237237126968763, 247, .small 2),
     (13757245211066428521, 1, .small 3),
     (10451216379200822467, 0, .small 23)]

/-- The 511-bit rung: `127 · 2^504 + 1`. -/
def cert511 : PrimeCert :=
  .pock 6651529715244960279866801463953681477304216637559507652230048059971343874294298695522804827606237247330601742147202064290729465301239118684363568061612033
    [(13757245211066428521, 503, .small 2),
     (10451216379200822467, 0, .small 127)]

/-- Map a bit-size rung to its prepared input. -/
def prepInput (bits : Nat) : Input :=
  if bits ≤ 31 then { n := 2147483647, cert := cert31 }
  else if bits ≤ 61 then { n := 1945555039024054273, cert := cert61 }
  else if bits ≤ 123 then { n := cert123.subject, cert := cert123 }
  else if bits ≤ 256 then { n := cert256.subject, cert := cert256 }
  else { n := cert511.subject, cert := cert511 }

private def sizeParams : Array Nat :=
  #[31, 61, 123, 256, 511]

-- Every rung's prepared certificate replays, and is about its own input.
#guard sizeParams.all fun bits =>
  let input := prepInput bits
  checkPrime input.cert && (input.cert.subject == input.n)

/-- Run the bounded decision end to end. -/
def runDecision (input : Input) : Nat :=
  match isPrime? input.n (Hex.Rand.ofSeed input.n) (defaultPrimeFuel input.n) with
  | .ok (true, _) => 1
  | .ok (false, _) => 0
  | .error _ => 2

/-- Run certificate search alone, forcing the result tree shallowly. -/
def runCertSearch (input : Input) : Nat :=
  match primeCert? input.n (Hex.Rand.ofSeed input.n) (defaultPrimeFuel input.n) with
  | .ok (c, _) => c.raw.subject % 4294967296
  | .error f => f.attempts

/-- Replay the checker on the prepared certificate: the compiled twin of
the kernel obligation. -/
def runChecker (input : Input) : Nat :=
  if checkPrime input.cert then 1 else 0

/-- Enumerate the primes below `n` and force the array. -/
def runSegment (n : Nat) : Nat :=
  (primesIn 0 n).size

/-- Identity preparation for the segment family. -/
def prepSegment (n : Nat) : Nat := n

/- One decision is a bounded number of modular exponentiations at `b`-bit
operands: `O(b)` multiplications of `O(b)`-bit numbers, a cubic bit-cost
proxy under schoolbook multiplication. GMP is subquadratic on the upper
rungs, so the tolerance is loose. -/
setup_benchmark runDecision n => n * n * n
  with prep := prepInput
  where {
    paramFloor := 31
    paramCeiling := 511
    paramSchedule := .custom sizeParams
    maxSecondsPerCall := 5.0
    targetInnerNanos := 100000000
    signalFloorMultiplier := 1.0
    slopeTolerance := 0.5
  }

/- Certificate search adds witness search over the same exponentiation
primitive, so the same cubic bit-cost proxy applies; the SPEC records
that this family's numbers say the least about the library, and the
fixed table-smooth inputs at least remove the rho variance. -/
setup_benchmark runCertSearch n => n * n * n
  with prep := prepInput
  where {
    paramFloor := 31
    paramCeiling := 511
    paramSchedule := .custom sizeParams
    maxSecondsPerCall := 5.0
    targetInnerNanos := 100000000
    signalFloorMultiplier := 1.0
    slopeTolerance := 0.5
  }

/- One checker level is `O(k)` modular exponentiations; the prepared
certificates keep `k` small and fixed, so the same cubic bit-cost proxy
applies. -/
setup_benchmark runChecker n => n * n * n
  with prep := prepInput
  where {
    paramFloor := 31
    paramCeiling := 511
    paramSchedule := .custom sizeParams
    maxSecondsPerCall := 5.0
    targetInnerNanos := 100000000
    signalFloorMultiplier := 1.0
    slopeTolerance := 0.5
  }

/- `primesIn` is trial division per candidate below `n`: `O(n √n)`
remainder tests. -/
setup_benchmark runSegment n => n * Nat.sqrt n
  with prep := prepSegment
  where {
    paramFloor := 1000
    paramCeiling := 32000
    paramSchedule := .custom #[1000, 2000, 4000, 8000, 16000, 32000]
    maxSecondsPerCall := 5.0
    targetInnerNanos := 100000000
    signalFloorMultiplier := 1.0
    slopeTolerance := 0.5
  }

end Hex.PrimalityBench

def main (args : List String) : IO UInt32 := LeanBench.Cli.dispatch args
