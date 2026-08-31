/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import HexIntFactor
import LeanBench

/-! Native benchmark families for integer factorization and replay. -/

namespace Hex.IntFactorBench

open Hex.Nat

-- Proof-producing benchmark inputs walk the committed primality table.
set_option maxRecDepth 100000

def runFactor (n : Nat) : Nat :=
  match factor? n (Hex.Rand.ofSeed n) with
  | .ok (F, _) => F.raw.factors.length
  | .error f => f.attempts

def runRho (n : Nat) : Nat :=
  match rhoSplit? n (Hex.Rand.ofSeed n) 1000000 with
  | .ok (d, _) => d
  | .error f => f.attempts

def runPMinusOne (n : Nat) : Nat :=
  match pMinusOneFactor n 2 10000 with
  | .factor d => d
  | .noFactor => 1
  | .whole => n

def runEcm (n : Nat) : Nat :=
  match ecmStage1 n 7 1000 with
  | .factor d => d
  | .noFactor => 1
  | .whole => n

def runCyclotomic (n : Nat) : Nat :=
  match cyclotomicSplit? 2 n .minus with
  | some parts => parts.foldl (fun acc part => acc + part.value % 65536) 0
  | none => 0

def replayInput (e : Nat) : Factorization :=
  ⟨2 ^ e, [⟨e, .small 2⟩]⟩

def runReplay (e : Nat) : Nat :=
  if checkFactorization (replayInput e) then 1 else 0

def runOrder (p : Nat) : Nat := orderOf 3 p

private def balancedInput : Nat → Nat
  | 32 => 64553 * 66553
  | 40 => 1047587 * 1049599
  | 48 => 16776217 * 16778227
  | 56 => 268434461 * 268436507
  | 64 => 4294966297 * 4294968317
  | 72 => 68719475767 * 68719477789
  | 80 => 1099511626781 * 1099511628781
  | _ => 64553 * 66553

def runBalancedFactor (bits : Nat) : Nat := runFactor (balancedInput bits)

def runBalancedRho (bits : Nat) : Nat := runRho (balancedInput bits)

private def smoothInput : Nat → Nat
  | 32 => 65537 * 65521
  | 40 => 65537 * 8400967
  | 48 => 65537 * 2147496017
  | 56 => 65537 * 549755826233
  | 64 => 65537 * 140737488367699
  | 72 => 65537 * 36028797018976327
  | 76 => 65537 * 576460752303435851
  | 80 => 65537 * 9223372036854788173
  | _ => 65537 * 65521

def runPMinusOneWord (bits : Nat) : Nat := runPMinusOne (smoothInput bits)

def runPMinusOneNat (bits : Nat) : Nat := runPMinusOne (smoothInput bits)

/- The word cases have least factor 1000003. The `Nat` cases have successful
ECM factors of 34, 37, and 39 bits. None has 1000-smooth predecessor, while the
fixed Suyama curve used by `runEcm` succeeds. This keeps the ECM ladder distinct
from a disguised p-1 success family and gives the arbitrary-precision backend
factors large enough to distinguish it from rho. -/
private def ecmInput : Nat → Nat
  | 48 => 1000003 * 268435579
  | 56 => 1000003 * 68719476901
  | 64 => 1000003 * 17592186044591
  | 72 => 8593846213 * 274878795833
  | 76 => 68723605421 * 549756752147
  | 80 => 274882253351 * 2199024243173
  | _ => 1000003 * 268435579

def runEcmWord (bits : Nat) : Nat := runEcm (ecmInput bits)

def runEcmNat (bits : Nat) : Nat := runEcm (ecmInput bits)

def runEcmRhoWord (bits : Nat) : Nat := runRho (ecmInput bits)

def runEcmRhoNat (bits : Nat) : Nat := runRho (ecmInput bits)

def runPowerSplit (e : Nat) : Nat :=
  match factorPower? 2 e .minus (Hex.Rand.ofSeed e) with
  | .ok (F, _) => F.raw.factors.length
  | .error f => f.attempts

def runPowerGeneric (e : Nat) : Nat :=
  runFactor (powerTarget 2 e .minus)

private def replayWidthInput (count : Nat) : Factorization :=
  let factors := (primeTable.toList.take count).map fun p => ⟨1, .small p⟩
  ⟨(factors.map fun entry => entry.prime).prod, factors⟩

def runReplayWidth (count : Nat) : Bool :=
  checkFactorization (replayWidthInput count)

def runPrimitiveRoot (p : Nat) : Nat :=
  match primeCert? p (Hex.Rand.ofSeed p) (defaultFuel p) with
  | .error failure => failure.attempts
  | .ok (pc, r) =>
      match factor? (p - 1) r with
      | .error failure => failure.attempts
      | .ok (F, _) =>
          match primitiveRoot? pc F p with
          | none => 0
          | some (g, _) => g

private def defaultFuelInputs : Array Nat := #[
  99999989,
  balancedInput 32,
  balancedInput 48,
  balancedInput 64,
  balancedInput 80,
  smoothInput 64,
  ecmInput 64,
  powerTarget 2 32 .minus,
  powerTarget 3 24 .plus
]

private def tableInputs : Array Nat := #[
  2, 3, 97, 65521, 65537, 99991, 99999989,
  97 * 101, 1009 * 1013, 65521 * 65537, 99991 * 100003
]

def runTableBatch (_ : Unit) : Array Nat := tableInputs.map runFactor

def runDefaultFuelSchedule (_ : Unit) : Array Nat :=
  defaultFuelInputs.map fun n =>
    match Internal.factorCounted? n (Hex.Rand.ofSeed n) with
    | .ok success => 2 * success.attempts + 1
    | .error failure => 2 * failure.attempts

def reportDefaultFuel : IO UInt32 := do
  for n in defaultFuelInputs do
    match Internal.factorCounted? n (Hex.Rand.ofSeed n) with
    | .ok success =>
        IO.println s!"{n},{defaultFuel n},success,{success.attempts}"
    | .error failure =>
        IO.println s!"{n},{defaultFuel n},failure,{failure.attempts}"
  return 0

def probeEcm (values : List String) : IO UInt32 := do
  for value in values do
    match value.toNat? with
    | none => IO.eprintln s!"invalid natural: {value}"
    | some n => IO.println s!"{n},{runEcm n}"
  return 0

private def orderLadder : Array Nat := #[257, 1013, 4073, 16363, 65537]

#guard orderLadder.all fun p => orderOf 3 p == p - 1

/- These 50- and 61-bit primes divide `3^64 - 1` and `3^176 - 1`,
respectively. They exercise downstream-sized operands while keeping the
otherwise linear reference order scan bounded. -/
private def downstreamOrderPrimes : Array Nat := #[
  926510094425921,
  1363620137403810529
]

def runDownstreamOrder (_ : Unit) : Array Nat :=
  downstreamOrderPrimes.map (orderOf 3)

def runDownstreamPrimitiveRoot (_ : Unit) : Array Nat :=
  downstreamOrderPrimes.map runPrimitiveRoot

private theorem boundedPowMul_exact (q acc : Nat) (hq : 0 < q)
    (hacc : 0 < acc) : ∀ e : Nat,
    boundedPowMul (acc * q ^ e) q acc e = some (acc * q ^ e)
  | 0 => by simp [boundedPowMul]
  | e + 1 => by
      have hpow : 0 < q ^ e := Nat.pow_pos hq
      have hle : q ≤ q ^ e * q := Nat.le_mul_of_pos_left q hpow
      have hmul : acc * q ≤ acc * q ^ (e + 1) := by
        simpa only [Nat.pow_succ] using Nat.mul_le_mul_left acc hle
      rw [boundedPowMul, if_neg (Nat.ne_of_gt hacc),
        if_neg (Nat.ne_of_gt hq),
        if_pos ((Nat.le_div_iff_mul_le hq).2 hmul)]
      simpa only [Nat.pow_succ, Nat.mul_assoc, Nat.mul_comm,
        Nat.mul_left_comm] using
        boundedPowMul_exact q (acc * q) hq (Nat.mul_pos hacc hq) e

private def sigmaExponentInput (e : Nat) : CheckedFactorization (3 ^ (e + 1)) :=
  ⟨⟨3 ^ (e + 1), [⟨e + 1, .small 3⟩]⟩, rfl, by
    simp only [checkFactorization, Bool.and_eq_true, decide_eq_true_eq]
    refine ⟨⟨Nat.pow_pos (by decide), ?_⟩, ?_⟩
    · simp [checkEntries, show checkPrime (.small 3) = true by decide]
    · simp only [factorProduct, PrimePower.prime, PrimeCert.subject]
      have h : boundedPowMul (3 ^ (e + 1)) 3 1 (e + 1) =
          some (3 ^ (e + 1)) := by
        simpa using boundedPowMul_exact 3 1 (by decide) (by decide) (e + 1)
      rw [h]⟩

structure SigmaExponentInput where
  subject : Nat
  checked : CheckedFactorization subject

instance : Hashable SigmaExponentInput where
  hash input := hash input.subject

def prepSigmaExponent (e : Nat) : SigmaExponentInput :=
  ⟨_, sigmaExponentInput e⟩

def runSigmaExponent (input : SigmaExponentInput) : Nat := sigma input.checked 1

private def sigmaEntries : List PrimePower :=
  primeTable.toList.map fun p => ⟨32, .small p⟩

private def sigmaSubject (count : Nat) : Nat :=
  ((sigmaEntries.take count).map fun entry => entry.prime ^ entry.exponent).prod

private def sigmaInput (count : Nat) (h : checkFactorization
    ⟨sigmaSubject count, sigmaEntries.take count⟩ = true) :
    CheckedFactorization (sigmaSubject count) :=
  ⟨⟨sigmaSubject count, sigmaEntries.take count⟩, rfl, h⟩

structure SigmaInput where
  subject : Nat
  checked : CheckedFactorization subject

instance : Hashable SigmaInput where
  hash input := hash input.subject

private opaque sigmaInputDefault : SigmaInput :=
  ⟨_, sigmaInput 0 (by decide)⟩
private opaque sigmaInput32 : SigmaInput :=
  ⟨_, sigmaInput 32 (by decide)⟩
private opaque sigmaInput64 : SigmaInput :=
  ⟨_, sigmaInput 64 (by decide)⟩
private opaque sigmaInput128 : SigmaInput :=
  ⟨_, sigmaInput 128 (by decide)⟩
private opaque sigmaInput256 : SigmaInput :=
  ⟨_, sigmaInput 256 (by decide)⟩
private opaque sigmaInput512 : SigmaInput :=
  ⟨_, sigmaInput 512 (by decide)⟩
set_option maxHeartbeats 1000000 in
private opaque sigmaInput1024 : SigmaInput :=
  ⟨_, sigmaInput 1024 (by decide)⟩

@[noinline]
def sigmaInputForCount : Nat → SigmaInput
  | 32 => sigmaInput32
  | 64 => sigmaInput64
  | 128 => sigmaInput128
  | 256 => sigmaInput256
  | 512 => sigmaInput512
  | 1024 => sigmaInput1024
  | _ => sigmaInputDefault

def runSigmaFactorCount (input : SigmaInput) : Nat :=
  sigma input.checked 1

def runSquareFactorCount (input : SigmaInput) : Nat :=
  squareDivisor input.checked + squarefreePart input.checked

def runTotientFactorCount (input : SigmaInput) : Nat :=
  totient input.checked

/- Generic factorization is rho-dominated on balanced semiprimes: the smaller
factor has size `sqrt n`, and rho takes its square root, giving `O(n^(1/4))`
arithmetic iterations. The returned factor-count hash is constant-size. -/
setup_benchmark runBalancedFactor n => 2 ^ (n / 4)
  where {
    paramFloor := 32
    paramCeiling := 80
    paramSchedule := .custom #[32, 40, 48, 56, 64, 72, 80]
    maxSecondsPerCall := 5.0
    targetInnerNanos := 100000000
    signalFloorMultiplier := 1.0
    outerTrials := 3
  }

/- Brent rho needs `O(sqrt p)` iterations for the least factor `p`; balanced
semiprimes have `p = sqrt n`, hence the declared `O(n^(1/4))` model. -/
setup_benchmark runBalancedRho n => 2 ^ (n / 4)
  where {
    paramFloor := 32
    paramCeiling := 80
    paramSchedule := .custom #[32, 40, 48, 56, 64, 72, 80]
    maxSecondsPerCall := 5.0
    targetInnerNanos := 100000000
    signalFloorMultiplier := 1.0
    outerTrials := 3
  }

/- The smoothness bound is fixed, so the arithmetic-operation count is fixed;
operand work scales with the modulus bit length, modeled by `O(log n)`. -/
setup_benchmark runPMinusOneWord n => n
  where {
    paramFloor := 32
    paramCeiling := 64
    paramSchedule := .custom #[32, 40, 48, 56, 64]
    maxSecondsPerCall := 5.0
    targetInnerNanos := 100000000
    signalFloorMultiplier := 1.0
    outerTrials := 3
  }

/- Above `2^64`, the p-1 stage uses direct `Nat` modular products. The bound
and scalar schedule remain fixed; quadratic operand work is the conservative
native model for this separate big-integer regime. -/
setup_benchmark runPMinusOneNat n => n * n
  where {
    paramFloor := 72
    paramCeiling := 80
    paramSchedule := .custom #[72, 76, 80]
    maxSecondsPerCall := 5.0
    targetInnerNanos := 100000000
    signalFloorMultiplier := 1.0
    outerTrials := 3
  }

/- Below `2^64`, ECM uses the fixed-width Montgomery backend. The curve and
smoothness bound are fixed, so this route is constant-cost in the selected
word-size regime. -/
setup_benchmark runEcmWord _n => 1
  where {
    paramFloor := 48
    paramCeiling := 64
    paramSchedule := .custom #[48, 56, 64]
    maxSecondsPerCall := 5.0
    targetInnerNanos := 100000000
    signalFloorMultiplier := 1.0
    outerTrials := 3
  }

/- Above the word boundary the same fixed stage-1 schedule uses direct `Nat`
modular products. With a fixed scalar-step count, quadratic operand work is
the conservative native-cost model on this short big-integer ladder. -/
setup_benchmark runEcmNat n => n * n
  where {
    paramFloor := 72
    paramCeiling := 80
    paramSchedule := .custom #[72, 76, 80]
    maxSecondsPerCall := 5.0
    targetInnerNanos := 100000000
    signalFloorMultiplier := 1.0
    outerTrials := 3
  }

/- On the same word-size ECM policy inputs, rho sees the fixed 20-bit least
factor 1000003. Its iteration count is therefore fixed across this ladder; the
paired registration makes the stage-1 policy decision directly measurable. -/
setup_benchmark runEcmRhoWord _n => 1
  where {
    paramFloor := 48
    paramCeiling := 64
    paramSchedule := .custom #[48, 56, 64]
    maxSecondsPerCall := 5.0
    targetInnerNanos := 100000000
    signalFloorMultiplier := 1.0
    outerTrials := 3
  }

/- Above the word boundary, the selected successful ECM factors grow toward
the square root of the input. Brent rho's worst expected route cost is thus
`O(n^(1/4))` arithmetic iterations; the exponential bit-length model is the
conservative upper bound used for this short paired policy ladder. -/
setup_benchmark runEcmRhoNat n => 2 ^ (n / 4)
  where {
    paramFloor := 72
    paramCeiling := 80
    paramSchedule := .custom #[72, 76, 80]
    maxSecondsPerCall := 5.0
    targetInnerNanos := 100000000
    signalFloorMultiplier := 1.0
    outerTrials := 3
  }

/- Building recursive cyclotomic values for the divisor indices through `n`
revisits prefixes whose total length has a quadratic cost bound. -/
setup_benchmark runCyclotomic n => n * n
  where {
    paramFloor := 4
    paramCeiling := 32
    paramSchedule := .custom #[4, 8, 16, 24, 32]
    maxSecondsPerCall := 5.0
    targetInnerNanos := 100000000
    signalFloorMultiplier := 1.0
  }

/- `boundedPowMul` replays the single exponent one guarded multiplication at a
time. The accumulator grows throughout the replay, so `n²` is the conservative
native-cost model for the widening guarded multiplications and divisions. -/
setup_benchmark runReplay n => n * n
  where {
    paramFloor := 1024
    paramCeiling := 262144
    paramSchedule := .custom #[1024, 4096, 16384, 65536, 262144]
    maxSecondsPerCall := 5.0
    targetInnerNanos := 100000000
    signalFloorMultiplier := 1.0
    outerTrials := 3
  }

/- Replay visits each certified prime-power entry once. The growing subject
also makes guarded products wider, so `n^2` is the conservative native-cost
model for the 1-through-10 entry ladder required by the SPEC. -/
setup_benchmark runReplayWidth n => n * n
  where {
    paramFloor := 1
    paramCeiling := 10
    paramSchedule := .custom #[1, 2, 4, 6, 8, 10]
    maxSecondsPerCall := 5.0
    targetInnerNanos := 100000000
    signalFloorMultiplier := 1.0
    outerTrials := 3
  }

/- `orderOf` carries one bounded residue and performs one modular multiplication
per candidate exponent. On every prime in this ladder, `3` has order `p - 1`,
so each run exercises `p - 1` scan steps and the declared arithmetic-operation
model is linear. -/
setup_benchmark runOrder n => n
  where {
    paramFloor := 257
    paramCeiling := 65537
    paramSchedule := .custom orderLadder
    maxSecondsPerCall := 5.0
    targetInnerNanos := 2500000000
    signalFloorMultiplier := 1.0
    outerTrials := 3
  }

/- The ascending primitive-root search performs at most `p` candidates, each
with bounded modular checks. This is the public search's linear candidate-count
upper bound; the selected primes expose its actual early-success policy. -/
setup_benchmark runPrimitiveRoot n => n
  where {
    paramFloor := 257
    paramCeiling := 65537
    paramSchedule := .custom orderLadder
    maxSecondsPerCall := 5.0
    targetInnerNanos := 100000000
    signalFloorMultiplier := 1.0
    outerTrials := 3
  }

/- Factoring `2^n - 1` without the structural split has the input-value upper
bound `2^n`; this registration is paired with `runPowerSplit` to measure the
policy benefit. The report treats faster observed scaling as a mode-2 upper-
bound result, not as a tight exponential claim. -/
setup_benchmark runPowerGeneric n => 2 ^ n
  where {
    paramFloor := 12
    paramCeiling := 64
    paramSchedule := .custom #[12, 16, 20, 24, 28, 32, 40, 48, 56, 64]
    maxSecondsPerCall := 5.0
    targetInnerNanos := 100000000
    signalFloorMultiplier := 1.0
    outerTrials := 3
  }

/- The cyclotomic route has the same conservative input-value upper bound as
the generic route, allowing an output-agreeing paired policy comparison over
the exact same exponent ladder. -/
setup_benchmark runPowerSplit n => 2 ^ n
  where {
    paramFloor := 12
    paramCeiling := 64
    paramSchedule := .custom #[12, 16, 20, 24, 28, 32, 40, 48, 56, 64]
    maxSecondsPerCall := 5.0
    targetInnerNanos := 100000000
    signalFloorMultiplier := 1.0
    outerTrials := 3
  }

/- These targets are much faster per call than the route-search targets
above, while using the same warm, autotuned 100 ms child-side batches. On the
scheduled high-startup host, the default ten-spawn floor would discard their
in-process measurements; the 1.0 multiplier changes only that filter, and
exported evidence still records the measured floor. -/

/- For the certified input `3^(e+1)` at `k = 1`, `sigma` computes a nontrivial
exact geometric quotient with `Theta(e)` output bits. Preparation hoists the
unused certified subject out of the timed loop. The quotient divisor is the
single-limb value `2`, so exponentiation dominates with the declared
quasi-linear `n log n` surrogate; Lean's `Nat` result hash is constant-time. -/
setup_benchmark runSigmaExponent n => n * n.log2
  with prep := prepSigmaExponent
  where {
    paramFloor := 16384
    paramCeiling := 4194304
    paramSchedule := .custom #[16384, 65536, 262144, 1048576, 4194304]
    maxSecondsPerCall := 5.0
    targetInnerNanos := 100000000
    signalFloorMultiplier := 1.0
    -- The multi-million-bit ladder crosses native multiplication regimes;
    -- 0.20 admits that finite-range transition without changing the model.
    slopeTolerance := 0.20
    outerTrials := 3
  }

/- Each certified entry has exponent 32. The `i`th sequential product step
multiplies a linearly growing accumulator by one bounded-size table-prime
entry sum. Its cost is `Theta(i)` limbs, whose sum is the declared
`Theta(n²)` native-cost model. Preparation selects a prechecked input once per
child spawn, outside the timed loop. -/
setup_benchmark runSigmaFactorCount n => n * n
  with prep := sigmaInputForCount
  where {
    paramFloor := 32
    paramCeiling := 512
    paramSchedule := .custom #[32, 64, 128, 256, 512]
    maxSecondsPerCall := 5.0
    targetInnerNanos := 100000000
    signalFloorMultiplier := 1.0
    outerTrials := 3
  }

/- Each prepared certificate has `n` entries of fixed exponent 32. The
square-divisor accumulator grows linearly in limbs, so its sequential
multiplication has the declared `Theta(n²)` native-cost model; the parity
product is identically one and contributes only a linear pass. Preparation
hoists the enormous certified subject out of the timed loop, so an input-range
scan would be immediately observable rather than hidden in setup. -/
setup_benchmark runSquareFactorCount n => n * n
  with prep := sigmaInputForCount
  where {
    paramFloor := 32
    paramCeiling := 1024
    paramSchedule := .custom #[32, 64, 128, 256, 512, 1024]
    maxSecondsPerCall := 5.0
    targetInnerNanos := 100000000
    signalFloorMultiplier := 1.0
    -- At 32..512 the early accumulator-width regimes gave an inconclusive
    -- slope. Extending to 1024 exposes convergence toward the n² model.
    slopeTolerance := 0.20
    outerTrials := 3
  }

/- Each prepared certificate has `n` fixed-exponent prime-power entries.
`totient` builds one bounded-size contribution per entry, then sequentially
multiplies an accumulator whose limb count grows linearly, giving the declared
`Theta(n²)` native-cost model. Hashing the linearly sized result is lower-order.
Preparation hoists the enormous subject out of the timed loop; scanning
residues below it would not terminate on these subjects. -/
setup_benchmark runTotientFactorCount n => n * n
  with prep := sigmaInputForCount
  where {
    paramFloor := 32
    paramCeiling := 1024
    paramSchedule := .custom #[32, 64, 128, 256, 512, 1024]
    maxSecondsPerCall := 5.0
    targetInnerNanos := 100000000
    signalFloorMultiplier := 1.0
    -- The ladder crosses accumulator-width regimes; 0.20 admits that
    -- finite-range transition without changing the model.
    slopeTolerance := 0.20
    outerTrials := 3
  }

private def defaultFuelConfig : LeanBench.FixedBenchmarkConfig where
  repeats := 3
  maxSecondsPerCall := 10.0

/- Absolute downstream policy case: the exact public `defaultFuel` schedule
over table, balanced, smooth, ECM, and power-form inputs. The odd/even encoding
retains success/failure together with the charged attempt count. -/
setup_fixed_benchmark runDefaultFuelSchedule where defaultFuelConfig

/- Absolute committed-table policy case. This covers prime lookup and small
composite factorization independently of the growing balanced ladder. -/
setup_fixed_benchmark runTableBatch where defaultFuelConfig

/- Downstream-size order and primitive-root policy cases. Their chosen primes
have short order for base 3, so this fixed track records operand-size behavior
without pretending that the reference linear scan is feasible through 64 bits. -/
setup_fixed_benchmark runDownstreamOrder where defaultFuelConfig

setup_fixed_benchmark runDownstreamPrimitiveRoot where defaultFuelConfig

end Hex.IntFactorBench

def main (args : List String) : IO UInt32 :=
  match args with
  | ["default-fuel"] => Hex.IntFactorBench.reportDefaultFuel
  | "ecm-probe" :: values => Hex.IntFactorBench.probeEcm values
  | _ => LeanBench.Cli.dispatch args
