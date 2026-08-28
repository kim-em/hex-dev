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

private def orderLadder : Array Nat := #[257, 1013, 4073, 16363, 65537]

#guard orderLadder.all fun p => orderOf 3 p == p - 1

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
setup_benchmark runFactor n => Nat.sqrt (Nat.sqrt n)
  where {
    paramFloor := 1000
    paramCeiling := 281474641166387
    paramSchedule := .custom #[1009, 10403, 4292870399, 281474641166387]
    maxSecondsPerCall := 5.0
    targetInnerNanos := 100000000
  }

/- Brent rho needs `O(sqrt p)` iterations for the least factor `p`; balanced
semiprimes have `p = sqrt n`, hence the declared `O(n^(1/4))` model. -/
setup_benchmark runRho n => Nat.sqrt (Nat.sqrt n)
  where {
    paramFloor := 1000
    paramCeiling := 18446744073709551615
    paramSchedule := .custom #[4292870399, 281474641166387, 18446743979220271189]
    maxSecondsPerCall := 5.0
    targetInnerNanos := 100000000
  }

/- The smoothness bound is fixed, so the arithmetic-operation count is fixed;
operand work scales with the modulus bit length, modeled by `O(log n)`. -/
setup_benchmark runPMinusOne n => n.log2
  where {
    paramFloor := 15
    paramCeiling := 10097063
    paramSchedule := .custom #[15, 299, 1009 * 10007]
    maxSecondsPerCall := 5.0
    targetInnerNanos := 100000000
  }

/- This stage-1 ladder fixes the curve and smoothness bound. Its scalar-step
count is fixed while modular operand work grows with `log n`. -/
setup_benchmark runEcm n => n.log2
  where {
    paramFloor := 91
    paramCeiling := 10403
    paramSchedule := .custom #[91, 589, 10403]
    maxSecondsPerCall := 5.0
    targetInnerNanos := 100000000
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
  }

/- `boundedPowMul` replays the single exponent one guarded multiplication at a
time, using one division to authorize each multiplication, so a certificate
with exponent `n` has linear arithmetic-operation cost. -/
setup_benchmark runReplay n => n
  where {
    paramFloor := 1
    paramCeiling := 64
    paramSchedule := .custom #[1, 2, 4, 8, 16, 32, 64]
    maxSecondsPerCall := 5.0
    targetInnerNanos := 100000000
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

end Hex.IntFactorBench

def main (args : List String) : IO UInt32 := LeanBench.Cli.dispatch args
