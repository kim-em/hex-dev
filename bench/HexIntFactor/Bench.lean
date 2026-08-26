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

set_option maxRecDepth 20000

def runFactor (n : Nat) : Nat :=
  match factor? n (Hex.Rand.ofSeed n) with
  | .ok (F, _) => F.raw.factors.length
  | .error f => f.attempts

def runRho (n : Nat) : Nat :=
  match rhoSplit? n (Hex.Rand.ofSeed n) 1000000 with
  | .ok (d, _) => d
  | .error f => f.attempts

def runPMinusOne (n : Nat) : Nat :=
  match pMinusOneStage1 n 2 10000 with
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

def runOrder (p : Nat) : Nat := orderOf 2 p

private theorem boundedPowMul_exact (q acc : Nat) (hq : 0 < q) : ∀ e : Nat,
    boundedPowMul (acc * q ^ e) q acc e = some (acc * q ^ e)
  | 0 => by simp [boundedPowMul]
  | e + 1 => by
      rw [boundedPowMul, ite_eq_right]
      · simpa only [Nat.pow_succ, Nat.mul_assoc, Nat.mul_comm,
          Nat.mul_left_comm] using boundedPowMul_exact q (acc * q) hq e
      · have hpow : 0 < q ^ e := Nat.pow_pos hq
        have hle : q ≤ q ^ e * q := Nat.le_mul_of_pos_left q hpow
        exact Nat.not_lt_of_ge (by
          simpa only [Nat.pow_succ] using Nat.mul_le_mul_left acc hle)

private def sigmaExponentInput (e : Nat) : CheckedFactorization (3 ^ (e + 1)) :=
  ⟨⟨3 ^ (e + 1), [⟨e + 1, .small 3⟩]⟩, rfl, by
    simp only [checkFactorization, Bool.and_eq_true, decide_eq_true_eq]
    refine ⟨⟨Nat.pow_pos (by decide), ?_⟩, ?_⟩
    · simp [checkEntries, show checkPrime (.small 3) = true by decide]
    · simp only [factorProduct, PrimePower.prime, PrimeCert.subject]
      have h : boundedPowMul (3 ^ (e + 1)) 3 1 (e + 1) =
          some (3 ^ (e + 1)) := by
        simpa using boundedPowMul_exact 3 1 (by decide) (e + 1)
      rw [h]⟩

def runSigmaExponent (e : Nat) : Nat := sigma (sigmaExponentInput e) 1

private def sigmaEntries : List PrimePower :=
  [⟨32, .small 2⟩, ⟨32, .small 3⟩, ⟨32, .small 5⟩,
    ⟨32, .small 7⟩, ⟨32, .small 11⟩, ⟨32, .small 13⟩,
    ⟨32, .small 17⟩, ⟨32, .small 19⟩, ⟨32, .small 23⟩,
    ⟨32, .small 29⟩, ⟨32, .small 31⟩, ⟨32, .small 37⟩,
    ⟨32, .small 41⟩, ⟨32, .small 43⟩, ⟨32, .small 47⟩,
    ⟨32, .small 53⟩, ⟨32, .small 59⟩, ⟨32, .small 61⟩,
    ⟨32, .small 67⟩, ⟨32, .small 71⟩, ⟨32, .small 73⟩,
    ⟨32, .small 79⟩, ⟨32, .small 83⟩, ⟨32, .small 89⟩,
    ⟨32, .small 97⟩]

private def sigmaSubject (count : Nat) : Nat :=
  ((sigmaEntries.take count).map fun entry => entry.prime ^ entry.exponent).prod

private def sigmaInput (count : Nat) (h : checkFactorization
    ⟨sigmaSubject count, sigmaEntries.take count⟩ = true) :
    CheckedFactorization (sigmaSubject count) :=
  ⟨⟨sigmaSubject count, sigmaEntries.take count⟩, rfl, h⟩

private opaque sigmaInput4 : CheckedFactorization (sigmaSubject 4) :=
  sigmaInput 4 (by decide)
private opaque sigmaInput8 : CheckedFactorization (sigmaSubject 8) :=
  sigmaInput 8 (by decide)
private opaque sigmaInput12 : CheckedFactorization (sigmaSubject 12) :=
  sigmaInput 12 (by decide)
private opaque sigmaInput16 : CheckedFactorization (sigmaSubject 16) :=
  sigmaInput 16 (by decide)
private opaque sigmaInput20 : CheckedFactorization (sigmaSubject 20) :=
  sigmaInput 20 (by decide)
private opaque sigmaInput25 : CheckedFactorization (sigmaSubject 25) :=
  sigmaInput 25 (by decide)

private structure SigmaInput where
  subject : Nat
  checked : CheckedFactorization subject

@[noinline]
private def sigmaInputForCount : Nat → SigmaInput
  | 4 => ⟨_, sigmaInput4⟩
  | 8 => ⟨_, sigmaInput8⟩
  | 12 => ⟨_, sigmaInput12⟩
  | 16 => ⟨_, sigmaInput16⟩
  | 20 => ⟨_, sigmaInput20⟩
  | 25 => ⟨_, sigmaInput25⟩
  | _ => ⟨_, sigmaInput4⟩

def runSigmaFactorCount (count : Nat) : Nat :=
  let input := sigmaInputForCount count
  sigma input.checked 1

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

/- `boundedPowMul` replays the single exponent one multiplication at a time,
so a certificate with exponent `n` has linear arithmetic-operation cost. -/
setup_benchmark runReplay n => n
  where {
    paramFloor := 1
    paramCeiling := 64
    paramSchedule := .custom #[1, 2, 4, 8, 16, 32, 64]
    maxSecondsPerCall := 5.0
    targetInnerNanos := 100000000
  }

/- `orderOf` scans candidate exponents up to the modulus and performs a bounded
modular-power check at each step, so the declared worst-case model is linear. -/
setup_benchmark runOrder n => n
  where {
    paramFloor := 7
    paramCeiling := 65537
    paramSchedule := .custom #[7, 31, 257, 65537]
    maxSecondsPerCall := 5.0
    targetInnerNanos := 100000000
  }

/- These two targets use warm, autotuned 100 ms child-side batches over fixed
scientific rungs. On the scheduled high-startup host, the default ten-spawn
floor would discard those in-process measurements; the 1.0 multiplier changes
only that filter, and exported evidence still records the measured floor. -/

/- For the certified input `3^(e+1)` at `k = 1`, `sigma` computes a nontrivial
exact geometric quotient with `Theta(e)` output bits. Binary exponentiation and
division dominate; hashing also traverses the growing result. Divide-and-
conquer division contributes a logarithmic factor over quasi-linear
multiplication, giving the declared soft-linear `n log^2 n` model. -/
setup_benchmark runSigmaExponent n => n * n.log2 * n.log2
  where {
    paramFloor := 16384
    paramCeiling := 4194304
    paramSchedule := .custom #[16384, 65536, 262144, 1048576, 4194304]
    maxSecondsPerCall := 5.0
    targetInnerNanos := 100000000
    signalFloorMultiplier := 1.0
    outerTrials := 3
  }

/- Each certified entry has exponent 32, so the geometric quotient dominates
fixed dispatch cost. `sigma` performs one such quotient and one product step
per entry; the growing product operands add the logarithmic factor in the
declared soft-linear model. -/
setup_benchmark runSigmaFactorCount n => n * n.log2
  where {
    paramFloor := 4
    paramCeiling := 25
    paramSchedule := .custom #[4, 8, 12, 16, 20, 25]
    maxSecondsPerCall := 5.0
    targetInnerNanos := 100000000
    signalFloorMultiplier := 1.0
    outerTrials := 3
  }

end Hex.IntFactorBench

def main (args : List String) : IO UInt32 := LeanBench.Cli.dispatch args
