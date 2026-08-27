/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import HexGFqRing.Operations
import HexPolyFast.Division
import HexPolyFp.PrimeField
import LeanBench

/-!
Benchmark registrations for `hex-gfq-ring`.

This Phase 4 infrastructure slice measures the canonical quotient-ring surface
for `F_p[x] / (f)` over the fixed word-prime field `F_65537`. Inputs use
deterministic dense moduli of degree `n + 1`; construction is hoisted through
`prep`, and timed targets return compact polynomial checksums.

Scientific registrations:

* `runReduceModChecksum`: dense polynomial remainder modulo a degree-`n`
  divisor, `O(n^2)`.
* `runOfPolyReprChecksum`: quotient construction followed by projection,
  `O(n^2)`.
* `runAddChecksum`: quotient addition on canonical representatives, `O(n)`.
* `runMulChecksum`: quotient multiplication on canonical representatives,
  `O(n^2)`.
* `runMulSchoolbookChecksum`: the retained schoolbook multiplication path for
  the end-to-end `mulFast` adoption comparison.
* `runNegSubChecksum`: quotient negation and subtraction, `O(n)`.
* `runPowChecksum`: square-and-multiply exponentiation, `O(n^2 log n)`.
* `runPowSchoolbookChecksum`: the retained quotient-power implementation.
* `runReduceFastChecksum`: one-shot Newton reduction paired with retained
  `runReduceModChecksum`.
* `runNsmulNatCastChecksum`: binary natural scalar multiplication plus casts,
  `O(n log n)`.
-/

namespace Hex
namespace GFqRingBench

open GFqRing

private instance benchBoundsLarge : ZMod64.Bounds 65537 := ⟨by decide, by decide⟩

-- `PolyQuotient` is a prime-modulus type.  65537 is far too large for the
-- linear primality decision procedure, so the trial-division bound is supplied
-- as data: 256 * 256 < 65537 < 257 * 257.
set_option maxRecDepth 8192 in
private theorem prime_65537 : Hex.Nat.Prime 65537 :=
  Hex.Nat.prime_of_bounded 65537 256 (by decide) (by decide) (by decide)

private instance benchPrimeLarge : ZMod64.PrimeModulus 65537 :=
  ZMod64.primeModulusOfPrime prime_65537

private theorem one_ne_zero_large : (1 : ZMod64 65537) ≠ 0 := by
  intro h
  have hm := (ZMod64.natCast_eq_natCast_iff (p := 65537) 1 0).mp h
  simp at hm

instance : Hashable (ZMod64 65537) where
  hash a := hash a.toNat

instance : Hashable (FpPoly 65537) where
  hash f := hash f.toArray

/-- Deterministic large-prime coefficient generator keyed by size, index, and salt. -/
def coeffValue (n i salt : Nat) : ZMod64 65537 :=
  ZMod64.ofNat 65537 <|
    ((i + 1) * (salt + 17) + (i + 3) * (i + 5) * 13 + n * 29) % 65537

/-- Deterministic dense polynomial over the benchmark prime field. -/
def densePoly (n salt : Nat) : FpPoly 65537 :=
  FpPoly.ofCoeffs <| (Array.range n).map fun i => coeffValue n i salt

/-- Deterministic nonconstant modulus of degree `degree + 1`. -/
def modulus (degree : Nat) : FpPoly 65537 :=
  { coeffs := ((Array.range degree).map fun i => coeffValue degree i 503).push 1
    normalized := by
      right
      intro hback
      have hlast :
          (((Array.range degree).map fun i => coeffValue degree i 503).push
              (1 : ZMod64 65537)).back? = some 1 := by
        simp
      rw [hlast] at hback
      exact one_ne_zero_large (Option.some.inj hback) }

/-- Generated moduli are nonconstant, so quotient representatives are meaningful. -/
theorem modulus_pos_degree (degree : Nat) : 0 < FpPoly.degree (modulus (degree + 1)) := by
  unfold FpPoly.degree DensePoly.degree? DensePoly.size modulus
  simp

/-- Stable checksum for polynomial-valued benchmark results. -/
def checksumPoly (f : FpPoly 65537) : UInt64 :=
  f.toArray.foldl (fun acc coeff => mixHash acc (hash coeff)) 0

/-- Prepared input for raw `reduceMod` benchmarks. -/
structure ReduceInput where
  modulus : FpPoly 65537
  poly : FpPoly 65537

/-- Prepared input for quotient construction/projection benchmarks. -/
structure OfPolyInput where
  modulus : FpPoly 65537
  modulusDegreePos : 0 < FpPoly.degree modulus
  poly : FpPoly 65537

/-- Prepared input for binary quotient operations. -/
structure BinaryInput where
  modulus : FpPoly 65537
  modulusDegreePos : 0 < FpPoly.degree modulus
  lhs : PolyQuotient modulus modulusDegreePos
  rhs : PolyQuotient modulus modulusDegreePos

/-- Prepared input for unary quotient operations. -/
structure UnaryInput where
  modulus : FpPoly 65537
  modulusDegreePos : 0 < FpPoly.degree modulus
  value : PolyQuotient modulus modulusDegreePos

/-- Prepared input for quotient exponentiation. -/
structure PowInput where
  modulus : FpPoly 65537
  modulusDegreePos : 0 < FpPoly.degree modulus
  value : PolyQuotient modulus modulusDegreePos
  exponent : Nat

/-- Prepared input for natural scalar/cast benchmarks. -/
structure NatInput where
  modulus : FpPoly 65537
  modulusDegreePos : 0 < FpPoly.degree modulus
  value : PolyQuotient modulus modulusDegreePos
  scalar : Nat

instance : Hashable ReduceInput where
  hash input := mixHash (hash input.modulus) (hash input.poly)

instance : Hashable OfPolyInput where
  hash input := mixHash (hash input.modulus) (hash input.poly)

instance : Hashable BinaryInput where
  hash input :=
    mixHash (mixHash (hash input.modulus) (hash <| repr input.lhs)) (hash <| repr input.rhs)

instance : Hashable UnaryInput where
  hash input := mixHash (hash input.modulus) (hash <| repr input.value)

instance : Hashable PowInput where
  hash input :=
    mixHash (mixHash (hash input.modulus) (hash <| repr input.value)) (hash input.exponent)

instance : Hashable NatInput where
  hash input :=
    mixHash (mixHash (hash input.modulus) (hash <| repr input.value)) (hash input.scalar)

/-- Per-parameter fixture for polynomial reduction by a degree-`n` modulus. -/
def prepReduceInput (n : Nat) : ReduceInput :=
  let degree := n + 1
  { modulus := modulus degree
    poly := densePoly (2 * degree + 1) 11 }

/-- Per-parameter fixture for quotient construction. -/
def prepOfPolyInput (n : Nat) : OfPolyInput :=
  let degree := n + 1
  let f := modulus degree
  let hf : 0 < FpPoly.degree f := by
    simpa [f] using modulus_pos_degree n
  { modulus := f
    modulusDegreePos := hf
    poly := densePoly (2 * degree + 1) 23 }

/-- Per-parameter fixture for quotient binary operations. -/
def prepBinaryInput (n : Nat) : BinaryInput :=
  let degree := n + 1
  let f := modulus degree
  let hf : 0 < FpPoly.degree f := by
    simpa [f] using modulus_pos_degree n
  { modulus := f
    modulusDegreePos := hf
    lhs := ofPoly f hf (densePoly degree 37)
    rhs := ofPoly f hf (densePoly degree 71) }

/-- Per-parameter fixture for quotient unary operations. -/
def prepUnaryInput (n : Nat) : UnaryInput :=
  let input := prepBinaryInput n
  { modulus := input.modulus
    modulusDegreePos := input.modulusDegreePos
    value := input.lhs }

/-- Exponent with all bits set at the benchmark parameter's bit length. -/
def denseExponent (n : Nat) : Nat :=
  2 ^ (Nat.log2 (n + 1) + 1) - 1

/-- Per-parameter fixture for quotient exponentiation. -/
def prepPowInput (n : Nat) : PowInput :=
  let input := prepUnaryInput n
  { modulus := input.modulus
    modulusDegreePos := input.modulusDegreePos
    value := input.value
    exponent := denseExponent n }

/-- Per-parameter fixture for natural scalar multiplication and casts. -/
def prepNatInput (n : Nat) : NatInput :=
  let input := prepUnaryInput n
  { modulus := input.modulus
    modulusDegreePos := input.modulusDegreePos
    value := input.value
    scalar := n + 1 }

/-- Benchmark target: reduce a dense polynomial modulo the prepared modulus. -/
def runReduceModChecksum (input : ReduceInput) : UInt64 :=
  checksumPoly <| reduceMod input.modulus input.poly

/-- Benchmark candidate: quotient remainder through one-shot Newton division. -/
def runReduceFastChecksum (input : ReduceInput) : UInt64 :=
  let qr : FpPoly 65537 × FpPoly 65537 :=
    @DensePoly.divModWith (ZMod64 65537) inferInstance inferInstance
      (FpPoly.fastPlan (p := 65537)) input.poly input.modulus
  checksumPoly qr.2

/-- Benchmark target: construct and project a quotient representative. -/
def runOfPolyReprChecksum (input : OfPolyInput) : UInt64 :=
  checksumPoly <| repr <| ofPoly input.modulus input.modulusDegreePos input.poly

/-- Benchmark target: quotient addition checksum. -/
def runAddChecksum (input : BinaryInput) : UInt64 :=
  checksumPoly <| repr (input.lhs + input.rhs)

/-- Benchmark target: quotient multiplication checksum. -/
def runMulChecksum (input : BinaryInput) : UInt64 :=
  checksumPoly <| repr (input.lhs * input.rhs)

/-- Benchmark reference: quotient multiplication with schoolbook products. -/
def runMulSchoolbookChecksum (input : BinaryInput) : UInt64 :=
  checksumPoly <| reduceMod input.modulus (repr input.lhs * repr input.rhs)

/-- Benchmark target: quotient negation and subtraction checksum. -/
def runNegSubChecksum (input : BinaryInput) : UInt64 :=
  mixHash (checksumPoly <| repr (-input.lhs)) (checksumPoly <| repr (input.lhs - input.rhs))

/-- Benchmark target: quotient exponentiation checksum. -/
def runPowChecksum (input : PowInput) : UInt64 :=
  checksumPoly <| repr (input.value ^ input.exponent)

/-- Retained quotient multiplication used only by the benchmark reference. -/
def mulSchoolbook {f : FpPoly 65537} {hf : 0 < FpPoly.degree f}
    (x y : PolyQuotient f hf) : PolyQuotient f hf :=
  ofPoly f hf (repr x * repr y)

/-- Retained quotient square-and-multiply used only by the benchmark reference. -/
def powSchoolbook {f : FpPoly 65537} {hf : 0 < FpPoly.degree f}
    (x : PolyQuotient f hf) (n : Nat) : PolyQuotient f hf :=
  let rec go (acc base : PolyQuotient f hf) (k : Nat) : PolyQuotient f hf :=
    if hk : k = 0 then acc
    else
      let acc' := if k % 2 = 1 then mulSchoolbook acc base else acc
      go acc' (mulSchoolbook base base) (k / 2)
  termination_by k
  decreasing_by
    simp_wf
    exact Nat.div_lt_self (Nat.pos_of_ne_zero hk) (by decide)
  go (one f hf) x n

/-- Benchmark reference: quotient exponentiation with schoolbook products. -/
def runPowSchoolbookChecksum (input : PowInput) : UInt64 :=
  checksumPoly <| repr (powSchoolbook input.value input.exponent)

/-- Benchmark target: natural scalar multiplication and casts checksum. -/
def runNsmulNatCastChecksum (input : NatInput) : UInt64 :=
  mixHash
    (checksumPoly <| repr (nsmul input.scalar input.value))
    (checksumPoly <| repr (natCast input.modulus input.modulusDegreePos input.scalar))

/-
Polynomial long division by a degree-`n` modulus performs a linear number of
dense coefficient updates on a degree-`2n` dividend, giving quadratic work.
-/
setup_benchmark runReduceModChecksum n => n * n
  with prep := prepReduceInput
  where {
    paramFloor := 32
    paramCeiling := 256
    paramSchedule := .custom #[32, 48, 64, 96, 128, 192, 256]
    maxSecondsPerCall := 4.0
    targetInnerNanos := 200000000
    signalFloorMultiplier := 1.0
  }

/-
Newton reduction is `O(M(n))`; the registered quadratic bound is conservative
for the current dense finite-field multiplication substrate.
-/
setup_benchmark runReduceFastChecksum n => (n * n)
  with prep := prepReduceInput
  where {
    paramFloor := 32
    paramCeiling := 256
    paramSchedule := .custom #[32, 48, 64, 96, 128, 192, 256]
    maxSecondsPerCall := 6.0
    targetInnerNanos := 200000000
    signalFloorMultiplier := 1.0
    tags := #["adoption", "reduction", "newton", "candidate", "fp65537"]
  }

/-
`ofPoly` normalizes through the same degree-`n` reduction as `reduceMod`; `repr`
is only the projection of the stored canonical representative.
-/
setup_benchmark runOfPolyReprChecksum n => n * n
  with prep := prepOfPolyInput
  where {
    paramFloor := 32
    paramCeiling := 256
    paramSchedule := .custom #[32, 48, 64, 96, 128, 192, 256]
    maxSecondsPerCall := 4.0
    targetInnerNanos := 200000000
    signalFloorMultiplier := 1.0
  }

/-
Canonical quotient addition touches at most `n` coefficients. The following
normalization is on an already degree-bounded representative.
-/
setup_benchmark runAddChecksum n => n
  with prep := prepBinaryInput
  where {
    paramFloor := 1024
    paramCeiling := 16384
    paramSchedule := .custom #[1024, 2048, 4096, 8192, 16384]
    maxSecondsPerCall := 2.0
    targetInnerNanos := 200000000
    signalFloorMultiplier := 1.0
  }

/-
Canonical quotient multiplication multiplies two degree-bounded dense
representatives and reduces the product modulo a degree-`n` modulus.
-/
setup_benchmark runMulChecksum n => n * n
  with prep := prepBinaryInput
  where {
    paramFloor := 32
    paramCeiling := 256
    paramSchedule := .custom #[32, 48, 64, 96, 128, 192, 256]
    maxSecondsPerCall := 4.0
    targetInnerNanos := 200000000
    signalFloorMultiplier := 1.0
  }

/-
The retained path performs quadratic dense multiplication followed by a
degree-`n` reduction with the same quadratic bound.
-/
setup_benchmark runMulSchoolbookChecksum n => (n * n)
  with prep := prepBinaryInput
  where {
    paramFloor := 32
    paramCeiling := 256
    paramSchedule := .custom #[32, 48, 64, 96, 128, 192, 256]
    maxSecondsPerCall := 4.0
    targetInnerNanos := 200000000
    signalFloorMultiplier := 1.0
    tags := #["adoption", "multiplication", "schoolbook", "reference", "fp65537"]
  }

/-
Negation and subtraction are coefficientwise operations on canonical
degree-bounded representatives, followed by degree-bounded normalization.
-/
setup_benchmark runNegSubChecksum n => n
  with prep := prepBinaryInput
  where {
    paramFloor := 1024
    paramCeiling := 16384
    paramSchedule := .custom #[1024, 2048, 4096, 8192, 16384]
    maxSecondsPerCall := 2.0
    targetInnerNanos := 200000000
    signalFloorMultiplier := 1.0
  }

/-
The prepared all-ones exponent has Theta(log n) bits and exercises both the
square and multiply-by-base branch on every bit. Each quotient multiplication is
quadratic in the modulus degree.
-/
setup_benchmark runPowChecksum n => n * n * Nat.log2 (n + 1)
  with prep := prepPowInput
  where {
    paramFloor := 32
    paramCeiling := 256
    paramSchedule := .custom #[32, 48, 64, 96, 128, 192, 256]
    maxSecondsPerCall := 4.0
    targetInnerNanos := 200000000
    signalFloorMultiplier := 1.0
  }

/-
Binary powering performs logarithmically many retained quadratic quotient
multiplications, giving `O(n^2 log n)` coefficient work.
-/
setup_benchmark runPowSchoolbookChecksum n => (n * n * Nat.log2 (n + 1))
  with prep := prepPowInput
  where {
    paramFloor := 32
    paramCeiling := 256
    paramSchedule := .custom #[32, 48, 64, 96, 128, 192, 256]
    maxSecondsPerCall := 4.0
    targetInnerNanos := 200000000
    signalFloorMultiplier := 1.0
    tags := #["adoption", "power", "schoolbook", "reference", "fp65537"]
  }

/-
Binary natural scalar multiplication uses Theta(log n) quotient additions for
the prepared scalar. Natural casts add the constant-polynomial reduction cost.
-/
setup_benchmark runNsmulNatCastChecksum n => n * Nat.log2 (n + 1)
  with prep := prepNatInput
  where {
    paramFloor := 1024
    paramCeiling := 16384
    paramSchedule := .custom #[1024, 2048, 4096, 8192, 16384]
    maxSecondsPerCall := 2.0
    targetInnerNanos := 200000000
    signalFloorMultiplier := 1.0
  }

end GFqRingBench
end Hex

def main (args : List String) : IO UInt32 :=
  LeanBench.Cli.dispatch args
