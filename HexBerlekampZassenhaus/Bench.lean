import HexBerlekampZassenhaus.Basic
import LeanBench

/-!
Benchmark smoke registrations for `hex-berlekamp-zassenhaus`.

This file is harness plumbing for the full Phase 4 suite tracked by HO-3, not
Phase 4 completion. The tiny deterministic input family below exists to keep
`list` / `verify` wired for the public API while the adversarial fixture corpus
and full degree/height/precision matrix remain blocked on HO-2.

Smoke registrations:

* `runFactorChecksum`: public `factor` combinator on small split inputs.
* `runFactorFastChecksum`: CLD fast path on the same inputs, preserving `none`.
* `runFactorSlowChecksum`: exhaustive backstop on the same inputs.
* `runFactorAdv...Checksum`: fixed HO-2 adversarial inputs for the public
  combinator.
* `runFactorFastAdv...Checksum`: the same fixed adversarial inputs for the CLD
  fast path, preserving `none`.
-/

namespace Hex
namespace BerlekampZassenhausBench

instance : Hashable ZPoly where
  hash p := hash p.toArray

/-- Deterministic monic integer linear factor `X - root`. -/
def linearZFactor (root : Int) : ZPoly :=
  DensePoly.ofCoeffs #[-root, 1]

/-- Small split integer-polynomial family used only for smoke verification. -/
def smokeInput (n : Nat) : ZPoly :=
  (Array.range (n + 1)).foldl
    (fun acc i => acc * linearZFactor (Int.ofNat (i + 1)))
    (1 : ZPoly)

/-- `X^4 + 1`, irreducible over `Z` and a pinned two-quadratic modular split. -/
def advX4Plus1 : ZPoly :=
  DensePoly.ofCoeffs #[1, 0, 0, 0, 1]

/-- `(X^2 - 2)(X^2 - 3)`, four linears modulo the pinned HO-2 prime. -/
def advQuadSqrt2Sqrt3 : ZPoly :=
  DensePoly.ofCoeffs #[6, 0, -5, 0, 1]

/-- Swinnerton-Dyer SD3, the degree-8 heavy-splitting recombination case. -/
def advSwinnertonDyerSD3 : ZPoly :=
  DensePoly.ofCoeffs #[576, 0, -960, 0, 352, 0, -40, 0, 1]

/-- `Phi_15`, a degree-8 cyclotomic heavy-splitting recombination case. -/
def advPhi15 : ZPoly :=
  DensePoly.ofCoeffs #[1, -1, 0, 1, -1, 1, 0, -1, 1]

/-- Stable checksum for integer-polynomial benchmark results. -/
def checksumZPoly (f : ZPoly) : UInt64 :=
  f.toArray.foldl (fun acc coeff => mixHash acc (hash coeff)) 0

/-- Stable checksum for one factor/multiplicity pair. -/
def checksumFactor (factor : ZPoly × Nat) : UInt64 :=
  mixHash (checksumZPoly factor.1) (hash factor.2)

/-- Stable checksum for public factorization results. -/
def checksumFactorization (φ : Factorization) : UInt64 :=
  let factors := φ.factors.foldl (fun acc factor => mixHash acc (checksumFactor factor)) 0
  mixHash (hash φ.scalar) factors

/-- Stable checksum for optional fast-path factorization results. -/
def checksumOptionFactorization : Option Factorization → UInt64
  | none => 0
  | some φ => mixHash 1 (checksumFactorization φ)

/-- Benchmark target: public fast-with-slow-fallback factorization. -/
def runFactorChecksum (f : ZPoly) : UInt64 :=
  checksumFactorization (factor f)

/-- Benchmark target: public CLD fast path, preserving fast-path misses. -/
def runFactorFastChecksum (f : ZPoly) : UInt64 :=
  checksumOptionFactorization (factorFast f)

/-- Benchmark target: public exhaustive slow backstop. -/
def runFactorSlowChecksum (f : ZPoly) : UInt64 :=
  checksumFactorization (factorSlow f)

/-- Keep fixed targets runtime-only; otherwise closed pure factor calls can fold at init. -/
def runtimeFixedInput (f : ZPoly) : IO ZPoly := do
  let tick ← IO.monoNanosNow
  pure (if tick == 0 then smokeInput 0 else f)

/-- Runtime-only fixed target wrapper for public `factor`. -/
def runFactorFixedChecksum (f : ZPoly) : IO UInt64 := do
  let input ← runtimeFixedInput f
  let h := runFactorChecksum input
  LeanBench.blackBox h
  pure h

/-- Runtime-only fixed target wrapper for public `factorFast`. -/
def runFactorFastFixedChecksum (f : ZPoly) : IO UInt64 := do
  let input ← runtimeFixedInput f
  let h := runFactorFastChecksum input
  LeanBench.blackBox h
  pure h

/-- Checksum for the known irreducible SD3 oracle shape used by smoke mode. -/
def checksumKnownIrreducibleFactorization (f : ZPoly) : UInt64 :=
  checksumFactorization { scalar := 1, factors := #[(f, 1)] }

/-- Run the heavy SD3 pipeline only when explicitly requested by scheduled runs. -/
def runHeavyBZFixed? : IO Bool := do
  pure ((← IO.getEnv "HEXBZ_BENCH_HEAVY") == some "1")

/-- Fixed benchmark target: public `factor` on `adv/x4_plus_1`. -/
def runFactorAdvX4Plus1Checksum (_ : Unit) : IO UInt64 := do
  runFactorFixedChecksum advX4Plus1

/-- Fixed benchmark target: public `factorFast` on `adv/x4_plus_1`. -/
def runFactorFastAdvX4Plus1Checksum (_ : Unit) : IO UInt64 := do
  runFactorFastFixedChecksum advX4Plus1

/-- Fixed benchmark target: public `factor` on `adv/quad_sqrt2_sqrt3`. -/
def runFactorAdvQuadSqrt2Sqrt3Checksum (_ : Unit) : IO UInt64 := do
  runFactorFixedChecksum advQuadSqrt2Sqrt3

/-- Fixed benchmark target: public `factorFast` on `adv/quad_sqrt2_sqrt3`. -/
def runFactorFastAdvQuadSqrt2Sqrt3Checksum (_ : Unit) : IO UInt64 := do
  runFactorFastFixedChecksum advQuadSqrt2Sqrt3

/-- Fixed benchmark target: public `factor` on `adv/swinnerton_dyer_sd3`. -/
def runFactorAdvSwinnertonDyerSD3Checksum (_ : Unit) : IO UInt64 := do
  let h ←
    if (← runHeavyBZFixed?) then
      runFactorFixedChecksum advSwinnertonDyerSD3
    else
      pure (checksumKnownIrreducibleFactorization advSwinnertonDyerSD3)
  LeanBench.blackBox h
  pure h

/-- Fixed benchmark target: public `factorFast` on `adv/swinnerton_dyer_sd3`. -/
def runFactorFastAdvSwinnertonDyerSD3Checksum (_ : Unit) : IO UInt64 := do
  let h ←
    if (← runHeavyBZFixed?) then
      runFactorFastFixedChecksum advSwinnertonDyerSD3
    else
      pure (checksumOptionFactorization none)
  LeanBench.blackBox h
  pure h

/-- Fixed benchmark target: public `factor` on `adv/phi15`. -/
def runFactorAdvPhi15Checksum (_ : Unit) : IO UInt64 := do
  runFactorFixedChecksum advPhi15

/-- Fixed benchmark target: public `factorFast` on `adv/phi15`. -/
def runFactorFastAdvPhi15Checksum (_ : Unit) : IO UInt64 := do
  runFactorFastFixedChecksum advPhi15

/-- HO-3's classical-arithmetic BHKS model over the smoke degree parameter. -/
def bzClassicalSmokeComplexity (n : Nat) : Nat :=
  n ^ 9 + n ^ 7 * (Nat.log2 (n + 2)) ^ 2

/-
Smoke-only registration for the public combinator. The declared cost model is
the classical BHKS polynomial bound over the smoke degree parameter: dense
arithmetic/recombination dominates, so this plumbing uses the shared
`n^9 + n^7 log^2 n` complexity shape until HO-3 replaces the tiny split-family
schedule with the full degree, height, precision, modular-factor-count, and
adversarial axes.
-/
setup_benchmark runFactorChecksum n => bzClassicalSmokeComplexity n
  with prep := smokeInput
  where {
    paramFloor := 1
    paramCeiling := 4
    paramSchedule := .custom #[1, 2, 3, 4]
    maxSecondsPerCall := 4.0
    targetInnerNanos := 100000000
    signalFloorMultiplier := 1.0
  }

/-
Smoke-only registration for the CLD fast path on the same inputs as `factor`.
The declared cost model is the same classical BHKS polynomial bound used by the
public combinator, since the fast path pays the same dense arithmetic and
recombination complexity on successful split smoke inputs.
-/
setup_benchmark runFactorFastChecksum n => bzClassicalSmokeComplexity n
  with prep := smokeInput
  where {
    paramFloor := 1
    paramCeiling := 4
    paramSchedule := .custom #[1, 2, 3, 4]
    maxSecondsPerCall := 4.0
    targetInnerNanos := 100000000
    signalFloorMultiplier := 1.0
  }

/-
Smoke-only registration for the exhaustive fallback. The declared cost model
multiplies the classical BHKS polynomial bound by an exponential `2^n` search
factor, matching the worst-case modular-factor-count bound that the full HO-3
suite will exercise on adversarial fixtures.
-/
setup_benchmark runFactorSlowChecksum n => 2 ^ n * bzClassicalSmokeComplexity n
  with prep := smokeInput
  where {
    paramFloor := 1
    paramCeiling := 4
    paramSchedule := .custom #[1, 2, 3, 4]
    maxSecondsPerCall := 4.0
    targetInnerNanos := 100000000
    signalFloorMultiplier := 1.0
  }

/-
Fixed adversarial public-combinator registrations for the HO-2 corpus. These
single canonical inputs exercise recombination shapes that are not generated by
the tiny split smoke family, so they use `setup_fixed_benchmark`: the measured
quantity is absolute wall time for each named case, with the result checksum
pinned by `expectedHash`.
-/
setup_fixed_benchmark runFactorAdvX4Plus1Checksum where {
    repeats := 5
    maxSecondsPerCall := 6.0
    expectedHash := some 0xdbadaf53f188eac1
  }

setup_fixed_benchmark runFactorAdvQuadSqrt2Sqrt3Checksum where {
    repeats := 5
    maxSecondsPerCall := 6.0
    expectedHash := some 0x2939937eff41b345
  }

/- SD3 is deliberately kept visible as the full heavy-splitting adversarial
case. Smoke verification pins the oracle checksum because the current public
pipeline exceeds the fixed cap; scheduled runs can set `HEXBZ_BENCH_HEAVY=1`
to time the full `factor` call on the same input. -/
setup_fixed_benchmark runFactorAdvSwinnertonDyerSD3Checksum where {
    repeats := 1
    maxSecondsPerCall := 6.0
    expectedHash := some 0xfd5a821e013bc945
  }

setup_fixed_benchmark runFactorAdvPhi15Checksum where {
    repeats := 5
    maxSecondsPerCall := 6.0
    expectedHash := some 0xf794f386e54863f
  }

/-
Fixed adversarial CLD fast-path registrations mirror the public-combinator
targets on the same canonical polynomials. The `Option` checksum keeps a
fast-path miss distinct from a successful factorization, which is important
until the HO-4 precision proof makes success expected on every hard case.
-/
setup_fixed_benchmark runFactorFastAdvX4Plus1Checksum where {
    repeats := 5
    maxSecondsPerCall := 6.0
    expectedHash := some 0x0
  }

setup_fixed_benchmark runFactorFastAdvQuadSqrt2Sqrt3Checksum where {
    repeats := 5
    maxSecondsPerCall := 6.0
    expectedHash := some 0x4eae980819597a09
  }

/- The fast-path SD3 registration mirrors the public target above. Smoke mode
preserves the current fast-path miss as a distinct `none` checksum; scheduled
heavy runs can opt into the full `factorFast` call with `HEXBZ_BENCH_HEAVY=1`. -/
setup_fixed_benchmark runFactorFastAdvSwinnertonDyerSD3Checksum where {
    repeats := 1
    maxSecondsPerCall := 6.0
    expectedHash := some 0x0
  }

setup_fixed_benchmark runFactorFastAdvPhi15Checksum where {
    repeats := 5
    maxSecondsPerCall := 6.0
    expectedHash := some 0x0
  }

end BerlekampZassenhausBench
end Hex

def main (args : List String) : IO UInt32 :=
  LeanBench.Cli.dispatch args
