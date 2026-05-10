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
* HO-2 adversarial polynomial constants plus singleton `factor` / `factorFast`
  targets for the smoke-tractable recombination surfaces.
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

/-- HO-2 adversarial input `X^4 + 1`, irreducible over `Z` but split mod `5`. -/
def advX4Plus1 : ZPoly :=
  DensePoly.ofCoeffs #[1, 0, 0, 0, 1]

/-- HO-2 adversarial input `(X^2 - 2)(X^2 - 3)`. -/
def advQuadSqrt2Sqrt3 : ZPoly :=
  DensePoly.ofCoeffs #[6, 0, -5, 0, 1]

/-- HO-2 Swinnerton-Dyer `SD_3` input. -/
def advSwinnertonDyerSD3 : ZPoly :=
  DensePoly.ofCoeffs #[576, 0, -960, 0, 352, 0, -40, 0, 1]

/-- HO-2 cyclotomic `Phi_15` input. -/
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

/-- Singleton benchmark target: public factorization on `X^4 + 1`. -/
@[noinline]
def runFactorAdvX4Plus1Checksum (f : ZPoly) : UInt64 :=
  runFactorChecksum f

/-- Singleton benchmark target: fast path on `X^4 + 1`, preserving `none`. -/
@[noinline]
def runFactorFastAdvX4Plus1Checksum (f : ZPoly) : UInt64 :=
  runFactorFastChecksum f

/-- Singleton benchmark target: public factorization on `(X^2 - 2)(X^2 - 3)`. -/
@[noinline]
def runFactorAdvQuadSqrt2Sqrt3Checksum (f : ZPoly) : UInt64 :=
  runFactorChecksum f

/-- Singleton benchmark target: fast path on `(X^2 - 2)(X^2 - 3)`, preserving `none`. -/
@[noinline]
def runFactorFastAdvQuadSqrt2Sqrt3Checksum (f : ZPoly) : UInt64 :=
  runFactorFastChecksum f

/-- Singleton benchmark target: public factorization on `Phi_15`. -/
@[noinline]
def runFactorAdvPhi15Checksum (f : ZPoly) : UInt64 :=
  runFactorChecksum f

/-- Singleton benchmark target: fast path on `Phi_15`, preserving `none`. -/
@[noinline]
def runFactorFastAdvPhi15Checksum (f : ZPoly) : UInt64 :=
  runFactorFastChecksum f

def prepAdvX4Plus1 (_ : Nat) : ZPoly :=
  advX4Plus1

def prepAdvQuadSqrt2Sqrt3 (_ : Nat) : ZPoly :=
  advQuadSqrt2Sqrt3

def prepAdvPhi15 (_ : Nat) : ZPoly :=
  advPhi15

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

/- Singleton HO-2 adversarial target: `X^4 + 1`. The declared cost model is
`n + 1` because the schedule pins `n = 0`; this constant smoke bound records a
canonical recombination shape where the integer polynomial is irreducible but
splits modulo `5` without widening this PR into the full Phase-4 matrix. -/
setup_benchmark runFactorAdvX4Plus1Checksum n => n + 1
  with prep := prepAdvX4Plus1
  where {
    paramFloor := 0
    paramCeiling := 0
    paramSchedule := .custom #[0]
    maxSecondsPerCall := 4.0
    targetInnerNanos := 100000000
    signalFloorMultiplier := 1.0
  }

/- Singleton HO-2 adversarial fast-path target for `X^4 + 1`. The declared cost
model is the same constant `n + 1` singleton bound, with `none` distinguished so
fast-path misses remain visible until the BHKS completion work succeeds. -/
setup_benchmark runFactorFastAdvX4Plus1Checksum n => n + 1
  with prep := prepAdvX4Plus1
  where {
    paramFloor := 0
    paramCeiling := 0
    paramSchedule := .custom #[0]
    maxSecondsPerCall := 4.0
    targetInnerNanos := 100000000
    signalFloorMultiplier := 1.0
  }

/- Singleton HO-2 adversarial target: `(X^2 - 2)(X^2 - 3)`. The declared cost
model is `n + 1`, a constant bound; at the pinned fixture prime this splits into
four local linear factors and recombines into two true quadratics. -/
setup_benchmark runFactorAdvQuadSqrt2Sqrt3Checksum n => n + 1
  with prep := prepAdvQuadSqrt2Sqrt3
  where {
    paramFloor := 0
    paramCeiling := 0
    paramSchedule := .custom #[0]
    maxSecondsPerCall := 4.0
    targetInnerNanos := 100000000
    signalFloorMultiplier := 1.0
  }

/- Singleton HO-2 adversarial fast-path target for `(X^2 - 2)(X^2 - 3)`. The
declared cost model is the same constant `n + 1` singleton bound. -/
setup_benchmark runFactorFastAdvQuadSqrt2Sqrt3Checksum n => n + 1
  with prep := prepAdvQuadSqrt2Sqrt3
  where {
    paramFloor := 0
    paramCeiling := 0
    paramSchedule := .custom #[0]
    maxSecondsPerCall := 4.0
    targetInnerNanos := 100000000
    signalFloorMultiplier := 1.0
  }

/- Singleton HO-2 adversarial target: `Phi_15`. The declared cost model is
`n + 1`, a constant bound for the pinned singleton schedule; the degree-eight
cyclotomic case exercises the recombination hot path without a wider matrix. -/
setup_benchmark runFactorAdvPhi15Checksum n => n + 1
  with prep := prepAdvPhi15
  where {
    paramFloor := 0
    paramCeiling := 0
    paramSchedule := .custom #[0]
    maxSecondsPerCall := 6.0
    targetInnerNanos := 100000000
    signalFloorMultiplier := 1.0
  }

/- Singleton HO-2 adversarial fast-path target for `Phi_15`. The declared cost
model is the same constant `n + 1` singleton bound. -/
setup_benchmark runFactorFastAdvPhi15Checksum n => n + 1
  with prep := prepAdvPhi15
  where {
    paramFloor := 0
    paramCeiling := 0
    paramSchedule := .custom #[0]
    maxSecondsPerCall := 6.0
    targetInnerNanos := 100000000
    signalFloorMultiplier := 1.0
  }

end BerlekampZassenhausBench
end Hex

def main (args : List String) : IO UInt32 :=
  LeanBench.Cli.dispatch args
