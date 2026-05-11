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
* HO-2 adversarial polynomial constants plus singleton `factor` targets and
  smoke-safe fast-path setup targets for the adversarial recombination surfaces.
  Full `factorFast` on `X^4 + 1` and `Phi_15` currently exceeds the smoke
  verifier's one-call budget, so those two fast-path registrations record the
  public precision cap and pinned modular split profile instead of falling
  through the public `factor` combinator.
* `runAdvSwinnertonDyerSD3ModularSplitChecksum`: the pinned SD3 modular split
  profile, keeping the worst-case recombination shape visible without running
  the currently smoke-intractable full integer factorization in `verify`.

Degree/height registrations:

* `runFactorDegreeHeightChecksum`: public `factor` over split inputs with
  encoded degree and root-height regimes.
* `runFactorFastDegreeHeightChecksum`: CLD fast path on the same regimes,
  preserving `none`.
* `runFactorSlowDegreeHeightChecksum`: bounded slow-path diagnostic on the
  smallest generated regimes.
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

/-- Prepared split input whose single parameter encodes degree and height. -/
structure DegreeHeightInput where
  degree : Nat
  height : Nat
  poly : ZPoly
  deriving Hashable

/-- Encoding scale for benchmark parameters that vary degree and height. -/
def degreeHeightParamScale : Nat :=
  1000

/-- Encode a degree/root-height pair as lean-bench's single `Nat` parameter. -/
def encodeDegreeHeightParam (degree height : Nat) : Nat :=
  degree * degreeHeightParamScale + height

/-- Decode the degree component from an encoded degree/height parameter. -/
def degreeHeightDegree (param : Nat) : Nat :=
  param / degreeHeightParamScale

/-- Decode the root-height component from an encoded degree/height parameter. -/
def degreeHeightHeight (param : Nat) : Nat :=
  param % degreeHeightParamScale

/-- Deterministic split family with roots scaled by the requested height. -/
def splitDegreeHeightInput (degree height : Nat) : ZPoly :=
  let scale := Int.ofNat (height + 1)
  (Array.range degree).foldl
    (fun acc i => acc * linearZFactor (scale * Int.ofNat (i + 1)))
    (1 : ZPoly)

/-- Per-parameter fixture for the ordinary degree/height benchmark matrix. -/
def prepDegreeHeightInput (param : Nat) : DegreeHeightInput :=
  let degree := degreeHeightDegree param
  let height := degreeHeightHeight param
  { degree
    height
    poly := splitDegreeHeightInput degree height }

/-- Encoded low/medium/higher degree and root-height regimes for the BZ suite. -/
def degreeHeightSchedule : Array Nat :=
  #[encodeDegreeHeightParam 3 2,
    encodeDegreeHeightParam 4 2,
    encodeDegreeHeightParam 4 8,
    encodeDegreeHeightParam 5 8,
    encodeDegreeHeightParam 6 32]

/-- Bounded slow-path subset of the degree/height schedule. -/
def slowDegreeHeightSchedule : Array Nat :=
  #[encodeDegreeHeightParam 2 2,
    encodeDegreeHeightParam 3 8,
    encodeDegreeHeightParam 4 8]

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

/-- Stable checksum for modular factor-degree profiles. -/
def checksumNatArray (xs : Array Nat) : UInt64 :=
  xs.foldl (fun acc x => mixHash acc (hash x)) 0

/-- Stable checksum for optional fast-path factorization results. -/
def checksumOptionFactorization : Option Factorization → UInt64
  | none => 0
  | some φ => mixHash 1 (checksumFactorization φ)

/-- Stable checksum for optional modular factor-degree profiles. -/
def checksumOptionNatArray : Option (Array Nat) → UInt64
  | none => 0
  | some xs => mixHash 1 (checksumNatArray xs)

/--
Stable checksum for smoke-safe fast-path setup on an adversarial singleton.

This deliberately does not call the public fallback combinator: the checksum
records the precision cap that `factorFast` would use and the pinned local split
shape feeding recombination. It keeps the hard fast-path cases visible to
`list` / `verify` while the full `factorFast` calls remain too expensive for
smoke verification.
-/
def checksumFastPathSetup (f : ZPoly) (p : Nat) : UInt64 :=
  mixHash (hash (factorFastPrecisionCap f)) (checksumOptionNatArray (modularFactorDegreesAt? f p))

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

/-- Singleton benchmark target: fast-path setup on `X^4 + 1`, pinned at `p = 5`. -/
@[noinline]
def runFactorFastSetupAdvX4Plus1Checksum (f : ZPoly) : UInt64 :=
  checksumFastPathSetup f 5

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

/-- Singleton benchmark target: fast-path setup on `Phi_15`, pinned at `p = 31`. -/
@[noinline]
def runFactorFastSetupAdvPhi15Checksum (f : ZPoly) : UInt64 :=
  checksumFastPathSetup f 31

/--
Singleton benchmark target: pinned modular split profile for Swinnerton-Dyer
`SD_3` at `p = 71`, where the degree-eight integer polynomial splits into
eight local linear factors.
-/
@[noinline]
def runAdvSwinnertonDyerSD3ModularSplitChecksum (f : ZPoly) : UInt64 :=
  checksumOptionNatArray (modularFactorDegreesAt? f 71)

def prepAdvX4Plus1 (_ : Nat) : ZPoly :=
  advX4Plus1

def prepAdvQuadSqrt2Sqrt3 (_ : Nat) : ZPoly :=
  advQuadSqrt2Sqrt3

def prepAdvSwinnertonDyerSD3 (_ : Nat) : ZPoly :=
  advSwinnertonDyerSD3

def prepAdvPhi15 (_ : Nat) : ZPoly :=
  advPhi15

/-- Benchmark target: public combinator over the degree/height matrix. -/
def runFactorDegreeHeightChecksum (input : DegreeHeightInput) : UInt64 :=
  checksumFactorization (factor input.poly)

/-- Benchmark target: CLD fast path over the degree/height matrix. -/
def runFactorFastDegreeHeightChecksum (input : DegreeHeightInput) : UInt64 :=
  checksumOptionFactorization (factorFast input.poly)

/-- Benchmark target: bounded slow-path diagnostic over small degree/height cases. -/
def runFactorSlowDegreeHeightChecksum (input : DegreeHeightInput) : UInt64 :=
  checksumFactorization (factorSlow input.poly)

/-- HO-3's classical-arithmetic BHKS model over the smoke degree parameter. -/
def bzClassicalSmokeComplexity (n : Nat) : Nat :=
  n ^ 9 + n ^ 7 * (Nat.log2 (n + 2)) ^ 2

/-- HO-3's classical-arithmetic BHKS model over encoded degree/height inputs. -/
def bzClassicalDegreeHeightComplexity (param : Nat) : Nat :=
  let n := degreeHeightDegree param
  let h := Nat.log2 (degreeHeightHeight param + 2)
  n ^ 9 + n ^ 7 * h ^ 2

/-- Exponential slow-path model over encoded degree/height inputs. -/
def bzSlowDegreeHeightComplexity (param : Nat) : Nat :=
  let n := degreeHeightDegree param
  2 ^ n * bzClassicalDegreeHeightComplexity param

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

/-
This registration varies both public input degree and root-height through an
encoded `(degree, height)` parameter. The declared model is the classical BHKS
integer-polynomial factorization bound `O(n^9 + n^7 h^2)`, with `h` represented
by `log2(height + 2)` for the deterministic split family.
-/
setup_benchmark runFactorDegreeHeightChecksum param => bzClassicalDegreeHeightComplexity param
  with prep := prepDegreeHeightInput
  where {
    paramFloor := encodeDegreeHeightParam 3 2
    paramCeiling := encodeDegreeHeightParam 6 32
    paramSchedule := .custom degreeHeightSchedule
    maxSecondsPerCall := 4.0
    targetInnerNanos := 100000000
    signalFloorMultiplier := 1.0
  }

/- Singleton HO-2 adversarial fast-path setup target for `X^4 + 1`. Full
`factorFast` exceeds the smoke verifier's one-call budget; the declared cost
model is the constant `n + 1` singleton bound for the pinned `n = 0` schedule.
This registration narrows the measured operation to the public fast-path
precision cap plus the pinned `p = 5` modular split profile. The public fallback
is not called, so a future `factorFast = none` result is not hidden by `factor`. -/
setup_benchmark runFactorFastSetupAdvX4Plus1Checksum n => n + 1
  with prep := prepAdvX4Plus1
  where {
    paramFloor := 0
    paramCeiling := 0
    paramSchedule := .custom #[0]
    maxSecondsPerCall := 4.0
    targetInnerNanos := 100000000
    signalFloorMultiplier := 1.0
  }

/-
The CLD fast path is measured on the same encoded degree/height matrix as the
public combinator. Successful fast-path runs pay the same textbook dense
arithmetic, lifting, and recombination bound `O(n^9 + n^7 h^2)`; `none`
remains a distinct checksum outcome.
-/
setup_benchmark runFactorFastDegreeHeightChecksum param => bzClassicalDegreeHeightComplexity param
  with prep := prepDegreeHeightInput
  where {
    paramFloor := encodeDegreeHeightParam 3 2
    paramCeiling := encodeDegreeHeightParam 6 32
    paramSchedule := .custom degreeHeightSchedule
    maxSecondsPerCall := 4.0
    targetInnerNanos := 100000000
    signalFloorMultiplier := 1.0
  }

/-
The slow diagnostic intentionally uses only the smallest degree/height subset:
exhaustive recombination has an exponential dependence on the number of local
factors, so the declared complexity is `O(2^n * (n^9 + n^7 h^2))`.
-/
setup_benchmark runFactorSlowDegreeHeightChecksum param => bzSlowDegreeHeightComplexity param
  with prep := prepDegreeHeightInput
  where {
    paramFloor := encodeDegreeHeightParam 2 2
    paramCeiling := encodeDegreeHeightParam 4 8
    paramSchedule := .custom slowDegreeHeightSchedule
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

/- Singleton HO-2 adversarial fast-path setup target for `Phi_15`. The declared
cost model is the constant `n + 1` singleton bound for the pinned `n = 0`
schedule. This smoke registration keeps the fast-path precision cap and pinned
`p = 31` eight-linear split visible without routing through the public fallback
combinator. -/
setup_benchmark runFactorFastSetupAdvPhi15Checksum n => n + 1
  with prep := prepAdvPhi15
  where {
    paramFloor := 0
    paramCeiling := 0
    paramSchedule := .custom #[0]
    maxSecondsPerCall := 6.0
    targetInnerNanos := 100000000
    signalFloorMultiplier := 1.0
  }

/-
Singleton HO-2 adversarial shape: Swinnerton-Dyer `SD_3`. Full `factor` and
`factorFast` on this degree-eight worst-case recombination input currently
exceed the smoke `verify` budget, so this reduced registration pins the same
canonical polynomial at the same conformance prime and records its eight-linear
modular split profile. The constant model is intentional: the schedule fixes
one canonical shape while keeping SD3 visible to `list` and `verify` until a
scientific-only full factorization registration is affordable.
-/
setup_benchmark runAdvSwinnertonDyerSD3ModularSplitChecksum n => n + 1
  with prep := prepAdvSwinnertonDyerSD3
  where {
    paramFloor := 0
    paramCeiling := 0
    paramSchedule := .custom #[0]
    maxSecondsPerCall := 4.0
    targetInnerNanos := 100000000
    signalFloorMultiplier := 1.0
  }

end BerlekampZassenhausBench
end Hex

def main (args : List String) : IO UInt32 :=
  LeanBench.Cli.dispatch args
