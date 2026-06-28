import HexBerlekampZassenhaus.Basic
import Hex.BenchOracle.Flint
import Lean.Data.Json
import LeanBench

/-!
Phase 4 benchmark registrations for `hex-berlekamp-zassenhaus`.

This module is the Phase 4 benchmark root for the BZ factorization API. It
covers the public combinator, the proof-facing fast path, the exhaustive slow
path, the (degree, height) matrix, the (degree, height, precision,
local-factor-count) fast-path setup surface, a shared-domain `compare` family,
and the HO-2 adversarial recombination shapes. Comparator ratios and the
headline performance report still depend on the scheduled-hardware runs and
report reconciliation described in `SPEC/benchmarking.md`.

The registration names are intentionally stable: CI and scheduled timing runs
refer to these case names when checking that the benchmark harness still covers
the public BZ API surface. Each `setup_benchmark` has an adjacent cost-model
derivation comment.

Each family below is either a *scientific* schedule (verdict-eligible scaling)
or a *fast* schedule (small fixed sweep used by `list` / `verify`); the
per-target comment annotates which one.

Split-family registrations (`prep := smokeInput`):

* `runFactorChecksum`: public `factor` combinator on split inputs over the
  scientific degree schedule
  `splitScientificSchedule = #[2, 3, 4, 5, 8, 10, 12, 14, 16, 18, 20, 22, 24]`.
* `runFactorFastChecksum`: CLD fast path on the same scientific schedule,
  preserving `none`.
* `runFactorSlowChecksum`: exhaustive backstop on the fast schedule
  `smokeSchedule = #[1, 2, 3, 4]`.
* `runFactorFallbackProbeChecksum`: public `factor` combinator on the explicit
  cascade-trigger split-degree schedule `fallbackProbeSchedule`.

Shared compare domain (`prep := smokeInput`, `paramSchedule := smokeSchedule`):

* `runFactorCompareChecksum` vs `runFactorSlowCompareChecksum` checks the
  public fallback factorization against the exhaustive slow path.
* `runFactorFastCompareChecksum` joins the same domain and returns the same
  factorization checksum only when `factorFast` succeeds; a fast-path miss is
  a distinct input-dependent checksum, so `compare` exposes rather than hides
  `none`.

Degree/height registrations (`prep := prepDegreeHeightInput`):

* `runFactorDegreeHeightChecksum`: public `factor` over the scientific encoded
  `degreeHeightSchedule`.
* `runFactorFastDegreeHeightChecksum`: CLD fast path on the same schedule,
  preserving `none`.
* `runFactorSlowDegreeHeightChecksum`: bounded slow-path diagnostic on the
  smallest-completing encoded subset `slowDegreeHeightSchedule`.

Precision/local-factor registration (`prep := prepPrecisionLocalInput`):

* `runFastPathPrecisionLocalChecksum`: `verify`-budget-safe fast-path setup
  over encoded degree, root-height, Hensel-precision, and local-factor-count
  regimes.

HO-2 adversarial singletons (each pinned at `paramSchedule := #[0]`):

* `runFactorAdvX4Plus1Checksum`, `runFactorAdvQuadSqrt2Sqrt3Checksum`,
  `runFactorAdvPhi15Checksum`: full public `factor` on the named adversarial
  input.
* `runFactorFastSetupAdvX4Plus1Checksum`,
  `runFactorFastSetupAdvPhi15Checksum`: fast-path *setup* only — these record
  the public precision cap and pinned modular split profile, because the full
  `factorFast` call exceeds the verifier's one-call budget on these inputs.
* `runFactorFastAdvQuadSqrt2Sqrt3Checksum`: full `factorFast` on the quadratic
  product (cheap enough to run in `verify`), preserving `none`.
* `runAdvSwinnertonDyerSD3ModularSplitChecksum`: pinned modular split profile
  for SD3 at the conformance prime, keeping the worst-case recombination
  shape visible without running the full integer factorization (which exceeds
  the `verify` budget).

Gating external comparator:

* `runIsabelleFactorChecksum`: verified Isabelle/AFP
  `Berlekamp_Zassenhaus.factor_int_poly`, exported to Haskell and compiled by
  `scripts/oracle/setup_bz_isabelle.sh`. The comparator process is persistent:
  one line-delimited JSON request `{"coeffs":[...]}` is sent per call, with
  coefficients in ascending degree order, and the reply is
  `{"ok":true,"result":{"scalar":c,"factors":[{"coeffs":[...],"multiplicity":m},...]}}`.
  The Lean bench process caches the child and reuses it across requests.
  Before the first timed request, a Lean-side guard checks `(x-1)(x-2)`,
  `Phi_5`, and `(x^2-2)(x^2-3)` by comparing canonical factor multisets
  against `factor`; factor order is deliberately ignored.
* `runIsabelleFactorBaselineChecksum`: the same persistent protocol on the
  constant polynomial `1`. Ratio reports subtract this trivial-input baseline
  from `runIsabelleFactorChecksum` before computing `hex/isabelle`.
  These fixed comparator targets are tagged `scheduled-hardware`; this bench
  executable's default `verify` command skips that tag so CI does not build or
  run the AFP comparator.
* `runIsabelleSplitN{2,3,4,5}Checksum`,
  `runIsabelleDegreeHeight{D}x{H}Checksum`: per-rung verified-Isabelle pairs
  for the parametric split-family and degree/height Lean targets, used to
  build the `hex/isabelle` scaling ladders in
  `reports/hex-berlekamp-zassenhaus-performance.md`.
* `runIsabelleAdv{X4Plus1,Phi15,SwinnertonDyerSD3}Checksum`: per-input
  verified-Isabelle pairs for the HO-2 adversarial singletons (one new
  registration per distinct singleton input not already covered by
  `runIsabelleFactorChecksum`).
* `runIsabelleFallbackProbeN{11,12,13,15,18,22,24}Checksum`: per-rung
  verified-Isabelle pairs for the cascade-trigger fallback-probe schedule. The
  `expectedHash` field is `none` on these registrations to keep elaboration off
  the cascade-affected Lean `factor` call path; see the per-`def` doc comment.
* `runIsabellePrecisionLocalRung{1..6}Checksum`: per-rung verified-Isabelle
  pairs for the precision/local-factor schedule. The Lean target measures
  fast-path setup (multifactor lifting + modular split profile) rather than
  full factorisation, so the resulting `Lean_setup / Isabelle_full` ratio is
  asymmetric and reported as a lower bound on the implied full-factor ratio;
  see the per-`def` doc comment and
  `reports/hex-berlekamp-zassenhaus-performance.md` §"Precision-local
  asymmetric ratio ladder".
-/

namespace Hex
namespace BerlekampZassenhausBench

open Lean (Json)

private instance benchBoundsThirtyOne : ZMod64.Bounds 31 := ⟨by decide, by decide⟩

instance : Hashable ZPoly where
  hash p := hash p.toArray

/-- Deterministic monic integer linear factor `X - root`. -/
def linearZFactor (root : Int) : ZPoly :=
  DensePoly.ofCoeffs #[-root, 1]

/--
Deterministic split integer-polynomial family. Consumed both as the fast
sweep (`smokeSchedule = #[1, 2, 3, 4]`, used by the slow target and the
`compare` registrations) and as the scientific schedule for the public and
fast-path targets
(`splitScientificSchedule = #[2, 3, 4, 5, 8, 10, 12, 14, 16, 18, 20, 22, 24]`).
-/
def smokeInput (n : Nat) : ZPoly :=
  (Array.range (n + 1)).foldl
    (fun acc i => acc * linearZFactor (Int.ofNat (i + 1)))
    (1 : ZPoly)

/-- Fast schedule used by the slow target and the shared-domain `compare` family. -/
def smokeSchedule : Array Nat :=
  #[1, 2, 3, 4]

/-- Scientific split-family schedule for public and proof-facing fast factoring. -/
def splitScientificSchedule : Array Nat :=
  #[2, 3, 4, 5, 8, 10, 12, 14, 16, 18, 20, 22, 24]

/--
Explicit fallback-prime probe family. Here the benchmark parameter is the split
degree itself, so `prepFallbackProbeInput 11` is `(X-1)(X-2)...(X-11)`.
-/
def prepFallbackProbeInput (degree : Nat) : ZPoly :=
  (Array.range degree).foldl
    (fun acc i => acc * linearZFactor (Int.ofNat (i + 1)))
    (1 : ZPoly)

/-- Cascade-trigger split-degree schedule from the BZ-vs-Isabelle post-mortem. -/
def fallbackProbeSchedule : Array Nat :=
  #[11, 12, 13, 15, 18, 22, 24]

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

/--
Prepared input for the Phase 4 fast-path setup surface. The encoded parameter
tracks input degree, root height, requested Hensel precision, and the number of
mod-`31` local factors separately, while the timed target avoids full
`factorFast` on adversarial cases.
-/
structure PrecisionLocalInput where
  degree : Nat
  height : Nat
  precision : Nat
  localFactorCount : Nat
  poly : ZPoly
  localFactors : Array ZPoly
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
  #[encodeDegreeHeightParam 1 2,
    encodeDegreeHeightParam 2 2,
    encodeDegreeHeightParam 3 8]

/-- Encoding scale for benchmark parameters with four small natural axes. -/
def precisionLocalParamScale : Nat :=
  1000

/--
Encode `(degree, height, precision, localFactorCount)` as lean-bench's single
`Nat` parameter.
-/
def encodePrecisionLocalParam
    (degree height precision localFactorCount : Nat) : Nat :=
  (((degree * precisionLocalParamScale + height) * precisionLocalParamScale
      + precision) * precisionLocalParamScale) + localFactorCount

/-- Decode the degree component from an encoded precision/local-factor parameter. -/
def precisionLocalDegree (param : Nat) : Nat :=
  param / (precisionLocalParamScale * precisionLocalParamScale * precisionLocalParamScale)

/-- Decode the root-height component from an encoded precision/local-factor parameter. -/
def precisionLocalHeight (param : Nat) : Nat :=
  (param / (precisionLocalParamScale * precisionLocalParamScale)) % precisionLocalParamScale

/-- Decode the requested Hensel precision component. -/
def precisionLocalPrecision (param : Nat) : Nat :=
  (param / precisionLocalParamScale) % precisionLocalParamScale

/-- Decode the local-factor-count component. -/
def precisionLocalFactorCount (param : Nat) : Nat :=
  param % precisionLocalParamScale

/--
Scientific schedule for the fast-path setup surface. The cases vary Hensel
precision and the number of local factors while keeping every polynomial split
over the supported benchmark prime `31`.
-/
def precisionLocalSchedule : Array Nat :=
  #[encodePrecisionLocalParam 2 2 4 2,
    encodePrecisionLocalParam 2 2 16 2,
    encodePrecisionLocalParam 4 4 16 4,
    encodePrecisionLocalParam 4 16 64 4,
    encodePrecisionLocalParam 6 16 64 6,
    encodePrecisionLocalParam 8 32 128 8]

/-- Deterministic local linear factors for the precision/local-factor matrix. -/
def splitPrecisionLocalFactors (localFactorCount height : Nat) : Array ZPoly :=
  let scale := Int.ofNat (height + 1)
  (Array.range localFactorCount).map fun i =>
    linearZFactor (scale * Int.ofNat (i + 1))

/-- Per-parameter fixture for the precision/local-factor benchmark matrix. -/
def prepPrecisionLocalInput (param : Nat) : PrecisionLocalInput :=
  let degree := precisionLocalDegree param
  let height := precisionLocalHeight param
  let precision := precisionLocalPrecision param
  let localFactorCount := precisionLocalFactorCount param
  let localFactors := splitPrecisionLocalFactors localFactorCount height
  { degree
    height
    precision
    localFactorCount
    poly := Array.polyProduct localFactors
    localFactors }

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

def intListLexLe : List Int → List Int → Bool
  | [], _ => true
  | _ :: _, [] => false
  | a :: as, b :: bs =>
      if a < b then true
      else if b < a then false
      else intListLexLe as bs

def canonicalFactorLe (a b : List Int × Nat) : Bool :=
  if a.1 = b.1 then
    a.2 ≤ b.2
  else
    intListLexLe a.1 b.1

def canonicalFactorArray (φ : Factorization) : Array (List Int × Nat) :=
  (φ.factors.map fun factor => (factor.1.toArray.toList, factor.2)).qsort canonicalFactorLe

def checksumCanonicalFactorArray (factors : Array (List Int × Nat)) : UInt64 :=
  factors.foldl
    (fun acc factor =>
      let coeffHash := factor.1.foldl (fun h c => mixHash h (hash c)) 0
      mixHash acc (mixHash coeffHash (hash factor.2)))
    0

def checksumCanonicalFactorization (scalar : Int) (factors : Array (List Int × Nat)) :
    UInt64 :=
  mixHash (hash scalar) (checksumCanonicalFactorArray factors)

def checksumCanonicalLeanFactorization (φ : Factorization) : UInt64 :=
  checksumCanonicalFactorization φ.scalar (canonicalFactorArray φ)

/-- Stable checksum for modular factor-degree profiles. -/
def checksumNatArray (xs : Array Nat) : UInt64 :=
  xs.foldl (fun acc x => mixHash acc (hash x)) 0

/-- Stable checksum for ordered integer-polynomial arrays. -/
def checksumZPolyArray (xs : Array ZPoly) : UInt64 :=
  xs.foldl (fun acc f => mixHash acc (checksumZPoly f)) 0

/-- Stable checksum for optional fast-path factorization results. -/
def checksumOptionFactorization : Option Factorization → UInt64
  | none => 0
  | some φ => mixHash 1 (checksumFactorization φ)

/-- Stable checksum for optional modular factor-degree profiles. -/
def checksumOptionNatArray : Option (Array Nat) → UInt64
  | none => 0
  | some xs => mixHash 1 (checksumNatArray xs)

/--
Stable checksum for `verify`-budget-safe fast-path setup on an adversarial
singleton.

This deliberately does not call the public fallback combinator: the checksum
records the precision cap that `factorFast` would use and the pinned local split
shape feeding recombination. It keeps the hard fast-path cases visible to
`list` / `verify` while the full `factorFast` calls remain too expensive for
the `verify` budget.
-/
def checksumFastPathSetup (f : ZPoly) (p : Nat) : UInt64 :=
  mixHash (hash (factorFastPrecisionCap f)) (checksumOptionNatArray (modularFactorDegreesAt? f p))

/-- Benchmark target: public fast-with-slow-fallback factorization. -/
def runFactorChecksum (f : ZPoly) : UInt64 :=
  checksumFactorization (factor f)

/-- Benchmark target: public factorization on explicit fallback-prime probes. -/
@[noinline]
def runFactorFallbackProbeChecksum (f : ZPoly) : UInt64 :=
  runFactorChecksum f

/-- Benchmark target: public CLD fast path, preserving fast-path misses. -/
def runFactorFastChecksum (f : ZPoly) : UInt64 :=
  checksumOptionFactorization (factorFast f)

/-- Benchmark target: public exhaustive slow backstop. -/
def runFactorSlowChecksum (f : ZPoly) : UInt64 :=
  checksumFactorization (factorSlowTrial f)

/-- Shared-domain compare target: public factorization on deterministic splits. -/
def runFactorCompareChecksum (f : ZPoly) : UInt64 :=
  checksumFactorization (factor f)

/-- Shared-domain compare target: exhaustive slow factorization on deterministic splits. -/
def runFactorSlowCompareChecksum (f : ZPoly) : UInt64 :=
  checksumFactorization (factorSlowTrial f)

/--
Shared-domain compare target: fast factorization on deterministic splits.

When `factorFast` misses, return an input-dependent sentinel instead of routing
through the public fallback. A `compare` run therefore reports divergence if the
fast path stops producing the same semantic result on this domain.
-/
def runFactorFastCompareChecksum (f : ZPoly) : UInt64 :=
  match factorFast f with
  | some φ => checksumFactorization φ
  | none => mixHash 0xffffffffffffffff (checksumZPoly f)

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

/-- Constant prep returning the `X^4 + 1` adversarial fixture for the pinned singleton schedule. -/
def prepAdvX4Plus1 (_ : Nat) : ZPoly :=
  advX4Plus1

/-- Constant prep returning the `(X^2 - 2)(X^2 - 3)` adversarial fixture. -/
def prepAdvQuadSqrt2Sqrt3 (_ : Nat) : ZPoly :=
  advQuadSqrt2Sqrt3

/-- Constant prep returning the Swinnerton-Dyer `SD_3` adversarial fixture. -/
def prepAdvSwinnertonDyerSD3 (_ : Nat) : ZPoly :=
  advSwinnertonDyerSD3

/-- Constant prep returning the cyclotomic `Phi_15` adversarial fixture. -/
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
  checksumFactorization (factorSlowTrial input.poly)

/--
Benchmark target: `verify`-budget-safe fast-path setup over encoded degree,
height, Hensel precision, and local-factor-count axes.
-/
def runFastPathPrecisionLocalChecksum (input : PrecisionLocalInput) : UInt64 :=
  let lifted :=
    ZPoly.multifactorLiftQuadratic 31 input.precision input.poly input.localFactors
  let splitProfile := modularFactorDegreesAt? input.poly 31
  mixHash (hash input.precision) <|
    mixHash (hash input.localFactorCount) <|
      mixHash (checksumZPolyArray lifted) <|
        mixHash (hash (factorFastPrecisionCap input.poly)) (checksumOptionNatArray splitProfile)

initialize isabelleBZBinaryRef : IO.Ref (Option String) ← IO.mkRef none

initialize isabelleBZChildRef :
    IO.Ref (Option Hex.BenchOracle.Flint.PersistentComparator) ← IO.mkRef none

initialize isabelleBZCrossCheckRef : IO.Ref Bool ← IO.mkRef false

def checkedProcessOutput (cmd : String) (args : Array String := #[]) : IO String := do
  let out ← IO.Process.output { cmd := cmd, args := args }
  if out.exitCode != 0 then
    throw <| IO.userError
      s!"process failed ({cmd}):\nstdout:\n{out.stdout}\nstderr:\n{out.stderr}"
  return out.stdout.trimAscii.toString

def resolveIsabelleBZBinary : IO String := do
  if let some cached ← isabelleBZBinaryRef.get then
    return cached
  let path ←
    match (← IO.getEnv "HEX_BZ_ISABELLE") with
    | some p => pure p
    | none => checkedProcessOutput "scripts/oracle/setup_bz_isabelle.sh"
  isabelleBZBinaryRef.set (some path)
  return path

def resolveIsabelleBZChild : IO Hex.BenchOracle.Flint.PersistentComparator := do
  if let some ch ← isabelleBZChildRef.get then
    return ch
  let binary ← resolveIsabelleBZBinary
  let ch ← Hex.BenchOracle.Flint.PersistentComparator.spawn binary
  isabelleBZChildRef.set (some ch)
  return ch

def requestIsabelleBZLineWithRetry (request : String) : Nat → IO String
  | 0 => do
    let reply ← (← resolveIsabelleBZChild).requestLine request
    if reply.isEmpty then
      throw <| IO.userError "bz_isabelle closed stdout before replying"
    return reply
  | Nat.succ remaining => do
    try
      let reply ← (← resolveIsabelleBZChild).requestLine request
      if reply.isEmpty then
        throw <| IO.userError "bz_isabelle closed stdout before replying"
      return reply
    catch _ =>
      isabelleBZChildRef.set none
      requestIsabelleBZLineWithRetry request remaining

def zpolyToIsabelleRequest (f : ZPoly) : Json :=
  Json.mkObj [("coeffs", Hex.BenchOracle.Flint.intsToJson f.toArray.toList)]

def parseIsabelleBZFactors (j : Json) : IO (Array (List Int × Nat)) := do
  let arr ←
    match j.getArr? with
    | Except.ok a => pure a
    | Except.error msg =>
        throw <| IO.userError s!"bz_isabelle factors field was not an array: {msg}"
  let mut out : Array (List Int × Nat) := Array.mkEmpty arr.size
  for entry in arr do
    let coeffsJson ←
      match entry.getObjVal? "coeffs" with
      | Except.ok c => pure c
      | Except.error msg =>
          throw <| IO.userError s!"bz_isabelle factor missing coeffs: {msg}"
    let coeffs ← Hex.BenchOracle.Flint.jsonToInts coeffsJson
    let multiplicityJson ←
      match entry.getObjVal? "multiplicity" with
      | Except.ok m => pure m
      | Except.error msg =>
          throw <| IO.userError s!"bz_isabelle factor missing multiplicity: {msg}"
    let multiplicity ←
      match multiplicityJson.getNat? with
      | Except.ok m => pure m
      | Except.error msg =>
          throw <| IO.userError s!"bz_isabelle factor multiplicity invalid: {msg}"
    out := out.push (coeffs, multiplicity)
  return out.qsort canonicalFactorLe

def requestIsabelleBZFactorizationRaw (f : ZPoly) : IO (Int × Array (List Int × Nat)) := do
  let reply ← requestIsabelleBZLineWithRetry (zpolyToIsabelleRequest f).compress 1
  let json ←
    match Json.parse reply with
    | Except.ok j => pure j
    | Except.error msg =>
        throw <| IO.userError s!"bz_isabelle reply was not valid JSON: {msg}; reply: {reply}"
  match json.getObjValAs? Bool "ok" with
  | Except.ok true =>
      let result ←
        match json.getObjVal? "result" with
        | Except.ok r => pure r
        | Except.error msg =>
            throw <| IO.userError s!"bz_isabelle success missing result: {msg}"
      let scalar ←
        match result.getObjVal? "scalar" with
        | Except.ok scalarJson =>
          match scalarJson.getInt? with
          | Except.ok n => pure n
          | Except.error msg =>
              throw <| IO.userError s!"bz_isabelle scalar invalid: {msg}"
        | Except.error msg =>
            throw <| IO.userError s!"bz_isabelle result missing scalar: {msg}"
      let factorsJson ←
        match result.getObjVal? "factors" with
        | Except.ok fs => pure fs
        | Except.error msg =>
            throw <| IO.userError s!"bz_isabelle result missing factors: {msg}"
      let factors ← parseIsabelleBZFactors factorsJson
      return (scalar, factors)
  | Except.ok false =>
      let err := (json.getObjValAs? String "error").toOption.getD "(no error message)"
      throw <| IO.userError s!"bz_isabelle: {err}"
  | Except.error msg =>
      throw <| IO.userError s!"bz_isabelle reply missing/non-bool ok: {msg}; reply: {reply}"

def isabelleFixtureInputs : List ZPoly :=
  [smokeInput 1, DensePoly.ofCoeffs #[1, 1, 1, 1, 1], advQuadSqrt2Sqrt3,
    smokeInput 2, smokeInput 3, smokeInput 4, smokeInput 5]

def ensureIsabelleBZCrossCheck : IO Unit := do
  if (← isabelleBZCrossCheckRef.get) then
    return ()
  for f in isabelleFixtureInputs do
    let leanChecksum := checksumCanonicalLeanFactorization (factor f)
    let (scalar, factors) ← requestIsabelleBZFactorizationRaw f
    let isabelleChecksum := checksumCanonicalFactorization scalar factors
    if leanChecksum != isabelleChecksum then
      throw <| IO.userError (
        s!"bz_isabelle cross-check failed for coeffs={f.toArray.toList}: " ++
        s!"lean={leanChecksum}, isabelle={isabelleChecksum}")
  isabelleBZCrossCheckRef.set true

def requestIsabelleBZFactorization (f : ZPoly) : IO (Int × Array (List Int × Nat)) := do
  ensureIsabelleBZCrossCheck
  requestIsabelleBZFactorizationRaw f

/-- Fixed Lean-side target matching the Isabelle comparator's canonical input. -/
def runFactorIsabelleDomainChecksum : Unit → IO UInt64 := fun _ => do
  return checksumCanonicalLeanFactorization (factor advQuadSqrt2Sqrt3)

/-- Fixed verified-Isabelle BZ comparator target on the same canonical input. -/
def runIsabelleFactorChecksum : Unit → IO UInt64 := fun _ => do
  let (scalar, factors) ← requestIsabelleBZFactorization advQuadSqrt2Sqrt3
  return checksumCanonicalFactorization scalar factors

/-- Fixed verified-Isabelle trivial-input baseline for process/protocol overhead. -/
def runIsabelleFactorBaselineChecksum : Unit → IO UInt64 := fun _ => do
  let (scalar, factors) ← requestIsabelleBZFactorizationRaw (1 : ZPoly)
  return checksumCanonicalFactorization scalar factors

/--
Per-rung verified-Isabelle BZ comparator targets on the deterministic split
family `smokeInput n` for `n = 2, 3, 4, 5`. Each pairs with the corresponding
rung of the parametric Lean `runFactorChecksum` registration to yield a
`hex/isabelle` ratio at that rung; together they form the scaling ladder
required by `SPEC/Libraries/hex-berlekamp-zassenhaus.md §"External
comparators"` headline-trend reporting.
-/
def runIsabelleSplitN2Checksum : Unit → IO UInt64 := fun _ => do
  let (scalar, factors) ← requestIsabelleBZFactorization (smokeInput 2)
  return checksumCanonicalFactorization scalar factors

def runIsabelleSplitN3Checksum : Unit → IO UInt64 := fun _ => do
  let (scalar, factors) ← requestIsabelleBZFactorization (smokeInput 3)
  return checksumCanonicalFactorization scalar factors

def runIsabelleSplitN4Checksum : Unit → IO UInt64 := fun _ => do
  let (scalar, factors) ← requestIsabelleBZFactorization (smokeInput 4)
  return checksumCanonicalFactorization scalar factors

def runIsabelleSplitN5Checksum : Unit → IO UInt64 := fun _ => do
  let (scalar, factors) ← requestIsabelleBZFactorization (smokeInput 5)
  return checksumCanonicalFactorization scalar factors

/--
Per-parameter verified-Isabelle BZ comparator targets on the encoded
degree/height inputs `prepDegreeHeightInput param` for the rungs of
`degreeHeightSchedule` (degree 3–6, height 2–32) and the additional
smaller-degree rungs of `slowDegreeHeightSchedule` (degree 1–3). Each pairs
with the corresponding rung of one of the parametric Lean
`runFactorDegreeHeightChecksum` / `runFactorFastDegreeHeightChecksum` /
`runFactorSlowDegreeHeightChecksum` registrations.
-/
def runIsabelleDegreeHeight3x2Checksum : Unit → IO UInt64 := fun _ => do
  let (scalar, factors) ← requestIsabelleBZFactorization
    (prepDegreeHeightInput (encodeDegreeHeightParam 3 2)).poly
  return checksumCanonicalFactorization scalar factors

def runIsabelleDegreeHeight4x2Checksum : Unit → IO UInt64 := fun _ => do
  let (scalar, factors) ← requestIsabelleBZFactorization
    (prepDegreeHeightInput (encodeDegreeHeightParam 4 2)).poly
  return checksumCanonicalFactorization scalar factors

def runIsabelleDegreeHeight4x8Checksum : Unit → IO UInt64 := fun _ => do
  let (scalar, factors) ← requestIsabelleBZFactorization
    (prepDegreeHeightInput (encodeDegreeHeightParam 4 8)).poly
  return checksumCanonicalFactorization scalar factors

def runIsabelleDegreeHeight5x8Checksum : Unit → IO UInt64 := fun _ => do
  let (scalar, factors) ← requestIsabelleBZFactorization
    (prepDegreeHeightInput (encodeDegreeHeightParam 5 8)).poly
  return checksumCanonicalFactorization scalar factors

def runIsabelleDegreeHeight6x32Checksum : Unit → IO UInt64 := fun _ => do
  let (scalar, factors) ← requestIsabelleBZFactorization
    (prepDegreeHeightInput (encodeDegreeHeightParam 6 32)).poly
  return checksumCanonicalFactorization scalar factors

def runIsabelleDegreeHeight1x2Checksum : Unit → IO UInt64 := fun _ => do
  let (scalar, factors) ← requestIsabelleBZFactorization
    (prepDegreeHeightInput (encodeDegreeHeightParam 1 2)).poly
  return checksumCanonicalFactorization scalar factors

def runIsabelleDegreeHeight2x2Checksum : Unit → IO UInt64 := fun _ => do
  let (scalar, factors) ← requestIsabelleBZFactorization
    (prepDegreeHeightInput (encodeDegreeHeightParam 2 2)).poly
  return checksumCanonicalFactorization scalar factors

def runIsabelleDegreeHeight3x8Checksum : Unit → IO UInt64 := fun _ => do
  let (scalar, factors) ← requestIsabelleBZFactorization
    (prepDegreeHeightInput (encodeDegreeHeightParam 3 8)).poly
  return checksumCanonicalFactorization scalar factors

/--
Per-input verified-Isabelle BZ comparator targets on the pinned HO-2 adversarial
fixtures. Each pairs with the corresponding `runFactorAdv*Checksum` Lean
singleton at its pinned `n = 0` row to yield a single-rung `hex/isabelle`
ratio. The advQuadSqrt2Sqrt3 case is already covered by
`runIsabelleFactorChecksum`, so only the other three adversarial inputs add new
registrations here.
-/
def runIsabelleAdvX4Plus1Checksum : Unit → IO UInt64 := fun _ => do
  let (scalar, factors) ← requestIsabelleBZFactorization advX4Plus1
  return checksumCanonicalFactorization scalar factors

def runIsabelleAdvPhi15Checksum : Unit → IO UInt64 := fun _ => do
  let (scalar, factors) ← requestIsabelleBZFactorization advPhi15
  return checksumCanonicalFactorization scalar factors

def runIsabelleAdvSwinnertonDyerSD3Checksum : Unit → IO UInt64 := fun _ => do
  let (scalar, factors) ← requestIsabelleBZFactorization advSwinnertonDyerSD3
  return checksumCanonicalFactorization scalar factors

/--
Per-rung verified-Isabelle BZ comparator targets on the cascade-trigger
`prepFallbackProbeInput n = (X-1)(X-2)...(X-n)` family for each rung of
`fallbackProbeSchedule = #[11, 12, 13, 15, 18, 22, 24]`. Each pairs with the
corresponding rung of the parametric Lean `runFactorFallbackProbeChecksum`
registration. The Isabelle reference factorisation on `(X-1)...(X-n)` is the
list of `n` distinct monic linears; this is the canonical-truth comparator the
`bz-vs-isabelle-investigation.md` post-mortem documents Lean as failing to
match on these rungs.

`expectedHash` is left as `none` rather than computing
`checksumCanonicalLeanFactorization (factor (prepFallbackProbeInput n))` at
elaboration time, because that compile-time call would invoke the same cascade
the post-mortem documents (200×–2,400× slower than Isabelle plus reducible
factor entries on these inputs), inflating compile time. Bench-time multiset
agreement is recorded by comparing the observed Isabelle hash against the
known split factorisation post-hoc.
-/
def runIsabelleFallbackProbeN11Checksum : Unit → IO UInt64 := fun _ => do
  let (scalar, factors) ← requestIsabelleBZFactorization (prepFallbackProbeInput 11)
  return checksumCanonicalFactorization scalar factors

def runIsabelleFallbackProbeN12Checksum : Unit → IO UInt64 := fun _ => do
  let (scalar, factors) ← requestIsabelleBZFactorization (prepFallbackProbeInput 12)
  return checksumCanonicalFactorization scalar factors

def runIsabelleFallbackProbeN13Checksum : Unit → IO UInt64 := fun _ => do
  let (scalar, factors) ← requestIsabelleBZFactorization (prepFallbackProbeInput 13)
  return checksumCanonicalFactorization scalar factors

def runIsabelleFallbackProbeN15Checksum : Unit → IO UInt64 := fun _ => do
  let (scalar, factors) ← requestIsabelleBZFactorization (prepFallbackProbeInput 15)
  return checksumCanonicalFactorization scalar factors

def runIsabelleFallbackProbeN18Checksum : Unit → IO UInt64 := fun _ => do
  let (scalar, factors) ← requestIsabelleBZFactorization (prepFallbackProbeInput 18)
  return checksumCanonicalFactorization scalar factors

def runIsabelleFallbackProbeN22Checksum : Unit → IO UInt64 := fun _ => do
  let (scalar, factors) ← requestIsabelleBZFactorization (prepFallbackProbeInput 22)
  return checksumCanonicalFactorization scalar factors

def runIsabelleFallbackProbeN24Checksum : Unit → IO UInt64 := fun _ => do
  let (scalar, factors) ← requestIsabelleBZFactorization (prepFallbackProbeInput 24)
  return checksumCanonicalFactorization scalar factors

/--
Per-rung verified-Isabelle BZ comparator targets on the
`prepPrecisionLocalInput param` polynomial at each rung of
`precisionLocalSchedule`. Each pairs with the corresponding rung of the
parametric Lean `runFastPathPrecisionLocalChecksum` registration.

The Lean target measures *fast-path setup* (multifactor lifting at the
precision axis plus the modular split profile), not full factorisation, so
the ratio `Lean_setup / Isabelle_full` is asymmetric: the operations
differ on the same input. The recorded number is therefore a strict
lower bound on the equivalent `factorFast`/`factor`-vs-Isabelle full-factor
ratio on that input — useful as a "setup alone exceeds Isabelle full
factor" tripwire rather than a full gating verdict. See
`reports/hex-berlekamp-zassenhaus-performance.md` §"Precision-local
asymmetric ratio ladder" for the methodology and interpretation.

`expectedHash` is `none` because the Lean precision-local checksum
records a mix of intermediate-state hashes (lifted factors, precision
cap, modular split profile), not a canonical factorisation, so the
two checksums are not directly comparable. Multiset agreement against
the constructed split factorisation `splitPrecisionLocalFactors` is
established post-hoc.
-/
def runIsabellePrecisionLocalRung1Checksum : Unit → IO UInt64 := fun _ => do
  let (scalar, factors) ← requestIsabelleBZFactorization
    (prepPrecisionLocalInput (encodePrecisionLocalParam 2 2 4 2)).poly
  return checksumCanonicalFactorization scalar factors

def runIsabellePrecisionLocalRung2Checksum : Unit → IO UInt64 := fun _ => do
  let (scalar, factors) ← requestIsabelleBZFactorization
    (prepPrecisionLocalInput (encodePrecisionLocalParam 2 2 16 2)).poly
  return checksumCanonicalFactorization scalar factors

def runIsabellePrecisionLocalRung3Checksum : Unit → IO UInt64 := fun _ => do
  let (scalar, factors) ← requestIsabelleBZFactorization
    (prepPrecisionLocalInput (encodePrecisionLocalParam 4 4 16 4)).poly
  return checksumCanonicalFactorization scalar factors

def runIsabellePrecisionLocalRung4Checksum : Unit → IO UInt64 := fun _ => do
  let (scalar, factors) ← requestIsabelleBZFactorization
    (prepPrecisionLocalInput (encodePrecisionLocalParam 4 16 64 4)).poly
  return checksumCanonicalFactorization scalar factors

def runIsabellePrecisionLocalRung5Checksum : Unit → IO UInt64 := fun _ => do
  let (scalar, factors) ← requestIsabelleBZFactorization
    (prepPrecisionLocalInput (encodePrecisionLocalParam 6 16 64 6)).poly
  return checksumCanonicalFactorization scalar factors

def runIsabellePrecisionLocalRung6Checksum : Unit → IO UInt64 := fun _ => do
  let (scalar, factors) ← requestIsabelleBZFactorization
    (prepPrecisionLocalInput (encodePrecisionLocalParam 8 32 128 8)).poly
  return checksumCanonicalFactorization scalar factors

def scheduledHardwareTag : String :=
  "scheduled-hardware"

/-- HO-3's classical-arithmetic BHKS model over the fast-schedule degree parameter. -/
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

/--
Classical setup model over encoded degree/height/precision/local-factor inputs:
the BHKS dense recombination surface plus quadratic multifactor lifting's
`r * n^2 * log k` contribution.
-/
def bzPrecisionLocalComplexity (param : Nat) : Nat :=
  let n := precisionLocalDegree param
  let h := Nat.log2 (precisionLocalHeight param + 2)
  let k := precisionLocalPrecision param
  let r := precisionLocalFactorCount param
  n ^ 9 + n ^ 7 * h ^ 2 + r * n * n * Nat.log2 (k + 1)

/-
Scientific split-family registration for the public combinator. The declared
cost model is the classical BHKS polynomial bound over the deterministic split
degree. `smokeInput n` has degree `n + 1`, so the asymptotic model is represented
with the same `n^9 + n^7 log^2 n` shape after dropping the constant offset;
dense arithmetic/recombination dominates, while the separate degree/height,
precision/local-factor, and adversarial registrations cover the other HO-3 axes.
-/
setup_benchmark runFactorChecksum n => bzClassicalSmokeComplexity n
  with prep := smokeInput
  where {
    paramFloor := 2
    paramCeiling := 24
    paramSchedule := .custom splitScientificSchedule
    maxSecondsPerCall := 8.0
    targetInnerNanos := 100000000
    signalFloorMultiplier := 1.0
  }

/-
Scientific fallback-prime probe registration for the public combinator. The
prepared fixture maps parameter `n` directly to the split degree of
`(X-1)...(X-n)`, selecting the post-mortem cascade-trigger cases where
prime-choice fallback and BHKS recombination shape interact. The declared model
remains the classical BHKS polynomial bound over that degree:
`n^9 + n^7 log^2 n`.
-/
setup_benchmark runFactorFallbackProbeChecksum n => bzClassicalSmokeComplexity n
  with prep := prepFallbackProbeInput
  where {
    paramFloor := 11
    paramCeiling := 24
    paramSchedule := .custom fallbackProbeSchedule
    maxSecondsPerCall := 8.0
    targetInnerNanos := 100000000
    signalFloorMultiplier := 1.0
  }

/-
Scientific split-family registration for the CLD fast path on the same inputs
as `factor`. Since `smokeInput n` again has degree `n + 1`, the declared model
uses the same offset-insensitive classical BHKS polynomial bound as the public
combinator. The fast path pays the same dense arithmetic and recombination
complexity on successful split inputs.
-/
setup_benchmark runFactorFastChecksum n => bzClassicalSmokeComplexity n
  with prep := smokeInput
  where {
    paramFloor := 2
    paramCeiling := 24
    paramSchedule := .custom splitScientificSchedule
    maxSecondsPerCall := 8.0
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
    paramSchedule := .custom smokeSchedule
    maxSecondsPerCall := 4.0
    targetInnerNanos := 100000000
    signalFloorMultiplier := 1.0
  }

/-
Shared-domain compare registration for the public combinator. The domain is the
same deterministic split family and `n = 1..4` schedule used by the fast-path
timing targets. The declared cost model is the classical BHKS bound
`bzClassicalSmokeComplexity n`, because this target runs the same public
fast-with-slow-fallback factorization as `runFactorChecksum` over the same
prepared inputs while making `compare` an intentional public-vs-exhaustive
equivalence check rather than an accidental overlap.
-/
setup_benchmark runFactorCompareChecksum n => bzClassicalSmokeComplexity n
  with prep := smokeInput
  where {
    paramFloor := 1
    paramCeiling := 4
    paramSchedule := .custom smokeSchedule
    maxSecondsPerCall := 4.0
    targetInnerNanos := 100000000
    signalFloorMultiplier := 1.0
  }

/-
Shared-domain compare registration for the exhaustive backstop. It returns the
same semantic factorization checksum as `runFactorCompareChecksum` on the same
deterministic split inputs, while retaining the slow path's exponential search
factor in the declared model.
-/
setup_benchmark runFactorSlowCompareChecksum n => 2 ^ n * bzClassicalSmokeComplexity n
  with prep := smokeInput
  where {
    paramFloor := 1
    paramCeiling := 4
    paramSchedule := .custom smokeSchedule
    maxSecondsPerCall := 4.0
    targetInnerNanos := 100000000
    signalFloorMultiplier := 1.0
  }

/-
Shared-domain compare registration for the CLD fast path. The return checksum
matches the public and slow compare targets when `factorFast` succeeds, and
uses a distinct sentinel on `none`, so adding this target to `compare` exposes
fast-path misses instead of masking them with the public fallback. The declared
cost model is again `bzClassicalSmokeComplexity n`: the fast path is the BHKS
bounded recombination route, and misses are encoded after that same attempted
computation rather than by falling through the exponential slow path.
-/
setup_benchmark runFactorFastCompareChecksum n => bzClassicalSmokeComplexity n
  with prep := smokeInput
  where {
    paramFloor := 1
    paramCeiling := 4
    paramSchedule := .custom smokeSchedule
    maxSecondsPerCall := 4.0
    targetInnerNanos := 100000000
    signalFloorMultiplier := 1.0
  }

/- Singleton HO-2 adversarial target: `X^4 + 1`. The declared cost model is
`n + 1` because the schedule pins `n = 0`; this constant bound records a
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
`factorFast` exceeds the `verify` mode's one-call budget; the declared cost
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
The slow diagnostic intentionally uses only the smallest completing
degree/height subset: exhaustive recombination has an exponential dependence on
the number of local factors, so the declared complexity is
`O(2^n * (n^9 + n^7 h^2))`.
-/
setup_benchmark runFactorSlowDegreeHeightChecksum param => bzSlowDegreeHeightComplexity param
  with prep := prepDegreeHeightInput
  where {
    paramFloor := encodeDegreeHeightParam 1 2
    paramCeiling := encodeDegreeHeightParam 3 8
    paramSchedule := .custom slowDegreeHeightSchedule
    maxSecondsPerCall := 4.0
    targetInnerNanos := 100000000
    signalFloorMultiplier := 1.0
  }

/-
Scientific fast-path setup registration for Phase 4. The encoded parameter
carries `(degree, height, precision, localFactorCount)`; the timed target runs
quadratic multifactor lifting at the requested precision and records the
supported-prime modular split profile, avoiding pathological full `factorFast`
calls while exposing the `k` and `r` axes required by the BZ/Hensel specs.
-/
setup_benchmark runFastPathPrecisionLocalChecksum param => bzPrecisionLocalComplexity param
  with prep := prepPrecisionLocalInput
  where {
    paramFloor := encodePrecisionLocalParam 2 2 4 2
    paramCeiling := encodePrecisionLocalParam 8 32 128 8
    paramSchedule := .custom precisionLocalSchedule
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
schedule. This setup-only registration keeps the fast-path precision cap and
pinned `p = 31` eight-linear split visible without routing through the public
fallback combinator. -/
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
exceed the `verify`-mode budget, so this reduced registration pins the same
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

/- Fixed bottom-rung verified-Isabelle comparator pair. Both targets return the
same canonical factor-multiset checksum for `(x^2 - 2)(x^2 - 3)`; scheduled runs use
`compare runFactorIsabelleDomainChecksum runIsabelleFactorChecksum` to record
the verified-to-verified ratio. -/
setup_fixed_benchmark runFactorIsabelleDomainChecksum where {
    repeats := 3
    maxSecondsPerCall := 20.0
    expectedHash := some (Hashable.hash (checksumCanonicalLeanFactorization (factor advQuadSqrt2Sqrt3)))
    tags := #[scheduledHardwareTag]
  }

setup_fixed_benchmark runIsabelleFactorChecksum where {
    repeats := 3
    maxSecondsPerCall := 60.0
    expectedHash := some (Hashable.hash (checksumCanonicalLeanFactorization (factor advQuadSqrt2Sqrt3)))
    tags := #[scheduledHardwareTag]
  }

setup_fixed_benchmark runIsabelleFactorBaselineChecksum where {
    repeats := 3
    maxSecondsPerCall := 60.0
    expectedHash := some (Hashable.hash (checksumCanonicalFactorization 1 #[]))
    tags := #[scheduledHardwareTag]
  }

/- Per-rung verified-Isabelle comparator registrations on `smokeInput n` for
`n = 2, 3, 4, 5`. The matched Lean timings come from the parametric
`runFactorChecksum` registration at the corresponding rung of
`splitScientificSchedule`; together they form the per-rung `hex/isabelle`
ratio ladder. Tagged `scheduled-hardware` so CI's `verify` does not invoke
the AFP-extracted comparator. -/
setup_fixed_benchmark runIsabelleSplitN2Checksum where {
    repeats := 3
    maxSecondsPerCall := 60.0
    expectedHash :=
      some (Hashable.hash (checksumCanonicalLeanFactorization (factor (smokeInput 2))))
    tags := #[scheduledHardwareTag]
  }

setup_fixed_benchmark runIsabelleSplitN3Checksum where {
    repeats := 3
    maxSecondsPerCall := 60.0
    expectedHash :=
      some (Hashable.hash (checksumCanonicalLeanFactorization (factor (smokeInput 3))))
    tags := #[scheduledHardwareTag]
  }

setup_fixed_benchmark runIsabelleSplitN4Checksum where {
    repeats := 3
    maxSecondsPerCall := 60.0
    expectedHash :=
      some (Hashable.hash (checksumCanonicalLeanFactorization (factor (smokeInput 4))))
    tags := #[scheduledHardwareTag]
  }

setup_fixed_benchmark runIsabelleSplitN5Checksum where {
    repeats := 3
    maxSecondsPerCall := 60.0
    expectedHash :=
      some (Hashable.hash (checksumCanonicalLeanFactorization (factor (smokeInput 5))))
    tags := #[scheduledHardwareTag]
  }

/- Per-rung verified-Isabelle comparator registrations on the encoded
degree/height inputs at each schedule rung. The first five cover
`degreeHeightSchedule = #[3002, 4002, 4008, 5008, 6032]` (paired with
`runFactorDegreeHeightChecksum` and `runFactorFastDegreeHeightChecksum`); the
last three cover the smaller-degree `slowDegreeHeightSchedule = #[1002, 2002,
3008]` (paired with `runFactorSlowDegreeHeightChecksum`). -/
setup_fixed_benchmark runIsabelleDegreeHeight3x2Checksum where {
    repeats := 3
    maxSecondsPerCall := 60.0
    expectedHash := some (Hashable.hash (checksumCanonicalLeanFactorization
      (factor (prepDegreeHeightInput (encodeDegreeHeightParam 3 2)).poly)))
    tags := #[scheduledHardwareTag]
  }

setup_fixed_benchmark runIsabelleDegreeHeight4x2Checksum where {
    repeats := 3
    maxSecondsPerCall := 60.0
    expectedHash := some (Hashable.hash (checksumCanonicalLeanFactorization
      (factor (prepDegreeHeightInput (encodeDegreeHeightParam 4 2)).poly)))
    tags := #[scheduledHardwareTag]
  }

setup_fixed_benchmark runIsabelleDegreeHeight4x8Checksum where {
    repeats := 3
    maxSecondsPerCall := 60.0
    expectedHash := some (Hashable.hash (checksumCanonicalLeanFactorization
      (factor (prepDegreeHeightInput (encodeDegreeHeightParam 4 8)).poly)))
    tags := #[scheduledHardwareTag]
  }

setup_fixed_benchmark runIsabelleDegreeHeight5x8Checksum where {
    repeats := 3
    maxSecondsPerCall := 60.0
    expectedHash := some (Hashable.hash (checksumCanonicalLeanFactorization
      (factor (prepDegreeHeightInput (encodeDegreeHeightParam 5 8)).poly)))
    tags := #[scheduledHardwareTag]
  }

setup_fixed_benchmark runIsabelleDegreeHeight6x32Checksum where {
    repeats := 3
    maxSecondsPerCall := 60.0
    expectedHash := some (Hashable.hash (checksumCanonicalLeanFactorization
      (factor (prepDegreeHeightInput (encodeDegreeHeightParam 6 32)).poly)))
    tags := #[scheduledHardwareTag]
  }

setup_fixed_benchmark runIsabelleDegreeHeight1x2Checksum where {
    repeats := 3
    maxSecondsPerCall := 60.0
    expectedHash := some (Hashable.hash (checksumCanonicalLeanFactorization
      (factor (prepDegreeHeightInput (encodeDegreeHeightParam 1 2)).poly)))
    tags := #[scheduledHardwareTag]
  }

setup_fixed_benchmark runIsabelleDegreeHeight2x2Checksum where {
    repeats := 3
    maxSecondsPerCall := 60.0
    expectedHash := some (Hashable.hash (checksumCanonicalLeanFactorization
      (factor (prepDegreeHeightInput (encodeDegreeHeightParam 2 2)).poly)))
    tags := #[scheduledHardwareTag]
  }

setup_fixed_benchmark runIsabelleDegreeHeight3x8Checksum where {
    repeats := 3
    maxSecondsPerCall := 60.0
    expectedHash := some (Hashable.hash (checksumCanonicalLeanFactorization
      (factor (prepDegreeHeightInput (encodeDegreeHeightParam 3 8)).poly)))
    tags := #[scheduledHardwareTag]
  }

/- Per-input verified-Isabelle comparator registrations on the HO-2 adversarial
fixtures (one per distinct singleton input). Each pairs with the matching
`runFactorAdv*Checksum` Lean singleton's pinned `n = 0` row. `advX4Plus1` and
`advPhi15` are small enough that the `factor`-driven `expectedHash` elaborates
quickly; `advSwinnertonDyerSD3` factor exceeds the verifier's per-call budget
(see `runAdvSwinnertonDyerSD3ModularSplitChecksum` doc) so its
`expectedHash` is left `none` and multiset agreement is established at bench
time by `ensureIsabelleBZCrossCheck` if the input is added to that fixture
list, or post-hoc against the known SD3 reference factorisation. -/
setup_fixed_benchmark runIsabelleAdvX4Plus1Checksum where {
    repeats := 3
    maxSecondsPerCall := 60.0
    expectedHash :=
      some (Hashable.hash (checksumCanonicalLeanFactorization (factor advX4Plus1)))
    tags := #[scheduledHardwareTag]
  }

setup_fixed_benchmark runIsabelleAdvPhi15Checksum where {
    repeats := 3
    maxSecondsPerCall := 60.0
    expectedHash :=
      some (Hashable.hash (checksumCanonicalLeanFactorization (factor advPhi15)))
    tags := #[scheduledHardwareTag]
  }

setup_fixed_benchmark runIsabelleAdvSwinnertonDyerSD3Checksum where {
    repeats := 3
    maxSecondsPerCall := 60.0
    tags := #[scheduledHardwareTag]
  }

/- Per-rung verified-Isabelle comparator registrations on
`prepFallbackProbeInput n` for each rung of `fallbackProbeSchedule`. Pairs with
`runFactorFallbackProbeChecksum` at the same rung. `expectedHash` is `none` on
every registration to avoid elaborating the cascade-affected Lean `factor` call
at compile time (see the per-`def` doc comment for the rationale). Tagged
`scheduled-hardware` so CI's `verify` does not invoke the AFP-extracted
comparator. -/
setup_fixed_benchmark runIsabelleFallbackProbeN11Checksum where {
    repeats := 3
    maxSecondsPerCall := 60.0
    tags := #[scheduledHardwareTag]
  }

setup_fixed_benchmark runIsabelleFallbackProbeN12Checksum where {
    repeats := 3
    maxSecondsPerCall := 60.0
    tags := #[scheduledHardwareTag]
  }

setup_fixed_benchmark runIsabelleFallbackProbeN13Checksum where {
    repeats := 3
    maxSecondsPerCall := 60.0
    tags := #[scheduledHardwareTag]
  }

setup_fixed_benchmark runIsabelleFallbackProbeN15Checksum where {
    repeats := 3
    maxSecondsPerCall := 60.0
    tags := #[scheduledHardwareTag]
  }

setup_fixed_benchmark runIsabelleFallbackProbeN18Checksum where {
    repeats := 3
    maxSecondsPerCall := 60.0
    tags := #[scheduledHardwareTag]
  }

setup_fixed_benchmark runIsabelleFallbackProbeN22Checksum where {
    repeats := 3
    maxSecondsPerCall := 60.0
    tags := #[scheduledHardwareTag]
  }

setup_fixed_benchmark runIsabelleFallbackProbeN24Checksum where {
    repeats := 3
    maxSecondsPerCall := 60.0
    tags := #[scheduledHardwareTag]
  }

/- Per-rung verified-Isabelle comparator registrations on
`prepPrecisionLocalInput param` for each rung of `precisionLocalSchedule`.
Pairs with `runFastPathPrecisionLocalChecksum` at the same rung. The
ratio is asymmetric (Lean measures setup only, Isabelle measures full
factor on the same input) and is reported as a lower bound on the
implied full-factor ratio — see the per-`def` doc comment for the
methodology and tripwire interpretation. `expectedHash` is `none` because
the Lean checksum mixes intermediate-state hashes, not a canonical
factorisation; multiset agreement against the constructed split
factorisation is established post-hoc. Tagged `scheduled-hardware` so
CI's `verify` does not invoke the AFP-extracted comparator. -/
setup_fixed_benchmark runIsabellePrecisionLocalRung1Checksum where {
    repeats := 3
    maxSecondsPerCall := 60.0
    tags := #[scheduledHardwareTag]
  }

setup_fixed_benchmark runIsabellePrecisionLocalRung2Checksum where {
    repeats := 3
    maxSecondsPerCall := 60.0
    tags := #[scheduledHardwareTag]
  }

setup_fixed_benchmark runIsabellePrecisionLocalRung3Checksum where {
    repeats := 3
    maxSecondsPerCall := 60.0
    tags := #[scheduledHardwareTag]
  }

setup_fixed_benchmark runIsabellePrecisionLocalRung4Checksum where {
    repeats := 3
    maxSecondsPerCall := 60.0
    tags := #[scheduledHardwareTag]
  }

setup_fixed_benchmark runIsabellePrecisionLocalRung5Checksum where {
    repeats := 3
    maxSecondsPerCall := 60.0
    tags := #[scheduledHardwareTag]
  }

setup_fixed_benchmark runIsabellePrecisionLocalRung6Checksum where {
    repeats := 3
    maxSecondsPerCall := 60.0
    tags := #[scheduledHardwareTag]
  }

end BerlekampZassenhausBench
end Hex

namespace Hex.BerlekampZassenhausBench

def verifySmokeTargetsOnly : IO UInt32 := do
  let parametric ← LeanBench.allRuntimeEntries
  let fixed ← LeanBench.allFixedRuntimeEntries
  let names :=
    (parametric.filter (fun e => !e.spec.config.tags.contains scheduledHardwareTag)
      |>.map (·.spec.name) |>.toList) ++
    (fixed.filter (fun e => !e.spec.config.tags.contains scheduledHardwareTag)
      |>.map (·.spec.name) |>.toList)
  let reports ← LeanBench.verify names
  IO.println (LeanBench.Format.fmtCombinedVerify reports)
  return if reports.passed then 0 else 1

end Hex.BerlekampZassenhausBench

def main (args : List String) : IO UInt32 :=
  match args with
  | ["verify"] => Hex.BerlekampZassenhausBench.verifySmokeTargetsOnly
  | _ => LeanBench.Cli.dispatch args
