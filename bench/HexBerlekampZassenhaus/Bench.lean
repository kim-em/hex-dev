/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import HexBerlekampZassenhaus
import Hex.BenchOracle.Flint
import Lean.Data.Json
import LeanBench

/-!
Phase 4 benchmark registrations for `hex-berlekamp-zassenhaus`.

This module is the Phase 4 benchmark root for the BZ factorization API. It
covers the public total cascade, the option-valued lattice tier, the exact
trial backstop, canonical degree/height and precision/local-factor inputs, a
shared-domain `compare` pair, product-adoption inputs, and the HO-2 adversarial
recombination shapes. Comparator ratios and the headline performance report
still depend on the scheduled-hardware runs and report reconciliation
described in `SPEC/benchmarking.md`.

The registration names are intentionally stable: CI and scheduled timing runs
refer to these case names when checking that the benchmark harness still covers
the public BZ API surface. Each fixed registration has an adjacent input and
absolute-budget justification.

The factor and product targets below use mode 3. Their former parametric
families could not justify a tight dominant-phase scaling model; the report
retains those clean sweeps and explicitly records the loss of asymptotic
regression detection.

Canonical split inputs:

* `runFactorChecksum`: public `ZPoly.factorize` on `smokeInput 24`.
* `runFactorSlowChecksum`: exact trial backstop on `smokeInput 8`.
* `runFactorFallbackProbeChecksum`: public `ZPoly.factorize` on the
  cascade-trigger `prepFallbackProbeInput 24`.

Shared compare domain (`smokeInput 8`):

* `runFactorCompareChecksum` vs `runFactorSlowCompareChecksum` checks the
  public cascade against exact trial factorization.

Degree/height registrations:

* `runFactorDegreeHeightChecksum`: public `ZPoly.factorize` at `(6, 32)`.
* `runFactorSlowDegreeHeightChecksum`: trial factorization at `(4, 8)`.

Precision/local-factor registration (`prep := prepPrecisionLocalInput`):

* `runFastPathPrecisionLocalChecksum`: `verify`-budget-safe fast-path setup at
  `(degree, height, precision, local factors) = (8, 32, 128, 8)`.

Fast-product adoption registrations:

* `runTrialProductSchoolbookChecksum` vs `runTrialProductChecksum`: balanced
  lifted-factor subset products with low factor degree and large coefficients.
* `runReassemblyProductSchoolbookChecksum` vs
  `runReassemblyProductChecksum`: balanced, higher-degree final integer
  reassembly products.
* `runSkewProductSchoolbookChecksum` vs `runSkewProductChecksum`: one large
  factor followed by many linear factors, guarding the skewed-degree case.

HO-2 adversarial fixed targets:

* `runFactorAdvX4Plus1Checksum`, `runFactorAdvQuadSqrt2Sqrt3Checksum`,
  `runFactorAdvPhi15Checksum`: full public `ZPoly.factorize` on the named adversarial
  input.
* `runFactorFastSetupAdvX4Plus1Checksum`,
  `runFactorFastSetupAdvPhi15Checksum`: lattice precision-cap *setup* only —
  these record the public precision cap and pinned modular split profile,
  because a full lattice factorization exceeds the verifier's one-call budget
  on these inputs.
* `runAdvSwinnertonDyerSD3ModularSplitChecksum`: pinned modular split profile
  for SD3 at the conformance prime, keeping the worst-case recombination shape
  independently visible.
* `runFactorLatticeAdvSwinnertonDyerSD3Checksum`,
  `runFactorLatticeAdvSwinnertonDyerSD4Checksum`: full `factorLattice` on SD3
  and SD4 — the lattice tier's certificate-backed early stop (#8395) makes the
  complete lattice factorization of these extreme-`r` irreducibles affordable
  in `verify`.

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
  for the historical split-family and degree/height parametric audits, used
  to build the retained `hex/isabelle` scaling ladders in
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

/-- Swinnerton-Dyer `SD_4` input (minimal polynomial of `√2+√3+√5+√7`),
degree 16: irreducible over `ℤ`, splits into 16 linear factors mod every
prime. -/
def advSwinnertonDyerSD4 : ZPoly :=
  DensePoly.ofCoeffs
    #[46225, 0, -5596840, 0, 13950764, 0, -7453176, 0, 1513334, 0, -141912, 0,
      6476, 0, -136, 0, 1]

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
mod-`31` local factors separately, while the timed target avoids a full
lattice factorization on adversarial cases.
-/
structure PrecisionLocalInput where
  degree : Nat
  height : Nat
  precision : Nat
  localFactorCount : Nat
  poly : ZPoly
  localFactors : Array ZPoly
  deriving Hashable

/-- Prepared integer factors for one retained/production product comparison. -/
structure ProductInput where
  factors : Array ZPoly
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

/-- Deterministic monic dense integer factor with independently controlled
degree and coefficient width. -/
def denseZFactor (degree bits salt : Nat) : ZPoly :=
  let scale := (2 : Int) ^ bits
  DensePoly.ofCoeffs <|
    ((Array.range degree).map fun i =>
      scale * Int.ofNat ((i + 1) * (salt + 3) + i * i + 1) +
        Int.ofNat (i + salt + 1)).push 1

/-- BZ subset-product shape: many small-degree monic lifted factors whose
non-leading coefficients have Hensel-sized magnitude. -/
def prepTrialProductInput (count : Nat) : ProductInput :=
  { factors := (Array.range count).map fun i => denseZFactor 4 64 (i + 11) }

/-- Final-reassembly shape: balanced higher-degree factors at larger integer
coefficient width. -/
def prepReassemblyProductInput (count : Nat) : ProductInput :=
  { factors := (Array.range count).map fun i => denseZFactor 32 128 (i + 29) }

/-- Skewed trial-product shape: one already-large residual factor followed by
many linear factors. -/
def prepSkewProductInput (count : Nat) : ProductInput :=
  let tail := (Array.range (count - 1)).map fun i =>
    linearZFactor ((2 : Int) ^ 64 + Int.ofNat (i + 1))
  { factors := if count = 0 then #[] else #[denseZFactor 256 64 47] ++ tail }

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
records the lattice tier's precision cap and the pinned local split shape
feeding recombination. It keeps the hard CLD cases visible to `list` / `verify`
while the full lattice factorization remains too expensive for the `verify`
budget.
-/
def checksumFastPathSetup (f : ZPoly) (p : Nat) : UInt64 :=
  mixHash (hash (latticePrecisionCap f)) (checksumOptionNatArray (modularFactorDegreesAt? f p))

/-- Checksum the public total factorization cascade on one input. -/
def factorChecksum (f : ZPoly) : UInt64 :=
  checksumFactorization (ZPoly.factorize f)

/-- Checksum public factorization on one explicit fallback-prime probe. -/
@[noinline]
def fallbackProbeChecksum (f : ZPoly) : UInt64 :=
  factorChecksum f

/-- Checksum the exact trial-division backstop on one input. -/
def trialFactorChecksum (f : ZPoly) : UInt64 :=
  checksumFactorization (factorTrial f)

/-- Checksum public factorization for the shared fixed compare domain. -/
def factorCompareChecksum (f : ZPoly) : UInt64 :=
  checksumFactorization (ZPoly.factorize f)

/-- Checksum trial factorization for the shared fixed compare domain. -/
def trialCompareChecksum (f : ZPoly) : UInt64 :=
  checksumFactorization (factorTrial f)

/-- Retained ordered schoolbook fold for a BZ subset-product fixture. -/
def trialProductSchoolbookChecksum (input : ProductInput) : UInt64 :=
  checksumZPoly <| input.factors.foldl (· * ·) 1

/-- Production `Array.polyProduct` dispatcher on a BZ subset-product fixture. -/
def trialProductChecksum (input : ProductInput) : UInt64 :=
  checksumZPoly <| Array.polyProduct input.factors

/-- Retained ordered schoolbook fold for final-reassembly factors. -/
def reassemblyProductSchoolbookChecksum (input : ProductInput) : UInt64 :=
  checksumZPoly <| input.factors.foldl (· * ·) 1

/-- Production `Array.polyProduct` dispatcher on final-reassembly factors. -/
def reassemblyProductChecksum (input : ProductInput) : UInt64 :=
  checksumZPoly <| Array.polyProduct input.factors

/-- Retained ordered schoolbook fold for a skewed BZ factor array. -/
def skewProductSchoolbookChecksum (input : ProductInput) : UInt64 :=
  checksumZPoly <| input.factors.foldl (· * ·) 1

/-- Production `Array.polyProduct` dispatcher on a skewed BZ factor array. -/
def skewProductChecksum (input : ProductInput) : UInt64 :=
  checksumZPoly <| Array.polyProduct input.factors

/-- Opaque IO boundary for fixed full-factorization benchmarks. -/
@[noinline]
def factorChecksumIO (f : ZPoly) : IO UInt64 :=
  pure (factorChecksum f)

/-- Opaque IO boundary for fixed trial-factorization benchmarks. -/
@[noinline]
def trialChecksumIO (f : ZPoly) : IO UInt64 :=
  pure (trialFactorChecksum f)

/-- Opaque IO boundary for fixed product benchmarks. -/
@[noinline]
def productChecksumIO (run : ProductInput → UInt64) (input : ProductInput) : IO UInt64 :=
  pure (run input)

/-- Opaque IO boundary for fixed fast-path-setup benchmarks. -/
@[noinline]
def setupChecksumIO (f : ZPoly) (p : Nat) : IO UInt64 :=
  pure (checksumFastPathSetup f p)

/-- Opaque IO boundary for fixed modular-split benchmarks. -/
@[noinline]
def splitChecksumIO (f : ZPoly) (p : Nat) : IO UInt64 :=
  pure (checksumOptionNatArray (modularFactorDegreesAt? f p))

/-- Opaque IO boundary for fixed lattice-tier benchmarks. -/
@[noinline]
def latticeChecksumIO (f : ZPoly) : IO UInt64 :=
  pure (checksumOptionFactorization (factorLattice f))

/-- Fixed benchmark target: public factorization on `X^4 + 1`. -/
def runFactorAdvX4Plus1Checksum : Unit → IO UInt64 := fun _ =>
  factorChecksumIO advX4Plus1

/-- Fixed benchmark target: fast-path setup on `X^4 + 1`, pinned at `p = 5`. -/
def runFactorFastSetupAdvX4Plus1Checksum : Unit → IO UInt64 := fun _ =>
  setupChecksumIO advX4Plus1 5

/-- Fixed benchmark target: public factorization on `(X^2 - 2)(X^2 - 3)`. -/
def runFactorAdvQuadSqrt2Sqrt3Checksum : Unit → IO UInt64 := fun _ =>
  factorChecksumIO advQuadSqrt2Sqrt3

/-- Fixed benchmark target: public factorization on `Phi_15`. -/
def runFactorAdvPhi15Checksum : Unit → IO UInt64 := fun _ =>
  factorChecksumIO advPhi15

/-- Fixed benchmark target: fast-path setup on `Phi_15`, pinned at `p = 31`. -/
def runFactorFastSetupAdvPhi15Checksum : Unit → IO UInt64 := fun _ =>
  setupChecksumIO advPhi15 31

/--
Singleton benchmark target: pinned modular split profile for Swinnerton-Dyer
`SD_3` at `p = 71`, where the degree-eight integer polynomial splits into
eight local linear factors.
-/
def runAdvSwinnertonDyerSD3ModularSplitChecksum : Unit → IO UInt64 := fun _ =>
  splitChecksumIO advSwinnertonDyerSD3 71

/--
Singleton benchmark target: CLD lattice tier (`factorLattice`) on
Swinnerton-Dyer `SD_3`.  The certificate-backed early stop (#8395) certifies
irreducibility at the first column-adequate precision instead of grinding the
doubling schedule to the BHKS cap, which is what makes the full lattice-tier
factorization affordable inside the `verify` budget.
-/
def runFactorLatticeAdvSwinnertonDyerSD3Checksum : Unit → IO UInt64 := fun _ =>
  latticeChecksumIO advSwinnertonDyerSD3

/--
Singleton benchmark target: CLD lattice tier (`factorLattice`) on
Swinnerton-Dyer `SD_4` (degree 16, 16-way modular split). The early-stop
separation certificate terminates at the column-adequacy floor, keeping the
extreme-`r` tail visible in `verify`.
-/
def runFactorLatticeAdvSwinnertonDyerSD4Checksum : Unit → IO UInt64 := fun _ =>
  latticeChecksumIO advSwinnertonDyerSD4

/-- Checksum the public combinator on one degree/height input. -/
def factorDegreeHeightChecksum (input : DegreeHeightInput) : UInt64 :=
  checksumFactorization (ZPoly.factorize input.poly)

/-- Checksum the trial backstop on one degree/height input. -/
def trialDegreeHeightChecksum (input : DegreeHeightInput) : UInt64 :=
  checksumFactorization (factorTrial input.poly)

/--
Benchmark target: `verify`-budget-safe fast-path setup over encoded degree,
height, Hensel precision, and local-factor-count axes.
-/
def precisionLocalChecksum (input : PrecisionLocalInput) : UInt64 :=
  let lifted :=
    ZPoly.multifactorLiftQuadratic 31 input.precision input.poly input.localFactors
  let splitProfile := modularFactorDegreesAt? input.poly 31
  mixHash (hash input.precision) <|
    mixHash (hash input.localFactorCount) <|
      mixHash (checksumZPolyArray lifted) <|
        mixHash (hash (latticePrecisionCap input.poly)) (checksumOptionNatArray splitProfile)

/-- Opaque IO boundary for fixed precision/local setup benchmarks. -/
@[noinline]
def precisionLocalChecksumIO (input : PrecisionLocalInput) : IO UInt64 :=
  pure (precisionLocalChecksum input)

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
    let leanChecksum := checksumCanonicalLeanFactorization (ZPoly.factorize f)
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
  return checksumCanonicalLeanFactorization (ZPoly.factorize advQuadSqrt2Sqrt3)

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
rung from the clean historical `runFactorChecksum` parametric audit to yield
a `hex/isabelle` ratio at that rung; together they form the retained ladder
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
with the corresponding rung from the clean historical
`runFactorDegreeHeightChecksum` / `runFactorSlowDegreeHeightChecksum`
parametric audits.
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
corresponding rung from the clean historical `runFactorFallbackProbeChecksum`
parametric audit. The Isabelle reference factorisation on `(X-1)...(X-n)` is the
list of `n` distinct monic linears; this is the canonical-truth comparator the
`bz-vs-isabelle-investigation.md` post-mortem documents Lean as failing to
match on these rungs.

`expectedHash` is left as `none` rather than computing
`checksumCanonicalLeanFactorization (ZPoly.factorize (prepFallbackProbeInput n))` at
elaboration time, because that compile-time call would invoke the same cascade
the post-mortem documents as producing reducible factor entries on these
inputs, inflating compile time. Bench-time multiset
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
`precisionLocalSchedule`. Each pairs with the corresponding rung from the
clean historical `runFastPathPrecisionLocalChecksum` parametric audit.

The Lean target measures *fast-path setup* (multifactor lifting at the
precision axis plus the modular split profile), not full factorisation, so
the ratio `Lean_setup / Isabelle_full` is asymmetric: the operations
differ on the same input. The recorded number is therefore a strict
lower bound on the equivalent `factorLattice`/`factor`-vs-Isabelle full-factor
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

/-- Fixed mode-3 target: public cascade on the top audited split input. -/
def runFactorChecksum : Unit → IO UInt64 := fun _ =>
  factorChecksumIO (smokeInput 24)

/-- Fixed mode-3 target: public cascade on the top fallback-prime probe. -/
def runFactorFallbackProbeChecksum : Unit → IO UInt64 := fun _ =>
  factorChecksumIO (prepFallbackProbeInput 24)

/-- Fixed mode-3 target: trial division on nine consecutive integer roots. -/
def runFactorSlowChecksum : Unit → IO UInt64 := fun _ =>
  trialChecksumIO (smokeInput 8)

/-- Fixed mode-3 public side of the shared `smokeInput 8` compare input. -/
def runFactorCompareChecksum : Unit → IO UInt64 := fun _ =>
  factorChecksumIO (smokeInput 8)

/-- Fixed mode-3 trial side of the shared `smokeInput 8` compare input. -/
def runFactorSlowCompareChecksum : Unit → IO UInt64 := fun _ =>
  trialChecksumIO (smokeInput 8)

/-- Fixed mode-3 public factorization at degree six and root-height 32. -/
def runFactorDegreeHeightChecksum : Unit → IO UInt64 := fun _ =>
  factorChecksumIO (prepDegreeHeightInput (encodeDegreeHeightParam 6 32)).poly

/-- Fixed mode-3 trial factorization at degree four and root-height eight. -/
def runFactorSlowDegreeHeightChecksum : Unit → IO UInt64 := fun _ =>
  trialChecksumIO (prepDegreeHeightInput (encodeDegreeHeightParam 4 8)).poly

/-- Fixed mode-3 setup at `(degree, height, precision, factors) = (8, 32, 128, 8)`. -/
def runFastPathPrecisionLocalChecksum : Unit → IO UInt64 := fun _ =>
  precisionLocalChecksumIO
    (prepPrecisionLocalInput (encodePrecisionLocalParam 8 32 128 8))

/-- Fixed product-adoption reference at 64 lifted factors. -/
def runTrialProductSchoolbookChecksum : Unit → IO UInt64 := fun _ =>
  productChecksumIO trialProductSchoolbookChecksum (prepTrialProductInput 64)

/-- Fixed product-adoption dispatcher at 64 lifted factors. -/
def runTrialProductChecksum : Unit → IO UInt64 := fun _ =>
  productChecksumIO trialProductChecksum (prepTrialProductInput 64)

/-- Fixed reassembly reference at 32 dense factors. -/
def runReassemblyProductSchoolbookChecksum : Unit → IO UInt64 := fun _ =>
  productChecksumIO reassemblyProductSchoolbookChecksum (prepReassemblyProductInput 32)

/-- Fixed reassembly dispatcher at 32 dense factors. -/
def runReassemblyProductChecksum : Unit → IO UInt64 := fun _ =>
  productChecksumIO reassemblyProductChecksum (prepReassemblyProductInput 32)

/-- Fixed skew-product reference at 256 factors. -/
def runSkewProductSchoolbookChecksum : Unit → IO UInt64 := fun _ =>
  productChecksumIO skewProductSchoolbookChecksum (prepSkewProductInput 256)

/-- Fixed skew-product dispatcher at 256 factors. -/
def runSkewProductChecksum : Unit → IO UInt64 := fun _ =>
  productChecksumIO skewProductChecksum (prepSkewProductInput 256)

/- All mode-3 targets below use the verifier's independently fixed four-second
per-call ceiling. This keeps each canonical operation within the existing CI
contract while tolerating shared-runner scheduling noise. -/

/- Mode 3: 64 lifted factors is the first sustained large-integer product
regime (clean baseline 9.7 ms). -/
setup_fixed_benchmark runTrialProductSchoolbookChecksum where {
    repeats := 5
    minTotalSeconds := 0.01
    maxSecondsPerCall := 4.0
    expectedHash := some 0xc83c0a1fbfe185a2
    tags := #["adoption", "trial-product", "schoolbook", "reference"]
  }

/- Mode 3 on the same 64-factor input (clean baseline 12.6 ms). -/
setup_fixed_benchmark runTrialProductChecksum where {
    repeats := 5
    minTotalSeconds := 0.01
    maxSecondsPerCall := 4.0
    expectedHash := some 0xc83c0a1fbfe185a2
    tags := #["adoption", "trial-product", "dispatch"]
  }

/- Mode 3: 32 dense factors exercise large-coefficient reassembly without the
next rung's one-second call (clean baseline 163 ms). -/
setup_fixed_benchmark runReassemblyProductSchoolbookChecksum where {
    repeats := 5
    minTotalSeconds := 0.05
    maxSecondsPerCall := 4.0
    expectedHash := some 0x55cb88e8ce461b3d
    tags := #["adoption", "reassembly", "schoolbook", "reference"]
  }

/- Mode 3 on the same 32-factor reassembly input (clean baseline 129 ms). -/
setup_fixed_benchmark runReassemblyProductChecksum where {
    repeats := 5
    minTotalSeconds := 0.05
    maxSecondsPerCall := 4.0
    expectedHash := some 0x55cb88e8ce461b3d
    tags := #["adoption", "reassembly", "dispatch"]
  }

/- Mode 3: 256 factors retain the skewed-degree stress shape (clean baseline
114 ms). -/
setup_fixed_benchmark runSkewProductSchoolbookChecksum where {
    repeats := 5
    minTotalSeconds := 0.05
    maxSecondsPerCall := 4.0
    expectedHash := some 0x5a3c3280f7b0e2ff
    tags := #["adoption", "trial-product", "skewed", "schoolbook", "reference"]
  }

/- Mode 3 on the same 256-factor skew input (clean baseline 110 ms). -/
setup_fixed_benchmark runSkewProductChecksum where {
    repeats := 5
    minTotalSeconds := 0.05
    maxSecondsPerCall := 4.0
    expectedHash := some 0x5a3c3280f7b0e2ff
    tags := #["adoption", "trial-product", "skewed", "dispatch"]
  }

/- Mode 3: `smokeInput 24` is the largest clean audited split input (clean
baseline 6.3 ms). -/
setup_fixed_benchmark runFactorChecksum where {
    repeats := 5
    minTotalSeconds := 0.001
    maxSecondsPerCall := 4.0
    expectedHash := some 0xaa37abf9a367da53
  }

/- Mode 3: the degree-24 fallback probe is the largest canonical cascade
trigger (clean baseline 5.9 ms). -/
setup_fixed_benchmark runFactorFallbackProbeChecksum where {
    repeats := 5
    minTotalSeconds := 0.001
    maxSecondsPerCall := 4.0
    expectedHash := some 0xa5c23a7af3e800c4
  }

/- Mode 3: `smokeInput 8` forces the integer-root scan through `9!` candidates
(clean baseline 4.1 ms). -/
setup_fixed_benchmark runFactorSlowChecksum where {
    repeats := 5
    minTotalSeconds := 0.001
    maxSecondsPerCall := 4.0
    expectedHash := some 0x352456cfdef1ea82
  }

/- Mode 3 public side of the shared `smokeInput 8` compare input. -/
setup_fixed_benchmark runFactorCompareChecksum where {
    repeats := 5
    minTotalSeconds := 0.001
    maxSecondsPerCall := 4.0
    expectedHash := some 0x352456cfdef1ea82
  }

/- Mode 3 trial side of the shared `smokeInput 8` compare input. -/
setup_fixed_benchmark runFactorSlowCompareChecksum where {
    repeats := 5
    minTotalSeconds := 0.001
    maxSecondsPerCall := 4.0
    expectedHash := some 0x352456cfdef1ea82
  }

/- Fixed HO-2 adversarial target: `X^4 + 1`. This records one canonical
recombination shape where the integer polynomial is irreducible but splits
modulo `5`; a fixed registration avoids a meaningless singleton scaling
verdict. -/
setup_fixed_benchmark runFactorAdvX4Plus1Checksum where {
    repeats := 5
    minTotalSeconds := 0.2
    maxSecondsPerCall := 4.0
    expectedHash := some 0xdbadaf53f188eac1
  }

/- Mode 3: `(degree, root-height) = (6, 32)` is the top audited matrix input. -/
setup_fixed_benchmark runFactorDegreeHeightChecksum where {
    repeats := 5
    minTotalSeconds := 0.001
    maxSecondsPerCall := 4.0
    expectedHash := some 0xf31efeaecbf8fa27
  }

/- Fixed HO-2 adversarial lattice precision-cap setup target for `X^4 + 1`.
A full lattice factorization exceeds the `verify` mode's one-call budget, so
this measures the public precision cap plus the pinned `p = 5` modular split
profile. -/
setup_fixed_benchmark runFactorFastSetupAdvX4Plus1Checksum where {
    repeats := 5
    minTotalSeconds := 0.2
    maxSecondsPerCall := 4.0
    expectedHash := some 0x6125716b68ef63ab
  }

/- Mode 3: `(degree, root-height) = (4, 8)` is the first nontrivial matrix case
beyond the former short ladder. -/
setup_fixed_benchmark runFactorSlowDegreeHeightChecksum where {
    repeats := 5
    minTotalSeconds := 0.001
    maxSecondsPerCall := 4.0
    expectedHash := some 0x0ed3a73af254827d
  }

/- Mode 3: `(8, 32, 128, 8)` is the top precision/local-factor setup input. -/
setup_fixed_benchmark runFastPathPrecisionLocalChecksum where {
    repeats := 5
    minTotalSeconds := 0.001
    maxSecondsPerCall := 4.0
    expectedHash := some 0x21b9063dace28489
  }

/- Fixed HO-2 adversarial target: `(X^2 - 2)(X^2 - 3)`. At the pinned fixture
prime this splits into four local linear factors and recombines into two true
quadratics. -/
setup_fixed_benchmark runFactorAdvQuadSqrt2Sqrt3Checksum where {
    repeats := 5
    minTotalSeconds := 0.2
    maxSecondsPerCall := 4.0
    expectedHash := some 0x2939937eff41b345
  }

/- Fixed HO-2 adversarial target: `Phi_15`. This degree-eight cyclotomic case
exercises the recombination hot path on a canonical fixture. -/
setup_fixed_benchmark runFactorAdvPhi15Checksum where {
    repeats := 5
    minTotalSeconds := 0.2
    maxSecondsPerCall := 6.0
    expectedHash := some 0x0f794f386e54863f
  }

/- Fixed HO-2 adversarial fast-path setup target for `Phi_15`. This keeps the
fast-path precision cap and pinned `p = 31` eight-linear split visible without
routing through the public fallback combinator. -/
setup_fixed_benchmark runFactorFastSetupAdvPhi15Checksum where {
    repeats := 5
    minTotalSeconds := 0.2
    maxSecondsPerCall := 6.0
    expectedHash := some 0xf58fd4dcfb9a609a
  }

/-
Fixed HO-2 adversarial shape: Swinnerton-Dyer `SD_3`. Full `factor` and
the CLD lattice tier on this degree-eight worst-case recombination input currently
exceed the `verify`-mode budget, so this reduced registration pins the same
canonical polynomial at the same conformance prime and records its eight-linear
modular split profile while keeping SD3 visible to `list` and `verify`.
-/
setup_fixed_benchmark runAdvSwinnertonDyerSD3ModularSplitChecksum where {
    repeats := 5
    minTotalSeconds := 0.2
    maxSecondsPerCall := 4.0
    expectedHash := some 0xe2da56484730f726
  }

/- Fixed lattice-tier target: full `factorLattice` on Swinnerton-Dyer `SD_3`,
certifying irreducibility via the early-stop separation certificate (#8395). -/
setup_fixed_benchmark runFactorLatticeAdvSwinnertonDyerSD3Checksum where {
    repeats := 5
    minTotalSeconds := 0.2
    maxSecondsPerCall := 4.0
    expectedHash := some 0xd91e58bd22915e00
  }

/- Fixed lattice-tier target: full `factorLattice` on Swinnerton-Dyer
`SD_4` (degree 16), the extreme-`r` tail case for the #8395 early stop. -/
setup_fixed_benchmark runFactorLatticeAdvSwinnertonDyerSD4Checksum where {
    repeats := 5
    minTotalSeconds := 0.2
    maxSecondsPerCall := 6.0
    expectedHash := some 0x687e925fbe11193b
  }

/- Fixed bottom-rung verified-Isabelle comparator pair. Both targets return the
same canonical factor-multiset checksum for `(x^2 - 2)(x^2 - 3)`; scheduled runs use
`compare runFactorIsabelleDomainChecksum runIsabelleFactorChecksum` to record
the verified-to-verified ratio. -/
setup_fixed_benchmark runFactorIsabelleDomainChecksum where {
    repeats := 3
    maxSecondsPerCall := 20.0
    expectedHash := some (Hashable.hash (checksumCanonicalLeanFactorization (ZPoly.factorize advQuadSqrt2Sqrt3)))
    tags := #[scheduledHardwareTag]
  }

setup_fixed_benchmark runIsabelleFactorChecksum where {
    repeats := 3
    maxSecondsPerCall := 60.0
    expectedHash := some (Hashable.hash (checksumCanonicalLeanFactorization (ZPoly.factorize advQuadSqrt2Sqrt3)))
    tags := #[scheduledHardwareTag]
  }

setup_fixed_benchmark runIsabelleFactorBaselineChecksum where {
    repeats := 3
    maxSecondsPerCall := 60.0
    expectedHash := some (Hashable.hash (checksumCanonicalFactorization 1 #[]))
    tags := #[scheduledHardwareTag]
  }

/- Per-rung verified-Isabelle comparator registrations on `smokeInput n` for
`n = 2, 3, 4, 5`. The matched Lean timings come from the clean historical
`runFactorChecksum` parametric audit at the corresponding rung of
`splitScientificSchedule`; together they form the retained `hex/isabelle`
ratio ladder. Tagged `scheduled-hardware` so CI's `verify` does not invoke
the AFP-extracted comparator. -/
setup_fixed_benchmark runIsabelleSplitN2Checksum where {
    repeats := 3
    maxSecondsPerCall := 60.0
    expectedHash :=
      some (Hashable.hash (checksumCanonicalLeanFactorization (ZPoly.factorize (smokeInput 2))))
    tags := #[scheduledHardwareTag]
  }

setup_fixed_benchmark runIsabelleSplitN3Checksum where {
    repeats := 3
    maxSecondsPerCall := 60.0
    expectedHash :=
      some (Hashable.hash (checksumCanonicalLeanFactorization (ZPoly.factorize (smokeInput 3))))
    tags := #[scheduledHardwareTag]
  }

setup_fixed_benchmark runIsabelleSplitN4Checksum where {
    repeats := 3
    maxSecondsPerCall := 60.0
    expectedHash :=
      some (Hashable.hash (checksumCanonicalLeanFactorization (ZPoly.factorize (smokeInput 4))))
    tags := #[scheduledHardwareTag]
  }

setup_fixed_benchmark runIsabelleSplitN5Checksum where {
    repeats := 3
    maxSecondsPerCall := 60.0
    expectedHash :=
      some (Hashable.hash (checksumCanonicalLeanFactorization (ZPoly.factorize (smokeInput 5))))
    tags := #[scheduledHardwareTag]
  }

/- Per-rung verified-Isabelle comparator registrations on the encoded
degree/height inputs at each schedule rung. The first five cover
`degreeHeightSchedule = #[3002, 4002, 4008, 5008, 6032]` (paired with
`runFactorDegreeHeightChecksum`); the
last three cover the smaller-degree `slowDegreeHeightSchedule = #[1002, 2002,
3008]` (paired with `runFactorSlowDegreeHeightChecksum`). -/
setup_fixed_benchmark runIsabelleDegreeHeight3x2Checksum where {
    repeats := 3
    maxSecondsPerCall := 60.0
    expectedHash := some (Hashable.hash (checksumCanonicalLeanFactorization
      (ZPoly.factorize (prepDegreeHeightInput (encodeDegreeHeightParam 3 2)).poly)))
    tags := #[scheduledHardwareTag]
  }

setup_fixed_benchmark runIsabelleDegreeHeight4x2Checksum where {
    repeats := 3
    maxSecondsPerCall := 60.0
    expectedHash := some (Hashable.hash (checksumCanonicalLeanFactorization
      (ZPoly.factorize (prepDegreeHeightInput (encodeDegreeHeightParam 4 2)).poly)))
    tags := #[scheduledHardwareTag]
  }

setup_fixed_benchmark runIsabelleDegreeHeight4x8Checksum where {
    repeats := 3
    maxSecondsPerCall := 60.0
    expectedHash := some (Hashable.hash (checksumCanonicalLeanFactorization
      (ZPoly.factorize (prepDegreeHeightInput (encodeDegreeHeightParam 4 8)).poly)))
    tags := #[scheduledHardwareTag]
  }

setup_fixed_benchmark runIsabelleDegreeHeight5x8Checksum where {
    repeats := 3
    maxSecondsPerCall := 60.0
    expectedHash := some (Hashable.hash (checksumCanonicalLeanFactorization
      (ZPoly.factorize (prepDegreeHeightInput (encodeDegreeHeightParam 5 8)).poly)))
    tags := #[scheduledHardwareTag]
  }

setup_fixed_benchmark runIsabelleDegreeHeight6x32Checksum where {
    repeats := 3
    maxSecondsPerCall := 60.0
    expectedHash := some (Hashable.hash (checksumCanonicalLeanFactorization
      (ZPoly.factorize (prepDegreeHeightInput (encodeDegreeHeightParam 6 32)).poly)))
    tags := #[scheduledHardwareTag]
  }

setup_fixed_benchmark runIsabelleDegreeHeight1x2Checksum where {
    repeats := 3
    maxSecondsPerCall := 60.0
    expectedHash := some (Hashable.hash (checksumCanonicalLeanFactorization
      (ZPoly.factorize (prepDegreeHeightInput (encodeDegreeHeightParam 1 2)).poly)))
    tags := #[scheduledHardwareTag]
  }

setup_fixed_benchmark runIsabelleDegreeHeight2x2Checksum where {
    repeats := 3
    maxSecondsPerCall := 60.0
    expectedHash := some (Hashable.hash (checksumCanonicalLeanFactorization
      (ZPoly.factorize (prepDegreeHeightInput (encodeDegreeHeightParam 2 2)).poly)))
    tags := #[scheduledHardwareTag]
  }

setup_fixed_benchmark runIsabelleDegreeHeight3x8Checksum where {
    repeats := 3
    maxSecondsPerCall := 60.0
    expectedHash := some (Hashable.hash (checksumCanonicalLeanFactorization
      (ZPoly.factorize (prepDegreeHeightInput (encodeDegreeHeightParam 3 8)).poly)))
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
      some (Hashable.hash (checksumCanonicalLeanFactorization (ZPoly.factorize advX4Plus1)))
    tags := #[scheduledHardwareTag]
  }

setup_fixed_benchmark runIsabelleAdvPhi15Checksum where {
    repeats := 3
    maxSecondsPerCall := 60.0
    expectedHash :=
      some (Hashable.hash (checksumCanonicalLeanFactorization (ZPoly.factorize advPhi15)))
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
