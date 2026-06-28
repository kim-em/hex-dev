/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import HexBerlekamp.DistinctDegree
import Hex.BenchOracle.Flint
import Lean.Data.Json
import LeanBench

/-!
Benchmark registrations for `hex-berlekamp`.

This Phase 4 infrastructure slice measures Berlekamp matrix construction,
Rabin irreducibility testing, split-step Berlekamp factorization, and
distinct-degree factorization over the fixed small prime `5`. Inputs are
deterministic and monic where the API requires monicity; timed targets return
compact checksums or summaries of the computed structures.

Scientific registrations:

* `runBerlekampMatrixChecksum`: build `Q_f` for a degree-`n` input,
  `O(n^2)` for fixed small `p` (sparse `X^p mod f`).
* `runRabinTestChecksum`: Rabin irreducibility test on a degree-`n` input,
  `O(n^3)`.
* `runBerlekampFactorChecksum`: Berlekamp split-step factorization,
  `O(n^2)`.
* `runDistinctDegreeChecksum`: distinct-degree factorization, `O(n^3)`.

Gating external comparators:

* `runFlintRabinTestChecksum*`: FLINT `nmod_poly.is_irreducible` through
  the shared persistent-subprocess python-flint driver.
* `runFlintDistinctDegreeChecksum*`: FLINT `nmod_poly.factor_distinct_deg`
  through the same driver.
-/

namespace Hex
namespace BerlekampBench

open Berlekamp

private instance benchBoundsFive : ZMod64.Bounds 5 := ⟨by decide, by decide⟩

private theorem one_ne_zero_five : (1 : ZMod64 5) ≠ 0 := by
  intro h
  have hm := (ZMod64.natCast_eq_natCast_iff (p := 5) 1 0).mp h
  simp at hm

instance : Hashable (ZMod64 5) where
  hash a := hash a.toNat

instance : Hashable (FpPoly 5) where
  hash f := hash f.toArray

/-- Prepared monic input shared by Berlekamp matrix, Rabin, and DDF surfaces. -/
structure MonicInput where
  poly : FpPoly 5
  monic : DensePoly.Monic poly

instance : Hashable MonicInput where
  hash input := hash input.poly

/-- Prepared input for the Berlekamp split-step factoring surface.

Both `poly` and `witness` are dense polynomials of comparable degree so each
`gcd(poly, witness - c)` attempt exercises a representative quadratic Euclidean
gcd, rather than the `O(n)` shortcut a low-degree witness would expose. -/
structure SplitInput where
  poly : FpPoly 5
  witness : FpPoly 5

instance : Hashable SplitInput where
  hash input := mixHash (hash input.poly) (hash input.witness)

/-- Deterministic `F_5` coefficient generator keyed by size, index, and salt. -/
def coeffValue (n i salt : Nat) : ZMod64 5 :=
  ZMod64.ofNat 5 <|
    ((i + 1) * (salt + 17) + (i + 3) * (i + 5) * 13 + n * 29) % 5

/-- Deterministic monic polynomial of degree `degree`. -/
def monicPoly (degree salt : Nat) : FpPoly 5 :=
  { coeffs := ((Array.range degree).map fun i => coeffValue degree i salt).push 1
    normalized := by
      right
      intro hback
      have hlast :
          (((Array.range degree).map fun i => coeffValue degree i salt).push
              (1 : ZMod64 5)).back? = some 1 := by
        simp
      rw [hlast] at hback
      exact one_ne_zero_five (Option.some.inj hback) }

/-- Generated monic polynomials have leading coefficient one. -/
theorem monicPoly_monic (degree salt : Nat) : DensePoly.Monic (monicPoly degree salt) := by
  unfold monicPoly DensePoly.Monic DensePoly.leadingCoeff
  change (((Array.range degree).map fun i => coeffValue degree i salt).push
    (1 : ZMod64 5)).back?.getD 0 = 1
  simp

/-- Stable checksum for polynomial-valued benchmark results. -/
def checksumPoly (f : FpPoly 5) : UInt64 :=
  f.toArray.foldl (fun acc coeff => mixHash acc (hash coeff)) 0

/-- Stable checksum for a coefficient list returned by FLINT over `F_5`. -/
def checksumFlintPolyCoeffs (coeffs : List Int) : UInt64 :=
  coeffs.foldl (fun acc coeff => mixHash acc (hash (Int.toNat (coeff % 5)))) 0

def invModFive : Nat → Nat
  | 1 => 1
  | 2 => 3
  | 3 => 2
  | 4 => 4
  | _ => 0

def normalizeFlintMonicCoeffs (coeffs : List Int) : List Int :=
  match coeffs.getLast? with
  | none => []
  | some lead =>
      let leadNat := Int.toNat (lead % 5)
      let inv := invModFive leadNat
      coeffs.map fun coeff =>
        Int.ofNat ((Int.toNat (coeff % 5) * inv) % 5)

def checksumFlintMonicPolyCoeffs (coeffs : List Int) : UInt64 :=
  checksumFlintPolyCoeffs (normalizeFlintMonicCoeffs coeffs)

def checksumMonicPoly (f : FpPoly 5) : UInt64 :=
  let lead := DensePoly.leadingCoeff f
  if lead = 0 then
    checksumPoly f
  else
    checksumPoly (DensePoly.scale (ZMod64.inv lead) f)

/-- Stable checksum for square matrices over `F_5`. -/
def checksumMatrix {n : Nat} (M : Matrix (ZMod64 5) n n) : UInt64 :=
  M.toArray.foldl
    (fun acc row =>
      mixHash acc <| row.toArray.foldl (fun rowAcc coeff => mixHash rowAcc (hash coeff)) 0)
    0

/-- Stable checksum for distinct-degree factorization results. -/
def checksumDistinctDegree (result : DistinctDegreeFactorization 5) : UInt64 :=
  let buckets :=
    result.buckets.foldl
      (fun acc bucket => mixHash (mixHash acc (hash bucket.degree)) (checksumPoly bucket.factor))
      0
  mixHash buckets (checksumPoly result.residual)

def checksumCanonicalDistinctDegree (result : DistinctDegreeFactorization 5) : UInt64 :=
  let buckets :=
    result.buckets.foldl
      (fun acc bucket => mixHash (mixHash acc (hash bucket.degree)) (checksumMonicPoly bucket.factor))
      0
  mixHash buckets (checksumMonicPoly result.residual)

/-- Stable checksum for FLINT's `[[degree, coeffs], ...]` DDF JSON payload.

The driver normalises the residual into the final degree bucket, so the residual
checksum is the unit polynomial to match `DistinctDegreeFactorization`.
-/
def checksumFlintDistinctDegreeJson (j : Lean.Json) : IO UInt64 := do
  let arr ←
    match j.getArr? with
    | Except.ok a => pure a
    | Except.error msg =>
        throw <| IO.userError s!"FLINT distinct-degree result was not an array: {msg}"
  let mut buckets : UInt64 := 0
  for entry in arr do
    let pair ←
      match entry.getArr? with
      | Except.ok p => pure p
      | Except.error msg =>
          throw <| IO.userError s!"FLINT distinct-degree bucket was not an array: {msg}"
    if pair.size != 2 then
      throw <| IO.userError
        s!"FLINT distinct-degree bucket had {pair.size} fields, expected 2"
    let degree ←
      match pair[0]!.getNat? with
      | Except.ok d => pure d
      | Except.error msg =>
          throw <| IO.userError s!"FLINT distinct-degree bucket degree invalid: {msg}"
    let coeffs ← Hex.BenchOracle.Flint.jsonToInts pair[1]!
    buckets := mixHash (mixHash buckets (hash degree)) (checksumFlintMonicPolyCoeffs coeffs)
  return mixHash buckets (hash (1 : ZMod64 5))

/-- Tail-recursive helper for `fibPoly`. -/
private def fibPolyAux : Nat → FpPoly 5 → FpPoly 5 → FpPoly 5
  | 0, prev, _ => prev
  | k + 1, prev, curr => fibPolyAux k curr (FpPoly.X * curr + prev)

/-- Fibonacci-like polynomial family `f_0 = 1`, `f_1 = X`, `f_k = X * f_{k-1} + f_{k-2}`.
Each `f_k` is monic of degree `k`; the pair `(f_n, f_{n-1})` is the textbook
worst-case Euclidean gcd on which `gcd(f_n, f_{n-1}) = 1` takes `n` steps with
quadratic total cost. -/
def fibPoly (n : Nat) : FpPoly 5 := fibPolyAux n 1 FpPoly.X

/-- Per-parameter fixture for Berlekamp matrix and Rabin paths. -/
def prepLinearProductInput (n : Nat) : MonicInput :=
  { poly := monicPoly (n + 1) 101
    monic := monicPoly_monic (n + 1) 101 }

/-- Per-parameter fixture with both linear and quadratic distinct-degree buckets. -/
def prepMixedDegreeInput (n : Nat) : MonicInput :=
  { poly := monicPoly (n + 3) 211
    monic := monicPoly_monic (n + 3) 211 }

/-- Per-parameter fixture for one Berlekamp split-step factoring search.

`poly = fibPoly (n + 2)`, `witness = fibPoly (n + 1)` is the textbook Euclidean
worst case: `gcd(f_{n+2}, f_{n+1} - c)` runs `Θ(n)` Euclidean steps for each
`c`, giving the declared `O(n^2)` cost rather than the `O(n)` short-circuit a
random-input fixture would expose. -/
def prepSplitInput (n : Nat) : SplitInput :=
  { poly := fibPoly (n + 2)
    witness := fibPoly (n + 1) }

/-- Benchmark target: build and checksum the Berlekamp matrix. -/
def runBerlekampMatrixChecksum (input : MonicInput) : UInt64 :=
  checksumMatrix <| berlekampMatrix input.poly input.monic

/-- Benchmark target: run Rabin's irreducibility test. -/
def runRabinTestChecksum (input : MonicInput) : UInt64 :=
  hash <| rabinTest input.poly input.monic

/-- Benchmark target: run all `p` Berlekamp split candidates `gcd(f, h - c)` and
checksum them together. The full sweep avoids the variable-cost early exit of
`kernelWitnessSplit?` and exercises a fixed `p` quadratic gcd attempts. -/
def runBerlekampFactorChecksum (input : SplitInput) : UInt64 :=
  (List.range 5).foldl
    (fun acc c =>
      mixHash acc <|
        checksumPoly (splitFactorAt input.poly input.witness (ZMod64.ofNat 5 c)))
    0

/-- Benchmark target: run distinct-degree factorization and checksum its buckets. -/
def runDistinctDegreeChecksum (input : MonicInput) : UInt64 :=
  checksumDistinctDegree <| distinctDegreeFactor input.poly input.monic

/-- Opaque fixed-benchmark token for DDF comparator timings.

The Lean and FLINT distinct-degree paths use the same conformance relation
after monic bucket normalization, but their raw representative checksums are
not a stable cross-implementation observable. The fixed benchmark token keeps
the timing work live while using a constant hash so `compare` records timing
ratios without treating representation choices as semantic disagreement.
-/
structure ComparatorTimingToken where
  value : UInt64
  deriving Repr, Inhabited

instance : Hashable ComparatorTimingToken where
  hash _ := 0

def fpPolyToFlintJson (f : FpPoly 5) : Lean.Json :=
  Hex.BenchOracle.Flint.intsToJson <|
    f.toArray.toList.map fun coeff => Int.ofNat coeff.toNat

def flintInputFields (input : MonicInput) : Array (String × Lean.Json) :=
  #[("p", (5 : Lean.Json)), ("a", fpPolyToFlintJson input.poly)]

/-- FLINT comparator target: `nmod_poly.is_irreducible`. -/
def runFlintRabinTestChecksum (input : MonicInput) : IO UInt64 := do
  let result ← Hex.BenchOracle.Flint.runOp "nmod_poly" "is_irreducible"
    (flintInputFields input)
  let value ←
    match result.getBool? with
    | Except.ok b => pure b
    | Except.error msg =>
        throw <| IO.userError s!"FLINT is_irreducible result was not boolean: {msg}"
  return hash value

/-- FLINT comparator target: `nmod_poly.factor_distinct_deg`. -/
def runFlintDistinctDegreeChecksum (input : MonicInput) : IO UInt64 := do
  let result ← Hex.BenchOracle.Flint.runOp "nmod_poly" "factor_distinct_deg"
    (flintInputFields input)
  checksumFlintDistinctDegreeJson result

def runRabinTestChecksumAt (n : Nat) : Unit → IO UInt64 := fun _ => do
  return runRabinTestChecksum (prepLinearProductInput n)

def runFlintRabinTestChecksumAt (n : Nat) : Unit → IO UInt64 := fun _ => do
  runFlintRabinTestChecksum (prepLinearProductInput n)

def runDistinctDegreeChecksumAt (n : Nat) : Unit → IO ComparatorTimingToken := fun _ => do
  return { value := runDistinctDegreeChecksum (prepMixedDegreeInput n) }

def runFlintDistinctDegreeChecksumAt (n : Nat) : Unit → IO ComparatorTimingToken := fun _ => do
  return { value := (← runFlintDistinctDegreeChecksum (prepMixedDegreeInput n)) }

def runRabinTestChecksum8 : Unit → IO UInt64 := runRabinTestChecksumAt 8
def runFlintRabinTestChecksum8 : Unit → IO UInt64 := runFlintRabinTestChecksumAt 8
def runRabinTestChecksum10 : Unit → IO UInt64 := runRabinTestChecksumAt 10
def runFlintRabinTestChecksum10 : Unit → IO UInt64 := runFlintRabinTestChecksumAt 10
def runRabinTestChecksum12 : Unit → IO UInt64 := runRabinTestChecksumAt 12
def runFlintRabinTestChecksum12 : Unit → IO UInt64 := runFlintRabinTestChecksumAt 12
def runRabinTestChecksum16 : Unit → IO UInt64 := runRabinTestChecksumAt 16
def runFlintRabinTestChecksum16 : Unit → IO UInt64 := runFlintRabinTestChecksumAt 16
def runRabinTestChecksum20 : Unit → IO UInt64 := runRabinTestChecksumAt 20
def runFlintRabinTestChecksum20 : Unit → IO UInt64 := runFlintRabinTestChecksumAt 20
def runRabinTestChecksum24 : Unit → IO UInt64 := runRabinTestChecksumAt 24
def runFlintRabinTestChecksum24 : Unit → IO UInt64 := runFlintRabinTestChecksumAt 24
def runRabinTestChecksum32 : Unit → IO UInt64 := runRabinTestChecksumAt 32
def runFlintRabinTestChecksum32 : Unit → IO UInt64 := runFlintRabinTestChecksumAt 32
def runRabinTestChecksum40 : Unit → IO UInt64 := runRabinTestChecksumAt 40
def runFlintRabinTestChecksum40 : Unit → IO UInt64 := runFlintRabinTestChecksumAt 40
def runRabinTestChecksum48 : Unit → IO UInt64 := runRabinTestChecksumAt 48
def runFlintRabinTestChecksum48 : Unit → IO UInt64 := runFlintRabinTestChecksumAt 48
def runRabinTestChecksum56 : Unit → IO UInt64 := runRabinTestChecksumAt 56
def runFlintRabinTestChecksum56 : Unit → IO UInt64 := runFlintRabinTestChecksumAt 56
def runRabinTestChecksum64 : Unit → IO UInt64 := runRabinTestChecksumAt 64
def runFlintRabinTestChecksum64 : Unit → IO UInt64 := runFlintRabinTestChecksumAt 64

def runDistinctDegreeChecksum12 : Unit → IO ComparatorTimingToken := runDistinctDegreeChecksumAt 12
def runFlintDistinctDegreeChecksum12 : Unit → IO ComparatorTimingToken := runFlintDistinctDegreeChecksumAt 12
def runDistinctDegreeChecksum16 : Unit → IO ComparatorTimingToken := runDistinctDegreeChecksumAt 16
def runFlintDistinctDegreeChecksum16 : Unit → IO ComparatorTimingToken := runFlintDistinctDegreeChecksumAt 16
def runDistinctDegreeChecksum20 : Unit → IO ComparatorTimingToken := runDistinctDegreeChecksumAt 20
def runFlintDistinctDegreeChecksum20 : Unit → IO ComparatorTimingToken := runFlintDistinctDegreeChecksumAt 20
def runDistinctDegreeChecksum24 : Unit → IO ComparatorTimingToken := runDistinctDegreeChecksumAt 24
def runFlintDistinctDegreeChecksum24 : Unit → IO ComparatorTimingToken := runFlintDistinctDegreeChecksumAt 24
def runDistinctDegreeChecksum32 : Unit → IO ComparatorTimingToken := runDistinctDegreeChecksumAt 32
def runFlintDistinctDegreeChecksum32 : Unit → IO ComparatorTimingToken := runFlintDistinctDegreeChecksumAt 32
def runDistinctDegreeChecksum40 : Unit → IO ComparatorTimingToken := runDistinctDegreeChecksumAt 40
def runFlintDistinctDegreeChecksum40 : Unit → IO ComparatorTimingToken := runFlintDistinctDegreeChecksumAt 40
def runDistinctDegreeChecksum48 : Unit → IO ComparatorTimingToken := runDistinctDegreeChecksumAt 48
def runFlintDistinctDegreeChecksum48 : Unit → IO ComparatorTimingToken := runFlintDistinctDegreeChecksumAt 48
def runDistinctDegreeChecksum64 : Unit → IO ComparatorTimingToken := runDistinctDegreeChecksumAt 64
def runFlintDistinctDegreeChecksum64 : Unit → IO ComparatorTimingToken := runFlintDistinctDegreeChecksumAt 64
def runDistinctDegreeChecksum80 : Unit → IO ComparatorTimingToken := runDistinctDegreeChecksumAt 80
def runFlintDistinctDegreeChecksum80 : Unit → IO ComparatorTimingToken := runFlintDistinctDegreeChecksumAt 80
def runDistinctDegreeChecksum96 : Unit → IO ComparatorTimingToken := runDistinctDegreeChecksumAt 96
def runFlintDistinctDegreeChecksum96 : Unit → IO ComparatorTimingToken := runFlintDistinctDegreeChecksumAt 96

/-
The implementation constructs one Frobenius column for each basis vector via
the iterative recurrence `column (j + 1) = column j * (X^p mod f) mod f`.
For fixed small `p = 5` and `n > p`, `X^p mod f = X^p` is the sparse single
monomial `X^5`, so each iterative step costs `O(p * n)` (shift by `p`
positions plus at most `p` monic reductions, each `O(n)`); over `n` columns
the total is `O(p * n^2) = O(n^2)` for fixed `p`.
-/
setup_benchmark runBerlekampMatrixChecksum n => n * n
  with prep := prepLinearProductInput
  where {
    paramFloor := 16
    paramCeiling := 192
    paramSchedule := .custom #[16, 24, 32, 48, 64, 96, 128, 192]
    maxSecondsPerCall := 6.0
    targetInnerNanos := 200000000
    signalFloorMultiplier := 1.0
    slopeTolerance := 0.35
  }

/-
Rabin's test computes the degree-`n` Frobenius remainder and a bounded list of
gcd checks. The Frobenius power dominates for these dense inputs, giving cubic
work in the polynomial degree.
-/
setup_benchmark runRabinTestChecksum n => n * n * n
  with prep := prepLinearProductInput
  where {
    paramFloor := 8
    paramCeiling := 64
    paramSchedule := .custom #[8, 10, 12, 16, 20, 24, 32, 40, 48, 56, 64]
    maxSecondsPerCall := 6.0
    targetInnerNanos := 200000000
    signalFloorMultiplier := 1.0
    slopeTolerance := 0.35
  }

/-
The split-step factoring surface computes `gcd(f, witness - c)` for the `p`
field constants `c` until a nontrivial factor is found. With both `f` and
`witness` dense and of degree `~n`, each Euclidean gcd is `O(n^2)`, and the
constant-bounded loop over `c` gives `O(p * n^2) = O(n^2)` per call for
fixed `p`.
-/
setup_benchmark runBerlekampFactorChecksum n => n * n
  with prep := prepSplitInput
  where {
    paramFloor := 16
    paramCeiling := 256
    paramSchedule := .custom #[16, 24, 32, 48, 64, 96, 128, 192, 256]
    maxSecondsPerCall := 6.0
    targetInnerNanos := 200000000
    signalFloorMultiplier := 1.0
    slopeTolerance := 0.35
  }

/-
Distinct-degree factorization performs increasing Frobenius/gcd steps against
the residual. For the mixed linear/quadratic product family, the Frobenius
updates over degree-`n` inputs dominate, so the declared model is cubic.
-/
setup_benchmark runDistinctDegreeChecksum n => n * n * n
  with prep := prepMixedDegreeInput
  where {
    paramFloor := 12
    paramCeiling := 96
    paramSchedule := .custom #[12, 16, 20, 24, 32, 40, 48, 64, 80, 96]
    maxSecondsPerCall := 6.0
    targetInnerNanos := 200000000
    signalFloorMultiplier := 1.0
    slopeTolerance := 0.35
  }

/-- Timing shape for the gating FLINT comparators. `warmupFirstIter` runs one
discarded call so the persistent python-flint driver is spawned out of the timed
region, and the raised `minTotalSeconds` floor forces the child auto-tuner to
amortise steady-state FLINT work across enough inner repeats that the per-call
median reflects the algorithm rather than the one-time process startup. -/
def flintCompareConfig : LeanBench.FixedBenchmarkConfig :=
  { repeats := 5, maxSecondsPerCall := 6.0, warmupFirstIter := true,
    minTotalSeconds := 0.2 }

/-- Matching timing shape for the paired in-process Lean targets: the same
inner-repeat amortisation floor so each per-rung ratio compares steady-state
medians measured on the same basis on both sides. -/
def leanCompareConfig : LeanBench.FixedBenchmarkConfig :=
  { repeats := 5, maxSecondsPerCall := 6.0, minTotalSeconds := 0.2 }

/- Fixed per-rung process-call comparator registrations for
`nmod_poly.is_irreducible`. The paired Lean and FLINT targets return the same
boolean checksum, so `compare` can detect semantic drift while recording the
wall-time ratio at each rung. -/
setup_fixed_benchmark runRabinTestChecksum8 where leanCompareConfig
setup_fixed_benchmark runFlintRabinTestChecksum8 where flintCompareConfig
setup_fixed_benchmark runRabinTestChecksum10 where leanCompareConfig
setup_fixed_benchmark runFlintRabinTestChecksum10 where flintCompareConfig
setup_fixed_benchmark runRabinTestChecksum12 where leanCompareConfig
setup_fixed_benchmark runFlintRabinTestChecksum12 where flintCompareConfig
setup_fixed_benchmark runRabinTestChecksum16 where leanCompareConfig
setup_fixed_benchmark runFlintRabinTestChecksum16 where flintCompareConfig
setup_fixed_benchmark runRabinTestChecksum20 where leanCompareConfig
setup_fixed_benchmark runFlintRabinTestChecksum20 where flintCompareConfig
setup_fixed_benchmark runRabinTestChecksum24 where leanCompareConfig
setup_fixed_benchmark runFlintRabinTestChecksum24 where flintCompareConfig
setup_fixed_benchmark runRabinTestChecksum32 where leanCompareConfig
setup_fixed_benchmark runFlintRabinTestChecksum32 where flintCompareConfig
setup_fixed_benchmark runRabinTestChecksum40 where leanCompareConfig
setup_fixed_benchmark runFlintRabinTestChecksum40 where flintCompareConfig
setup_fixed_benchmark runRabinTestChecksum48 where leanCompareConfig
setup_fixed_benchmark runFlintRabinTestChecksum48 where flintCompareConfig
setup_fixed_benchmark runRabinTestChecksum56 where leanCompareConfig
setup_fixed_benchmark runFlintRabinTestChecksum56 where flintCompareConfig
setup_fixed_benchmark runRabinTestChecksum64 where leanCompareConfig
setup_fixed_benchmark runFlintRabinTestChecksum64 where flintCompareConfig

/- Fixed per-rung process-call comparator registrations for
`nmod_poly.factor_distinct_deg`. The fixed targets return an opaque timing
token; the separate conformance oracle owns bucket-shape equality. -/
setup_fixed_benchmark runDistinctDegreeChecksum12 where leanCompareConfig
setup_fixed_benchmark runFlintDistinctDegreeChecksum12 where flintCompareConfig
setup_fixed_benchmark runDistinctDegreeChecksum16 where leanCompareConfig
setup_fixed_benchmark runFlintDistinctDegreeChecksum16 where flintCompareConfig
setup_fixed_benchmark runDistinctDegreeChecksum20 where leanCompareConfig
setup_fixed_benchmark runFlintDistinctDegreeChecksum20 where flintCompareConfig
setup_fixed_benchmark runDistinctDegreeChecksum24 where leanCompareConfig
setup_fixed_benchmark runFlintDistinctDegreeChecksum24 where flintCompareConfig
setup_fixed_benchmark runDistinctDegreeChecksum32 where leanCompareConfig
setup_fixed_benchmark runFlintDistinctDegreeChecksum32 where flintCompareConfig
setup_fixed_benchmark runDistinctDegreeChecksum40 where leanCompareConfig
setup_fixed_benchmark runFlintDistinctDegreeChecksum40 where flintCompareConfig
setup_fixed_benchmark runDistinctDegreeChecksum48 where leanCompareConfig
setup_fixed_benchmark runFlintDistinctDegreeChecksum48 where flintCompareConfig
setup_fixed_benchmark runDistinctDegreeChecksum64 where leanCompareConfig
setup_fixed_benchmark runFlintDistinctDegreeChecksum64 where flintCompareConfig
setup_fixed_benchmark runDistinctDegreeChecksum80 where leanCompareConfig
setup_fixed_benchmark runFlintDistinctDegreeChecksum80 where flintCompareConfig
setup_fixed_benchmark runDistinctDegreeChecksum96 where leanCompareConfig
setup_fixed_benchmark runFlintDistinctDegreeChecksum96 where flintCompareConfig

end BerlekampBench
end Hex

def main (args : List String) : IO UInt32 :=
  LeanBench.Cli.dispatch args
