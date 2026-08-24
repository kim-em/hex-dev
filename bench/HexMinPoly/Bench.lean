/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import HexMinPoly
import HexPolyFp.PrimeField
import Hex.BenchOracle.Flint
import Hex.BenchOracle.Pari
import LeanBench

/-!
Benchmark registrations for deterministic matrix minimal polynomials.

The stage targets use a nilpotent shift to expose operation-count scaling without
rational coefficient growth. The random, modular-companion, derogatory, and
rational-companion families separately exercise dense generic work, fixed-width
full-degree work, repeated low-order blocks, and a closed-form full-degree answer.
The `metrics` command times the public operation and reports `deg m_A` and the
sum of the basis-vector order degrees for every family. On random rational inputs
it also independently instruments the order/lcm fold and records peak coefficient
bit size. FLINT and PARI are fixed-rung, informational comparators driven through
the shared persistent subprocesses.
-/

namespace Hex.MinPolyBench

private def signedEntry (n i j salt : Nat) : Int :=
  Int.ofNat ((i * (n + 7) + j * 13 + salt * 17 + i * j * 3) % 23) - 11

private def randomRatMatrix (n salt : Nat) : Matrix Rat n n :=
  Matrix.ofFn fun i j => (signedEntry n i.val j.val salt : Rat)

/- A nilpotent shift keeps exact-rational coefficients at zero or one while
still supplying Krylov chains of every length from `1` through `n`. The dense
matrix kernels do not exploit its sparsity, so it isolates operation-count
scaling without coefficient-bit growth. -/
private def shiftMatrix (n : Nat) : Matrix Rat n n :=
  Matrix.ofFn fun i j => if i.val + 1 = j.val then 1 else 0

private def orderDegreeSum {F : Type} [Lean.Grind.Field F] [DecidableEq F]
    {n : Nat} (A : Matrix F n n) : Nat :=
  (List.finRange n).foldl
    (fun total i => total + Matrix.krylovDeg A (Matrix.basisVec n i)) 0

private def checksumPoly {F : Type} [Hashable F] [Zero F] [DecidableEq F]
    (p : DensePoly F) : UInt64 :=
  hash p.toArray

private def checksumMinPoly {F : Type} [Lean.Grind.Field F] [DecidableEq F]
    [Hashable F] {n : Nat} (A : Matrix F n n) : UInt64 :=
  checksumPoly (Matrix.minPoly A)

private def checksumVector {F : Type} [Hashable F] {n : Nat}
    (v : Vector F n) : UInt64 :=
  hash v.toArray

private def checksumMatrix {F : Type} [Hashable F] {n m : Nat}
    (A : Matrix F n m) : UInt64 :=
  A.rows.toArray.foldl
    (fun checksum row => mixHash checksum (checksumVector row))
    (hash (n, m))

/-- Prepared exact-rational input shared by the stage-level benchmark targets.
The dependent fields retain the matrix dimension without timing reconstruction. -/
structure WorkInput where
  n : Nat
  matrix : Matrix Rat n n
  vector : Vector Rat n
  polynomial : DensePoly Rat

instance : Hashable WorkInput where
  hash input := mixHash (hash input.n)
    (mixHash (checksumMatrix input.matrix)
      (mixHash (checksumVector input.vector) (checksumPoly input.polynomial)))

/-- Deterministic shift matrix, longest-chain vector, and degree-`n`
polynomial fixture. -/
def prepWorkInput (n : Nat) : WorkInput :=
  { n := n
    matrix := shiftMatrix n
    vector := Vector.ofFn fun i => if i.val + 1 = n then 1 else 0
    polynomial := DensePoly.ofCoeffs (Array.replicate (n + 1) 1) }

/-- Prepared certificate input used to isolate checker cost from production. -/
structure CertInput where
  n : Nat
  matrix : Matrix Rat n n
  cert : Matrix.MinPolyCert Rat n

/-- Construct the certificate once, outside the checker's timed region. -/
def prepCertInput (n : Nat) : CertInput :=
  let A := shiftMatrix n
  { n := n, matrix := A, cert := Matrix.minPolyCert A }

/-- Evaluate a degree-`n` polynomial on a vector and force the result. -/
def runEvalVec (input : WorkInput) : UInt64 :=
  checksumVector (Matrix.evalVec input.polynomial input.matrix input.vector)

/-- Materialize `n + 1` shared Krylov rows and force every entry. -/
def runKrylovRows (input : WorkInput) : UInt64 :=
  (Matrix.krylovRows input.matrix input.vector (input.n + 1)).toArray.foldl
    (fun checksum row => mixHash checksum (checksumVector row))
    (hash input.n)

/-- Compute and force the order polynomial of the prepared vector. -/
def runVecMinPoly (input : WorkInput) : UInt64 :=
  checksumPoly (Matrix.vecMinPoly input.matrix input.vector)

/-- Compute and force the matrix minimal polynomial on the shared shift
family. -/
def runMinPoly (input : WorkInput) : UInt64 :=
  checksumPoly (Matrix.minPoly input.matrix)

private def checksumLcmStep (step : Matrix.LcmStep Rat) : UInt64 :=
  #[step.common, step.left, step.right, step.bezoutLeft,
      step.bezoutRight, step.result].foldl
    (fun checksum polynomial => mixHash checksum (checksumPoly polynomial)) 0

private def checksumOrder {n : Nat} (order : Matrix.OrderCert Rat n) : UInt64 :=
  mixHash (checksumPoly order.poly)
    (mixHash (hash order.deg) (checksumMatrix order.inv))

private def checksumCert {n : Nat} (cert : Matrix.MinPolyCert Rat n) : UInt64 :=
  let orders := cert.order.toArray.foldl
    (fun checksum order => mixHash checksum (checksumOrder order)) 0
  let steps := cert.steps.toArray.foldl
    (fun checksum step => mixHash checksum (checksumLcmStep step)) 0
  mixHash (checksumPoly cert.poly) (mixHash orders steps)

instance : Hashable CertInput where
  hash input := mixHash (hash input.n)
    (mixHash (checksumMatrix input.matrix) (checksumCert input.cert))

/-- Produce a complete certificate and force every polynomial and inverse. -/
def runMinPolyCert (input : WorkInput) : UInt64 :=
  checksumCert (Matrix.minPolyCert input.matrix)

/-- Check a certificate prepared outside the timed region. -/
def runCertCheck (input : CertInput) : UInt64 :=
  hash (input.cert.check input.matrix)

/-- Dense deterministic rational matrices, representative of the generic
full-degree case. -/
def runRandomDense (n : Nat) : UInt64 :=
  checksumMinPoly (randomRatMatrix n 1)

private instance benchBoundsFive : ZMod64.Bounds 5 := ⟨by decide, by decide⟩

private theorem benchPrimeFive : Hex.Nat.Prime 5 := by
  constructor
  · decide
  · intro m hm
    have hmle : m ≤ 5 := Nat.le_of_dvd (by decide : 0 < 5) hm
    have hcases : m = 0 ∨ m = 1 ∨ m = 2 ∨ m = 3 ∨ m = 4 ∨ m = 5 := by omega
    rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl
    · simp at hm
    · exact Or.inl rfl
    · simp at hm
    · simp at hm
    · simp at hm
    · exact Or.inr rfl

private instance benchPrimeModulusFive : ZMod64.PrimeModulus 5 :=
  ZMod64.primeModulusOfPrime benchPrimeFive

private instance : Hashable (ZMod64 5) where
  hash x := hash x.toNat

private def modularMatrix (n : Nat) : Matrix (ZMod64 5) n n :=
  let coefficient (j : Nat) := ZMod64.ofNat 5 ((j + 1) % 5)
  Matrix.ofFn fun i j =>
    if j.val = i.val + 1 then 1
    else if i.val + 1 = n then -coefficient j.val
    else 0

/-- Full-degree companion matrices over a fixed-width prime field. Their
nonzero constant coefficient makes every standard basis vector cyclic. -/
def runModular (n : Nat) : UInt64 :=
  checksumMinPoly (modularMatrix n)

private def derogatoryMatrix (n : Nat) : Matrix Rat n n :=
  Matrix.ofFn fun i j =>
    if i.val % 2 = 0 ∧ j.val = i.val + 1 then 1 else 0

/-- Repeated nilpotent blocks: the matrix grows while its minimal-polynomial
degree stays bounded by two. -/
def runDerogatory (n : Nat) : UInt64 :=
  checksumMinPoly (derogatoryMatrix n)

private def companionCoefficients (n : Nat) : Array Rat :=
  (Array.range (n + 1)).map fun i =>
    if i = n then 1 else (signedEntry n i 0 5 : Rat)

private def companionMatrix (n : Nat) : Matrix Rat n n :=
  let coefficients := companionCoefficients n
  Matrix.ofFn fun i j =>
    if j.val = i.val + 1 then 1
    else if i.val + 1 = n then -coefficients.getD j.val 0
    else 0

/-- Companion matrices, checked in the timed target against their defining
monic polynomial. -/
def runCompanion (n : Nat) : UInt64 :=
  let A := companionMatrix n
  let actual := Matrix.minPoly A
  let expected := DensePoly.ofCoeffs (companionCoefficients n)
  if actual = expected then checksumPoly actual
  else panic! "companion minimal-polynomial self-check failed"

private def randomSchedule : Array Nat := #[2, 3, 4, 5, 6, 8, 10, 12]
private def stageSchedule : Array Nat := #[2, 3, 4, 5, 6, 8, 10, 12, 14, 16, 20]
private def modularSchedule : Array Nat := #[2, 3, 4, 5, 6, 8, 10, 12, 16, 20, 24, 32]
private def derogatorySchedule : Array Nat := #[2, 4, 6, 8, 10, 12, 16, 20]
private def companionSchedule : Array Nat := #[2, 3, 4, 5, 6, 8, 10, 12]

private def intBits (value : Int) : Nat :=
  if value = 0 then 0 else Nat.log2 value.natAbs + 1

private def ratBits (value : Rat) : Nat :=
  max (intBits value.num) (Nat.log2 value.den + 1)

private def polyBits (p : DensePoly Rat) : Nat :=
  p.toArray.foldl (fun peak coefficient => max peak (ratBits coefficient)) 0

private structure Growth where
  poly : DensePoly Rat
  peakBits : Nat
  orderDegreeSum : Nat

/-- Independently replay the basis-order/lcm fold while retaining the largest
coefficient observed in an order polynomial or running lcm. -/
private def minPolyGrowth {n : Nat} (A : Matrix Rat n n) : Growth :=
  (List.finRange n).foldl (fun state i =>
    let order := Matrix.vecMinPoly A (Matrix.basisVec n i)
    let running := DensePoly.lcm state.poly order
    { poly := running
      peakBits := max state.peakBits (max (polyBits order) (polyBits running))
      orderDegreeSum := state.orderDegreeSum + order.degree?.getD 0 })
    { poly := 1, peakBits := 1, orderDegreeSum := 0 }

private def natJson (value : Nat) : Lean.Json :=
  Lean.Json.num (Lean.JsonNumber.fromNat value)

private def emitMetrics {F : Type} [Lean.Grind.Field F] [DecidableEq F]
    [Hashable F] {n : Nat} (family : String) (A : Matrix F n n)
    (instrumented : Option (DensePoly F × Nat × Nat) := none) : IO Unit := do
  let start ← IO.monoNanosNow
  let answer := Matrix.minPoly A
  let checksum := checksumPoly answer
  LeanBench.blackBox checksum
  let stop ← IO.monoNanosNow
  let (degreeSum, peakBits) ← match instrumented with
    | none => pure (orderDegreeSum A, none)
    | some (instrumentedAnswer, peak, sum) =>
        if instrumentedAnswer = answer then pure (sum, some peak)
        else throw <| IO.userError s!"{family}: growth instrumentation disagrees with minPoly"
  let base := [
    ("family", Lean.Json.str family),
    ("dimension", natJson n),
    ("elapsed_nanos", natJson (stop - start)),
    ("degree", natJson (answer.degree?.getD 0)),
    ("sum_order_degrees", natJson degreeSum),
    ("checksum", natJson checksum.toNat)]
  let fields := match peakBits with
    | none => base
    | some peak => base ++ [("peak_coefficient_bits", natJson peak)]
  IO.println (Lean.Json.mkObj fields).compress

/-- Emit wallclock and redundancy metrics for every specified family, plus
coefficient-growth instrumentation for the random rational family. -/
def metricsReport : IO UInt32 := do
  for n in randomSchedule do
    let A := randomRatMatrix n 1
    let growth := minPolyGrowth A
    emitMetrics "random-dense-minpoly" A
      (some (growth.poly, growth.peakBits, growth.orderDegreeSum))
  for n in modularSchedule do
    emitMetrics "modular-minpoly" (modularMatrix n)
  for n in derogatorySchedule do
    emitMetrics "derogatory-minpoly" (derogatoryMatrix n)
  for n in companionSchedule do
    emitMetrics "companion-minpoly" (companionMatrix n)
  return 0

/- Cost model: Horner evaluation performs `n + 1` dense matrix-vector
products, each quadratic in the dimension; hashing the output is linear. -/
setup_benchmark runEvalVec n => n * n * n
  with prep := prepWorkInput
  where {
    paramFloor := 2
    paramCeiling := 20
    paramSchedule := .custom stageSchedule
    maxSecondsPerCall := 8.0
    targetInnerNanos := 1000000000
    slopeTolerance := 0.45
  }

/- Cost model: the shared Krylov recurrence performs `n` dense
matrix-vector products of quadratic cost. Hashing all `(n + 1) * n` entries
is lower-order quadratic work. -/
setup_benchmark runKrylovRows n => n * n * n
  with prep := prepWorkInput
  where {
    paramFloor := 2
    paramCeiling := 20
    paramSchedule := .custom stageSchedule
    maxSecondsPerCall := 8.0
    targetInnerNanos := 1000000000
    slopeTolerance := 0.45
  }

/- Cost model: one vector order builds a cubic Krylov workspace and performs
dense row reduction on an `(n + 1) × n` matrix, also cubic. -/
setup_benchmark runVecMinPoly n => n * n * n
  with prep := prepWorkInput
  where {
    paramFloor := 2
    paramCeiling := 20
    paramSchedule := .custom stageSchedule
    maxSecondsPerCall := 8.0
    targetInnerNanos := 1000000000
    slopeTolerance := 0.45
  }

/- Cost model: the deterministic standard-basis sweep computes `n` vector
orders of cubic cost; polynomial LCM and result hashing are lower order. -/
setup_benchmark runMinPoly n => n * n * n * n
  with prep := prepWorkInput
  where {
    paramFloor := 2
    paramCeiling := 20
    paramSchedule := .custom stageSchedule
    maxSecondsPerCall := 8.0
    targetInnerNanos := 1000000000
    slopeTolerance := 0.45
  }

/- Cost model: certificate production performs the `n` cubic vector-order
and right-inverse computations in the basis sweep. Walking every witness for
the result hash costs at most cubic time and does not change the quartic
bound. -/
setup_benchmark runMinPolyCert n => n * n * n * n
  with prep := prepWorkInput
  where {
    paramFloor := 2
    paramCeiling := 20
    paramSchedule := .custom stageSchedule
    maxSecondsPerCall := 8.0
    targetInnerNanos := 1000000000
    slopeTolerance := 0.50
  }

/- Cost model: checking each of `n` order witnesses rebuilds a cubic Krylov
prefix/right-inverse product in the worst case. Polynomial identity checks
are lower order, giving a quartic checker bound. -/
setup_benchmark runCertCheck n => n * n * n * n
  with prep := prepCertInput
  where {
    paramFloor := 2
    paramCeiling := 20
    paramSchedule := .custom stageSchedule
    maxSecondsPerCall := 8.0
    targetInnerNanos := 1000000000
    slopeTolerance := 0.50
  }

/- Cost model: the basis sweep computes up to `n` vector orders; each order
uses up to `n` dense matrix-vector products of quadratic cost, while polynomial
gcd/lcm work is lower order here, giving the conservative quartic bound. -/
setup_benchmark runRandomDense n => n * n * n * n
  where {
    paramFloor := 2
    paramCeiling := 12
    paramSchedule := .custom randomSchedule
    maxSecondsPerCall := 8.0
    targetInnerNanos := 1000000000
    slopeTolerance := 0.50
  }

/- Cost model: the basis sweep computes up to `n` vector orders; each order
uses up to `n` dense matrix-vector products of quadratic cost, so the declared
worst-case complexity is quartic in the dimension. -/
setup_benchmark runModular n => n * n * n * n
  where {
    paramFloor := 2
    paramCeiling := 32
    paramSchedule := .custom modularSchedule
    maxSecondsPerCall := 8.0
    targetInnerNanos := 1000000000
    slopeTolerance := 0.60
  }

/- Cost model: even though repeated blocks can shorten individual Krylov
sequences, the generic algorithm sweeps `n` basis vectors with at most `n`
quadratic matrix-vector steps each, hence a quartic worst-case bound. -/
setup_benchmark runDerogatory n => n * n * n * n
  where {
    paramFloor := 2
    paramCeiling := 20
    paramSchedule := .custom derogatorySchedule
    maxSecondsPerCall := 8.0
    targetInnerNanos := 1000000000
    slopeTolerance := 0.55
  }

/- Cost model: companion structure is not exploited by the dense algorithm;
the `n` vector orders can each take `n` quadratic matrix-vector steps, which
derives the conservative quartic model. -/
setup_benchmark runCompanion n => n * n * n * n
  where {
    paramFloor := 2
    paramCeiling := 12
    paramSchedule := .custom companionSchedule
    maxSecondsPerCall := 8.0
    targetInnerNanos := 1000000000
    slopeTolerance := 0.45
  }

private def rowsJson (n : Nat) : Lean.Json :=
  Lean.Json.arr (Array.ofFn fun i : Fin n =>
    Hex.BenchOracle.Flint.intsToJson
      (List.ofFn fun j : Fin n => signedEntry n i.val j.val 1))

private def runHexAt (n : Nat) (_ : Unit) : IO (List Int) :=
  return (Matrix.minPoly (randomRatMatrix n 1)).toArray.toList.map (fun q => q.num)

private def runFlintAt (n : Nat) (_ : Unit) : IO (List Int) := do
  let result ← Hex.BenchOracle.Flint.runOp "fmpz_mat" "minpoly"
    #[("rows", rowsJson n)]
  Hex.BenchOracle.Flint.jsonToInts result

private def runPariAt (n : Nat) (_ : Unit) : IO (List Int) := do
  let result ← Hex.BenchOracle.Pari.runOp "fmpz_mat" "minpoly"
    #[("rows", rowsJson n)]
  Hex.BenchOracle.Flint.jsonToInts result

def runHex6 : Unit → IO (List Int) := runHexAt 6
def runFlint6 : Unit → IO (List Int) := runFlintAt 6
def runPari6 : Unit → IO (List Int) := runPariAt 6
def runHex10 : Unit → IO (List Int) := runHexAt 10
def runFlint10 : Unit → IO (List Int) := runFlintAt 10
def runPari10 : Unit → IO (List Int) := runPariAt 10
def runHex12 : Unit → IO (List Int) := runHexAt 12
def runFlint12 : Unit → IO (List Int) := runFlintAt 12
def runPari12 : Unit → IO (List Int) := runPariAt 12

private def hexComparisonConfig : LeanBench.FixedBenchmarkConfig where
  repeats := 5
  maxSecondsPerCall := 8.0

private def externalComparisonConfig : LeanBench.FixedBenchmarkConfig where
  repeats := 5
  maxSecondsPerCall := 8.0
  warmupFirstIter := true

setup_fixed_benchmark runHex6 where hexComparisonConfig
setup_fixed_benchmark runFlint6 where externalComparisonConfig
setup_fixed_benchmark runPari6 where externalComparisonConfig
setup_fixed_benchmark runHex10 where hexComparisonConfig
setup_fixed_benchmark runFlint10 where externalComparisonConfig
setup_fixed_benchmark runPari10 where externalComparisonConfig
setup_fixed_benchmark runHex12 where hexComparisonConfig
setup_fixed_benchmark runFlint12 where externalComparisonConfig
setup_fixed_benchmark runPari12 where externalComparisonConfig

end Hex.MinPolyBench

def main (args : List String) : IO UInt32 :=
  match args with
  | ["metrics"] => Hex.MinPolyBench.metricsReport
  | _ => LeanBench.Cli.dispatch args
