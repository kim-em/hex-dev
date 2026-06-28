import HexPolyZ
import LeanBench

/-!
Benchmark registrations for `hex-poly-z`.

This Phase 4 infrastructure slice measures the integer-polynomial operations
owned by `HexPolyZ`: finite-prefix congruence checks, Bezout witness checking,
content and primitive-part wrappers, and the executable Mignotte-bound helpers.

Scientific registrations:

* `runCongrPrefix`: finite-prefix coefficient congruence checking, `O(n)`.
* `runCoprimeModPWitness`: finite-prefix Bezout witness checking, `O(n^2)`.
* `runContent`: integer coefficient content, `O(n)`.
* `runPrimitivePartChecksum`: integer primitive part, `O(n)`.
* `runBinom`: central-binomial multiplicative formula, `O(n^2)` under
  compiled `Nat` arithmetic. The timed loop performs `O(n)` arithmetic steps
  over an accumulator whose bit width grows linearly in `n`.
* `runFloorSqrtChecksum`: batched floor-square-root computation, `O(n log n)`.
* `runCeilSqrtChecksum`: batched ceiling-square-root computation, `O(n log n)`.
* `runCoeffNormSq`: squared coefficient-vector norm, `O(n)`.
* `runCoeffL2NormBound`: conservative coefficient-vector norm bound, `O(n)`.
* `runMignotteCoeffBound`: executable Mignotte coefficient bound over a
  logarithmically growing factor-degree fixture, `O(n)`. The ambient
  coefficient-norm scan dominates the smaller binomial subproblem.
-/

namespace Hex.PolyZBench

instance : Hashable ZPoly where
  hash p := hash p.toArray

/-- Prepared input for finite-prefix congruence checks. -/
structure CongrInput where
  lhs : ZPoly
  rhs : ZPoly
  modulus : Nat
  width : Nat
  deriving Hashable

/-- Prepared input for finite-prefix Bezout witness checks. -/
structure BezoutInput where
  f : ZPoly
  g : ZPoly
  s : ZPoly
  t : ZPoly
  modulus : Nat
  width : Nat
  deriving Hashable

/-- Prepared input for content and primitive-part benchmarks. -/
structure ContentInput where
  poly : ZPoly
  deriving Hashable

/-- Prepared integer polynomial for Mignotte helper benchmarks. -/
structure MignotteInput where
  poly : ZPoly
  factorDegree : Nat
  coeffIndex : Nat
  deriving Hashable

/-- Prepared batch of natural-number square-root inputs. -/
structure SqrtInput where
  values : Array Nat
  deriving Hashable

/-- Deterministic nonzero-ish coefficient generator keyed by size, index, and salt. -/
def coeffValue (n i salt : Nat) : Int :=
  let raw := ((i + 5) * (salt + 31) + (i + 1) * (i + 7) * 17 + n * 43) % 2003
  let value := Int.ofNat (raw + 1)
  if (i + salt) % 2 = 0 then value else -value

/-- Deterministic dense integer polynomial with `n` generated coefficients. -/
def denseZPoly (n salt : Nat) : ZPoly :=
  DensePoly.ofCoeffs <| (Array.range n).map fun i => coeffValue n i salt

/-- Deterministic integer polynomial whose coefficient content is nontrivial. -/
def contentPoly (n salt : Nat) : ZPoly :=
  let common : Int := Int.ofNat ((salt % 7) + 2)
  DensePoly.ofCoeffs <|
    (Array.range n).map fun i =>
      let base := if i = 0 then (1 : Int) else coeffValue n i salt
      common * base

/-- Stable bounded observable for integer-polynomial benchmark results. -/
def checksum (p : ZPoly) : UInt64 :=
  p.toArray.foldl (fun acc coeff => mixHash acc (hash coeff)) 0

/-- Stable bounded observable for natural-number benchmark results. -/
def checksumNat (acc : UInt64) (n : Nat) : UInt64 :=
  mixHash acc (hash n)

/-- Executable coefficient congruence modulo `m`. -/
def coeffCongrMod (m : Nat) (a b : Int) : Bool :=
  ((a - b) % (m : Int)) == 0

/-- Executable finite-prefix version of `ZPoly.congr`. -/
def congrPrefix (f g : ZPoly) (m width : Nat) : Bool :=
  (List.range width).foldl
    (fun ok i =>
      let hit := coeffCongrMod m (f.coeff i) (g.coeff i)
      hit && ok)
    true

/-- Per-parameter fixture for finite-prefix congruence checks. -/
def prepCongrInput (n : Nat) : CongrInput :=
  let modulus := 101
  let lhs := denseZPoly n 11
  let rhs :=
    DensePoly.ofCoeffs <|
      (Array.range n).map fun i =>
        lhs.coeff i + (Int.ofNat (((i + 1) % 5) + 1) * Int.ofNat modulus)
  { lhs := lhs
    rhs := rhs
    modulus := modulus
    width := n }

/-- Per-parameter fixture for finite-prefix Bezout witness checks.

The identity `s * f + t * g = 1` holds by construction, while `s * f`
still exercises a nontrivial dense product in the checked combination.
-/
def prepBezoutInput (n : Nat) : BezoutInput :=
  let f := denseZPoly n 23
  let s := denseZPoly n 47
  let t := (1 : ZPoly)
  let g := (1 : ZPoly) - s * f
  { f := f
    g := g
    s := s
    t := t
    modulus := 101
    width := 2 * n + 1 }

/-- Per-parameter fixture for content and primitive-part benchmarks. -/
def prepContentInput (n : Nat) : ContentInput :=
  { poly := contentPoly n 71 }

/-- Per-parameter fixture for Mignotte helper benchmarks. -/
def prepMignotteInput (n : Nat) : MignotteInput :=
  { poly := denseZPoly n 89
    factorDegree := n
    coeffIndex := n / 2 }

/-- Per-parameter fixture for the full Mignotte-bound benchmark.

The polynomial has `n` coefficients, so `mignotteCoeffBound` still performs the
linear ambient norm scan. The factor degree grows as `log n`, keeping the
binomial subproblem scaling but below the scan cost. The central-binomial
stress case at full degree has its own registration above.
-/
def prepMignotteBoundInput (n : Nat) : MignotteInput :=
  let factorDegree := Nat.log2 (n + 1)
  { poly := denseZPoly n 89
    factorDegree := factorDegree
    coeffIndex := factorDegree / 2 }

/-- Per-parameter batch of square-root inputs with values of size `O(n^2)`. -/
def prepSqrtInput (n : Nat) : SqrtInput :=
  { values := (Array.range n).map fun i =>
      let x := i + n + 17
      x * x + 3 * x + 5 }

/-- Benchmark target: finite-prefix coefficient congruence checking. -/
def runCongrPrefix (input : CongrInput) : Bool :=
  congrPrefix input.lhs input.rhs input.modulus input.width

/-- Benchmark target: finite-prefix Bezout witness checking. -/
def runCoprimeModPWitness (input : BezoutInput) : Bool :=
  let combo := input.s * input.f + input.t * input.g
  congrPrefix combo 1 input.modulus input.width

/-- Benchmark target: compute integer coefficient content. -/
def runContent (input : ContentInput) : Int :=
  ZPoly.content input.poly

/-- Benchmark target: compute integer primitive part and checksum the result. -/
def runPrimitivePartChecksum (input : ContentInput) : UInt64 :=
  checksum (ZPoly.primitivePart input.poly)

/-- Benchmark target: compute a central binomial coefficient. -/
def runBinom (n : Nat) : Nat :=
  ZPoly.binom (2 * n) n

/-- Benchmark target: compute floor square roots over a prepared batch. -/
def runFloorSqrtChecksum (input : SqrtInput) : UInt64 :=
  input.values.foldl (fun acc n => checksumNat acc (ZPoly.floorSqrt n)) 0

/-- Benchmark target: compute ceiling square roots over a prepared batch. -/
def runCeilSqrtChecksum (input : SqrtInput) : UInt64 :=
  input.values.foldl (fun acc n => checksumNat acc (ZPoly.ceilSqrt n)) 0

/-- Benchmark target: compute squared coefficient-vector norm. -/
def runCoeffNormSq (input : MignotteInput) : Nat :=
  ZPoly.coeffNormSq input.poly

/-- Benchmark target: compute conservative coefficient-vector norm bound. -/
def runCoeffL2NormBound (input : MignotteInput) : Nat :=
  ZPoly.coeffL2NormBound input.poly

/-- Benchmark target: compute the executable Mignotte coefficient bound. -/
def runMignotteCoeffBound (input : MignotteInput) : Nat :=
  ZPoly.mignotteCoeffBound input.poly input.factorDegree input.coeffIndex

setup_benchmark runCongrPrefix n => n
  with prep := prepCongrInput
  where {
    paramFloor := 8192
    paramCeiling := 131072
    paramSchedule := .custom #[8192, 16384, 32768, 65536, 131072]
    maxSecondsPerCall := 2.0
    targetInnerNanos := 200000000
    signalFloorMultiplier := 1.0
  }

setup_benchmark runCoprimeModPWitness n => n * n
  with prep := prepBezoutInput
  where {
    paramFloor := 128
    paramCeiling := 512
    paramSchedule := .custom #[128, 192, 256, 384, 512]
    maxSecondsPerCall := 3.0
    targetInnerNanos := 200000000
    signalFloorMultiplier := 1.0
  }

setup_benchmark runContent n => n
  with prep := prepContentInput
  where {
    paramFloor := 8192
    paramCeiling := 131072
    paramSchedule := .custom #[8192, 16384, 32768, 65536, 131072]
    maxSecondsPerCall := 2.0
    targetInnerNanos := 200000000
    signalFloorMultiplier := 1.0
  }

setup_benchmark runPrimitivePartChecksum n => n
  with prep := prepContentInput
  where {
    paramFloor := 8192
    paramCeiling := 131072
    paramSchedule := .custom #[8192, 16384, 32768, 65536, 131072]
    maxSecondsPerCall := 2.0
    targetInnerNanos := 200000000
    signalFloorMultiplier := 1.0
  }

/-
`ZPoly.binom (2*n) n` folds across `min n n = n` multiplicative terms.
For this central-binomial fixture the accumulator reaches linear bit width.
Each compiled `Nat` multiply/divide step therefore scales with the accumulator
limb count, so the scientific declaration models bit-cost growth rather than
only counting loop iterations.
-/
setup_benchmark runBinom n => n * n
  where {
    paramFloor := 16384
    paramCeiling := 131072
    paramSchedule := .custom #[16384, 32768, 65536, 131072]
    maxSecondsPerCall := 10.0
    targetInnerNanos := 300000000
    signalFloorMultiplier := 1.0
  }

setup_benchmark runFloorSqrtChecksum n => n * Nat.log2 (n + 1)
  with prep := prepSqrtInput
  where {
    paramFloor := 1024
    paramCeiling := 16384
    paramSchedule := .custom #[1024, 2048, 4096, 8192, 16384]
    maxSecondsPerCall := 3.0
    targetInnerNanos := 200000000
    signalFloorMultiplier := 1.0
  }

setup_benchmark runCeilSqrtChecksum n => n * Nat.log2 (n + 1)
  with prep := prepSqrtInput
  where {
    paramFloor := 1024
    paramCeiling := 16384
    paramSchedule := .custom #[1024, 2048, 4096, 8192, 16384]
    maxSecondsPerCall := 3.0
    targetInnerNanos := 200000000
    signalFloorMultiplier := 1.0
  }

setup_benchmark runCoeffNormSq n => n
  with prep := prepMignotteInput
  where {
    paramFloor := 8192
    paramCeiling := 131072
    paramSchedule := .custom #[8192, 16384, 32768, 65536, 131072]
    maxSecondsPerCall := 2.0
    targetInnerNanos := 200000000
    signalFloorMultiplier := 1.0
  }

setup_benchmark runCoeffL2NormBound n => n
  with prep := prepMignotteInput
  where {
    paramFloor := 8192
    paramCeiling := 131072
    paramSchedule := .custom #[8192, 16384, 32768, 65536, 131072]
    maxSecondsPerCall := 2.0
    targetInnerNanos := 200000000
    signalFloorMultiplier := 1.0
  }

/-
`mignotteCoeffBound` computes `binom k j * coeffL2NormBound f`. Here
`f` has `n` coefficients and `k = log2 (n + 1)`, so the norm scan is linear
while the binomial part is sublinear relative to the fixture size.
-/
setup_benchmark runMignotteCoeffBound n => n
  with prep := prepMignotteBoundInput
  where {
    paramFloor := 8192
    paramCeiling := 131072
    paramSchedule := .custom #[8192, 16384, 32768, 65536, 131072]
    maxSecondsPerCall := 2.0
    targetInnerNanos := 200000000
    signalFloorMultiplier := 1.0
  }

end Hex.PolyZBench

def main (args : List String) : IO UInt32 :=
  LeanBench.Cli.dispatch args
