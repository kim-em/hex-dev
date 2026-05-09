import HexHensel.Multifactor
import HexHensel.Quadratic
import HexHensel.QuadraticMultifactor
import LeanBench

/-!
Benchmark registrations for `hex-hensel`.

This Phase 4 infrastructure slice measures the executable bridge operations,
linear and quadratic Hensel lift steps, and the ordered multifactor helpers.
Inputs are deterministic and use the fixed small prime `5`; timed targets
return compact checksums of the computed polynomial data.

Scientific registrations:

* `runModPChecksum`: coefficient reduction from `Z[x]` to `F_5[x]`, `O(n)`.
* `runLiftToZChecksum`: canonical lift from `F_5[x]` to `Z[x]`, `O(n)`.
* `runReduceModPowChecksum`: coefficient reduction modulo `5^k`, `O(n)`.
* `runLinearHenselStepChecksum`: one linear Hensel correction, `O(n^2)`.
* `runHenselLiftChecksum`: iterative linear lift over `(n, k)`, `O(n^2 k)`.
* `runQuadraticHenselStepChecksum`: one quadratic Hensel correction, `O(n^2)`.
* `runPolyProductChecksum`: ordered product of `n` linear factors, `O(n^2)`.
* `runMultifactorLiftChecksum`: two-factor ordered lift over `(n, k)`,
  `O(n^2 k)`.
* `runMultifactorLiftQuadraticChecksum`: production quadratic multifactor lift,
  `O(n^2 log k)`.

Compare groups:

* `compare runMultifactorLiftChecksum runMultifactorLiftQuadraticChecksum`
  checks the linear and quadratic multifactor lifters on the shared encoded
  `(n, k)` fixture schedule.
-/

namespace Hex
namespace HenselBench

private instance benchBoundsFive : ZMod64.Bounds 5 := ⟨by decide, by decide⟩

instance : Hashable ZPoly where
  hash p := hash p.toArray

instance {p : Nat} [ZMod64.Bounds p] : Hashable (ZMod64 p) where
  hash a := hash a.toNat

instance {p : Nat} [ZMod64.Bounds p] : Hashable (FpPoly p) where
  hash f := hash f.toArray

/-- Prepared input for bridge benchmarks. -/
structure BridgeInput where
  zpoly : ZPoly
  fpoly : FpPoly 5
  deriving Hashable

/-- Prepared input for one linear Hensel step and the iterative wrapper. -/
structure LinearInput where
  k : Nat := 3
  f : ZPoly
  g : ZPoly
  h : ZPoly
  s : FpPoly 5
  t : FpPoly 5
  deriving Hashable

/-- Prepared input for one quadratic Hensel step. -/
structure QuadraticInput where
  f : ZPoly
  g : ZPoly
  h : ZPoly
  s : ZPoly
  t : ZPoly
  deriving Hashable

/-- Prepared input for ordered multifactor helpers. -/
structure MultifactorInput where
  k : Nat := 3
  f : ZPoly
  factors : Array ZPoly
  deriving Hashable

/-- Encoding scale for benchmark parameters that vary both degree `n` and precision `k`. -/
def liftParamScale : Nat :=
  1000

/-- Encode a degree/precision pair as the single `Nat` parameter accepted by lean-bench. -/
def encodeLiftParam (n k : Nat) : Nat :=
  n * liftParamScale + k

/-- Decode the degree component from an encoded lift benchmark parameter. -/
def liftBenchDegree (param : Nat) : Nat :=
  param / liftParamScale

/-- Decode the requested precision component from an encoded lift benchmark parameter. -/
def liftBenchPrecision (param : Nat) : Nat :=
  param % liftParamScale

/-- Textbook cost model for linear lifting over encoded `(n, k)` parameters. -/
def liftLinearComplexity (param : Nat) : Nat :=
  let n := liftBenchDegree param
  let k := liftBenchPrecision param
  n * n * k

/-- Textbook cost model for quadratic lifting over encoded `(n, k)` parameters. -/
def liftQuadraticComplexity (param : Nat) : Nat :=
  let n := liftBenchDegree param
  let k := liftBenchPrecision param
  n * n * Nat.log2 (k + 1)

/-- Deterministic integer coefficient generator keyed by size, index, and salt. -/
def zCoeffValue (n i salt : Nat) : Int :=
  let raw := ((i + 3) * (salt + 19) + (i + 1) * (i + 5) * 11 + n * 37) % 997
  let value := Int.ofNat (raw + 1)
  if (i + salt) % 2 = 0 then value else -value

/-- Deterministic `F_5` coefficient generator keyed by size, index, and salt. -/
def fpCoeffValue (n i salt : Nat) : ZMod64 5 :=
  ZMod64.ofNat 5 <|
    ((i + 1) * (salt + 7) + (i + 5) * (i + 9) * 3 + n * 13) % 5

/-- Deterministic dense integer polynomial with `n` generated coefficients. -/
def denseZPoly (n salt : Nat) : ZPoly :=
  DensePoly.ofCoeffs <| (Array.range n).map fun i => zCoeffValue n i salt

/-- Deterministic dense `F_5` polynomial with `n` generated coefficients. -/
def denseFpPoly (n salt : Nat) : FpPoly 5 :=
  FpPoly.ofCoeffs <| (Array.range n).map fun i => fpCoeffValue n i salt

/-- Deterministic monic integer linear factor. -/
def linearZFactor (salt : Nat) : ZPoly :=
  DensePoly.ofCoeffs #[Int.ofNat ((salt % 4) + 1), 1]

/-- Deterministic monic `F_5` linear factor. -/
def linearFpFactor (salt : Nat) : FpPoly 5 :=
  FpPoly.ofCoeffs #[fpCoeffValue 1 0 salt, 1]

/-- Stable checksum for integer-polynomial benchmark results. -/
def checksumZPoly (f : ZPoly) : UInt64 :=
  f.toArray.foldl (fun acc coeff => mixHash acc (hash coeff)) 0

/-- Stable checksum for finite-field-polynomial benchmark results. -/
def checksumFpPoly {p : Nat} [ZMod64.Bounds p] (f : FpPoly p) : UInt64 :=
  f.toArray.foldl (fun acc coeff => mixHash acc (hash coeff)) 0

/-- Stable checksum for an ordered array of integer polynomials. -/
def checksumZPolyArray (polys : Array ZPoly) : UInt64 :=
  polys.foldl (fun acc f => mixHash acc (checksumZPoly f)) 0

/-- Per-parameter fixture for bridge operations. -/
def prepBridgeInput (n : Nat) : BridgeInput :=
  { zpoly := denseZPoly n 17
    fpoly := denseFpPoly n 23 }

/-- Per-parameter fixture for linear Hensel operations.

The factor error is built as a multiple of `5`, so the correction path is
nontrivial while staying deterministic. The Bezout pair is computed via
`normalizedXGCD` so that `s * gMod + t * hMod ≡ 1 (mod 5)`; the iterative
linear lift relies on this precondition to keep the corrected `h` factor
bounded in degree across all `k` steps. The shared salts `59 / 62 / 67`
match `prepMultifactorLiftInput`, which already verifies coprimeness on
the full scientific `n` ladder including `n = 192`.
-/
def prepLinearInput (n : Nat) : LinearInput :=
  let g := linearZFactor 59
  let h := denseZPoly (n + 1) 62
  let e := denseZPoly (n + 1) 67
  let f := g * h + DensePoly.scale (5 : Int) e
  let xgcd := ZPoly.normalizedXGCD 5 g h
  { f := f
    g := g
    h := h
    s := xgcd.left
    t := xgcd.right }

/-- Encoded `(n, k)` fixture for iterative linear Hensel lift benchmarks. -/
def prepLinearLiftInput (param : Nat) : LinearInput :=
  { prepLinearInput (liftBenchDegree param) with
    k := liftBenchPrecision param }

/-- Per-parameter fixture for quadratic Hensel operations. -/
def prepQuadraticInput (n : Nat) : QuadraticInput :=
  let g := linearZFactor 43
  let h := denseZPoly (n + 1) 47
  let e := denseZPoly (n + 1) 53
  let f := g * h + DensePoly.scale (5 : Int) e
  { f := f
    g := g
    h := h
    s := 0
    t := 1 }

/-- Per-parameter fixture for the ordered product of many small factors. -/
def prepProductInput (n : Nat) : MultifactorInput :=
  let factors := (Array.range n).map linearZFactor
  { f := Array.polyProduct factors
    factors := factors }

/-- Per-parameter fixture for the two-factor multifactor lifting path. -/
def prepMultifactorLiftInput (n : Nat) : MultifactorInput :=
  let g := linearZFactor 59
  -- Salt 62 keeps `h` coprime to `g` modulo 5 across the scientific ladder.
  let h := denseZPoly (n + 1) 62
  let factors := #[g, h]
  let e := denseZPoly (n + 1) 67
  { f := Array.polyProduct factors + DensePoly.scale (5 : Int) e
    factors := factors }

/-- Encoded `(n, k)` fixture for iterative multifactor lift benchmarks. -/
def prepMultifactorLiftPrecisionInput (param : Nat) : MultifactorInput :=
  { prepMultifactorLiftInput (liftBenchDegree param) with
    k := liftBenchPrecision param }

/-- Benchmark target: reduce integer coefficients modulo `5`. -/
def runModPChecksum (input : BridgeInput) : UInt64 :=
  checksumFpPoly <| ZPoly.modP 5 input.zpoly

/-- Benchmark target: lift `F_5` coefficients to canonical integer representatives. -/
def runLiftToZChecksum (input : BridgeInput) : UInt64 :=
  checksumZPoly <| FpPoly.liftToZ input.fpoly

/-- Benchmark target: reduce integer coefficients modulo `5^3`. -/
def runReduceModPowChecksum (input : BridgeInput) : UInt64 :=
  checksumZPoly <| ZPoly.reduceModPow input.zpoly 5 3

/-- Benchmark target: one linear Hensel correction step. -/
def runLinearHenselStepChecksum (input : LinearInput) : UInt64 :=
  let r := ZPoly.linearHenselStep 5 1 input.f input.g input.h input.s input.t
  mixHash (checksumZPoly r.g) (checksumZPoly r.h)

/-- Benchmark target: fixed-precision iterative linear Hensel lift. -/
def runHenselLiftChecksum (input : LinearInput) : UInt64 :=
  let r := ZPoly.henselLift 5 input.k input.f input.g input.h input.s input.t
  mixHash (checksumZPoly r.g) (checksumZPoly r.h)

/-- Benchmark target: one quadratic Hensel correction step. -/
def runQuadraticHenselStepChecksum (input : QuadraticInput) : UInt64 :=
  let r := ZPoly.quadraticHenselStep 5 input.f input.g input.h input.s input.t
  mixHash (mixHash (checksumZPoly r.g) (checksumZPoly r.h))
    (mixHash (checksumZPoly r.s) (checksumZPoly r.t))

/-- Benchmark target: ordered product of prepared integer-polynomial factors. -/
def runPolyProductChecksum (input : MultifactorInput) : UInt64 :=
  checksumZPoly <| Array.polyProduct input.factors

/-- Benchmark target: ordered multifactor lift of two prepared factors. -/
def runMultifactorLiftChecksum (input : MultifactorInput) : UInt64 :=
  checksumZPolyArray <| ZPoly.multifactorLift 5 input.k input.f input.factors

/-- Benchmark target: production quadratic ordered multifactor lift. -/
def runMultifactorLiftQuadraticChecksum (input : MultifactorInput) : UInt64 :=
  checksumZPolyArray <| ZPoly.multifactorLiftQuadratic 5 input.k input.f input.factors

/-
Coefficient reduction maps each of the `n` dense integer coefficients once and
then normalizes the result, so the bridge operation has linear cost.
-/
setup_benchmark runModPChecksum n => n
  with prep := prepBridgeInput
  where {
    paramFloor := 8192
    paramCeiling := 131072
    paramSchedule := .custom #[8192, 16384, 32768, 65536, 131072]
    maxSecondsPerCall := 2.0
    targetInnerNanos := 200000000
    signalFloorMultiplier := 1.0
  }

/-
Canonical lifting maps each of the `n` finite-field coefficients to its
integer representative and normalizes the dense result, giving linear cost.
-/
setup_benchmark runLiftToZChecksum n => n
  with prep := prepBridgeInput
  where {
    paramFloor := 8192
    paramCeiling := 131072
    paramSchedule := .custom #[8192, 16384, 32768, 65536, 131072]
    maxSecondsPerCall := 2.0
    targetInnerNanos := 200000000
    signalFloorMultiplier := 1.0
  }

/-
Reduction modulo a fixed power `5^3` performs one bounded integer reduction per
dense coefficient followed by normalization, so the model is linear in `n`.
-/
setup_benchmark runReduceModPowChecksum n => n
  with prep := prepBridgeInput
  where {
    paramFloor := 8192
    paramCeiling := 131072
    paramSchedule := .custom #[8192, 16384, 32768, 65536, 131072]
    maxSecondsPerCall := 2.0
    targetInnerNanos := 200000000
    signalFloorMultiplier := 1.0
  }

/-
The linear step performs dense arithmetic against degree-`n` inputs, including
a correction product whose operands both grow linearly with the fixture size.
-/
setup_benchmark runLinearHenselStepChecksum n => n * n
  with prep := prepLinearInput
  where {
    paramFloor := 64
    paramCeiling := 512
    paramSchedule := .custom #[64, 96, 128, 192, 256, 384, 512]
    maxSecondsPerCall := 4.0
    targetInnerNanos := 200000000
    signalFloorMultiplier := 1.0
  }

/-
The wrapper performs `k` linear correction steps over degree-`n` dense inputs;
the single lean-bench parameter encodes `(n, k)` as `n * 1000 + k`, including
Mignotte-sized precisions such as `42` on the scientific schedule.
-/
setup_benchmark runHenselLiftChecksum param => liftLinearComplexity param
  with prep := prepLinearLiftInput
  where {
    paramFloor := encodeLiftParam 32 4
    paramCeiling := encodeLiftParam 192 64
    paramSchedule := .custom #[
      encodeLiftParam 32 4,
      encodeLiftParam 32 16,
      encodeLiftParam 32 42,
      encodeLiftParam 64 16,
      encodeLiftParam 64 42,
      encodeLiftParam 96 42,
      encodeLiftParam 128 64,
      encodeLiftParam 192 64]
    maxSecondsPerCall := 6.0
    targetInnerNanos := 200000000
    signalFloorMultiplier := 1.0
  }

/-
The quadratic step performs dense factor and Bezout correction products over
degree-`n` fixtures while the requested modulus size is fixed.
-/
setup_benchmark runQuadraticHenselStepChecksum n => n * n
  with prep := prepQuadraticInput
  where {
    paramFloor := 64
    paramCeiling := 512
    paramSchedule := .custom #[64, 96, 128, 192, 256, 384, 512]
    maxSecondsPerCall := 6.0
    targetInnerNanos := 200000000
    signalFloorMultiplier := 1.0
  }

/-
Left-folding `n` linear factors grows the accumulator degree one step at a
time, giving a quadratic total number of coefficient operations.
-/
setup_benchmark runPolyProductChecksum n => n * n
  with prep := prepProductInput
  where {
    paramFloor := 128
    paramCeiling := 1024
    paramSchedule := .custom #[128, 192, 256, 384, 512, 768, 1024]
    maxSecondsPerCall := 4.0
    targetInnerNanos := 200000000
    signalFloorMultiplier := 1.0
  }

/-
This two-factor fixture exercises the public ordered lift helper over encoded
`(n, k)` parameters; the linear delegated Hensel lift repeats a quadratic
dense-polynomial correction `k` times.
-/
setup_benchmark runMultifactorLiftChecksum param => liftLinearComplexity param
  with prep := prepMultifactorLiftPrecisionInput
  where {
    paramFloor := encodeLiftParam 32 4
    paramCeiling := encodeLiftParam 192 64
    paramSchedule := .custom #[
      encodeLiftParam 32 4,
      encodeLiftParam 32 16,
      encodeLiftParam 32 42,
      encodeLiftParam 64 16,
      encodeLiftParam 64 42,
      encodeLiftParam 96 42,
      encodeLiftParam 128 64,
      encodeLiftParam 192 64]
    maxSecondsPerCall := 6.0
    targetInnerNanos := 200000000
    signalFloorMultiplier := 1.0
  }

/-
The production path shares the encoded `(n, k)` fixture with the linear lifter,
but its binary lift uses only `ceil(log₂ k)` quadratic-doubling steps; the
factor/Bezout correction products dominate each step.
-/
setup_benchmark runMultifactorLiftQuadraticChecksum param => liftQuadraticComplexity param
  with prep := prepMultifactorLiftPrecisionInput
  where {
    paramFloor := encodeLiftParam 32 4
    paramCeiling := encodeLiftParam 192 64
    paramSchedule := .custom #[
      encodeLiftParam 32 4,
      encodeLiftParam 32 16,
      encodeLiftParam 32 42,
      encodeLiftParam 64 16,
      encodeLiftParam 64 42,
      encodeLiftParam 96 42,
      encodeLiftParam 128 64,
      encodeLiftParam 192 64]
    maxSecondsPerCall := 6.0
    targetInnerNanos := 200000000
    signalFloorMultiplier := 1.0
  }

end HenselBench
end Hex

def main (args : List String) : IO UInt32 :=
  LeanBench.Cli.dispatch args
