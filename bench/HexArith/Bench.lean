import HexArith
import LeanBench

/-!
Benchmark registrations for `hex-arith`.

This Phase 4 slice compares two implementations of the same repeated modular
multiplication task over the shared small odd modulus `65537`: Barrett reduction
for one-off modular products, and Montgomery arithmetic with factors converted
to Montgomery form in the prepared input. It also registers public modular
exponentiation over the same odd word-sized modulus, parameterized by exponent
bit length.

It also registers the `Nat`, GMP-backed `Int`, and `UInt64` extended-GCD API
surface on a shared nonnegative input family. The `run*ExtGcdShapes`
registrations return a compact summary of normalized `(g, s*a + t*b)`
observations rather than raw Bezout coefficients, because valid extended-GCD
implementations may choose different coefficients while still proving the same
gcd certificate.

Scientific benchmark registrations:

* `runBarrettMulChain`: repeated modular multiplication with `BarrettCtx.mulMod`,
  `O(n)`.
* `runMontgomeryMulChain`: the same multiplication chain using
  `MontCtx.toMont`, `MontCtx.mulMont`, and `MontCtx.fromMont`, `O(n)`.
* `runPowMod`: `HexArith.powMod` over a fixed odd word-sized modulus with an
  `n`-bit deterministic exponent, `O(n)`.
* `runNatExtGcdShapes`: `HexArith.extGcd` over `Nat`, batched over `n`
  bounded-word samples, `O(n)`.
* `runIntExtGcdShapes`: `HexArith.Int.extGcd` over nonnegative `Int`, batched
  over the same samples, `O(n)`.
* `runUInt64ExtGcdShapes`: `HexArith.UInt64.extGcd`, batched over the same
  samples, `O(n)`.

Compare groups:

* `compare runNatExtGcdShapes runIntExtGcdShapes runUInt64ExtGcdShapes` checks
  agreement on the normalized gcd/Bezout output shape over the shared prepared
  nonnegative bounded-word input domain.
-/

namespace Hex.ArithBench

/-- Shared small odd modulus in the overlap between Barrett and Montgomery. -/
def benchModulus : UInt64 :=
  65_537

/-- Barrett context for the shared benchmark modulus. -/
def barrettCtx : BarrettCtx benchModulus :=
  BarrettCtx.mk benchModulus (by decide) (by decide)

/-- Montgomery context for the shared benchmark modulus. -/
def montCtx : MontCtx benchModulus :=
  MontCtx.mk benchModulus (by decide)

/-- Prepared inputs for repeated modular multiplication. -/
structure MulChainInput where
  factors : Array UInt64
  montFactors : Array UInt64
  deriving Repr, BEq, Hashable

/-- Prepared input for public modular-exponentiation benchmarks. -/
structure PowModInput where
  base : Nat
  exponent : Nat
  modulus : Nat
  deriving Repr, BEq, Hashable

/-- One nonnegative shared input pair for extended-GCD benchmarks. -/
structure ExtGcdSample where
  a : Nat
  b : Nat
  deriving Repr, BEq, Hashable

/-- Prepared batched input for extended-GCD benchmarks. -/
structure ExtGcdInput where
  samples : Array ExtGcdSample
  deriving Repr, BEq, Hashable

/-- Compact normalized extended-GCD observable used for compare. -/
structure ExtGcdShape where
  count : Nat
  gcdSum : Nat
  bezoutSum : Int
  gcdMix : UInt64
  bezoutMix : UInt64
  deriving Repr, BEq, Hashable

/-- Deterministic residue generator, always returning `0 < x < benchModulus`. -/
def factorAt (i : Nat) : UInt64 :=
  let x :=
    ((i + 1) * 1_103_515_245 +
      (i + 17) * 12_345 +
      0x9E37) % 65_536
  UInt64.ofNat (x + 1)

/-- Deterministic input family shared by both benchmark registrations. -/
def prepMulChainInput (n : Nat) : MulChainInput :=
  let factors := (Array.range n).map factorAt
  { factors := factors
    montFactors := factors.map montCtx.toMont }

/--
Deterministic public-API exponentiation input. The parameter is the requested
exponent bit length, so repeated squaring has the textbook linear model in `n`.
-/
def prepPowModInput (n : Nat) : PowModInput :=
  { base := 0x1234_5678_9ABC_DEF0
    exponent := 2 ^ n - 1
    modulus := benchModulus.toNat }

/--
Deterministic nonnegative sample generator. Values stay below `2^32`, keeping
the `UInt64` and arbitrary-precision paths on the same bounded-word domain.
-/
def extGcdSampleAt (i : Nat) : ExtGcdSample :=
  let a := ((i + 1) * 1_103_515_245 + (i + 17) * 12_345 + 0x9E37) % 4_294_967_291
  let b := ((i + 3) * 1_664_525 + (i + 29) * 1_013_904_223 + 0x7F4A) % 4_294_967_291
  { a := a + 1, b := b + 1 }

/-- Deterministic input family shared by all extended-GCD registrations. -/
def prepExtGcdInput (n : Nat) : ExtGcdInput :=
  { samples := (Array.range n).map extGcdSampleAt }

/-- Constant hot-loop multiplier for extended-GCD benchmark signal. -/
def extGcdInnerRepeats : Nat :=
  64

/-- Empty normalized extended-GCD summary. -/
def emptyExtGcdShape : ExtGcdShape :=
  { count := 0
    gcdSum := 0
    bezoutSum := 0
    gcdMix := 0
    bezoutMix := 0 }

/-- Deterministic wrapping mix for compact benchmark result summaries. -/
def mixNat (acc : UInt64) (x : Nat) : UInt64 :=
  acc * 0x9E3779B97F4A7C15 + UInt64.ofNat x + 0xBF58476D1CE4E5B9

/-- Add one normalized extended-GCD result to a compact summary. -/
def addExtGcdShape (acc : ExtGcdShape) (g : Nat) (bezoutValue : Int) :
    ExtGcdShape :=
  { count := acc.count + 1
    gcdSum := acc.gcdSum + g
    bezoutSum := acc.bezoutSum + bezoutValue
    gcdMix := mixNat acc.gcdMix g
    bezoutMix := mixNat acc.bezoutMix bezoutValue.natAbs }

/-- Run the chain directly in standard representation with Barrett reduction. -/
def runBarrettMulChain (input : MulChainInput) : UInt64 :=
  input.factors.foldl (fun acc x => barrettCtx.mulMod acc x) 1

/--
Run the same chain through Montgomery representation. Factor conversion is
hoisted into `prepMulChainInput`; the timed operation is the hot multiplication
loop plus the final conversion out of Montgomery form.
-/
def runMontgomeryMulChain (input : MulChainInput) : UInt64 :=
  let acc0 := montCtx.toMont 1
  let acc := input.montFactors.foldl
    (fun acc x => montCtx.mulMont acc x)
    acc0
  montCtx.fromMont acc

/-- Benchmark target: public modular exponentiation by repeated squaring. -/
def runPowMod (input : PowModInput) : Nat :=
  HexArith.powMod input.base input.exponent input.modulus

/-- Summarize a batch of `HexArith.extGcd` results over the prepared samples. -/
def natExtGcdShapes (input : ExtGcdInput) : ExtGcdShape :=
  input.samples.foldl (init := emptyExtGcdShape) fun acc sample =>
    let (g, s, t) := HexArith.extGcd sample.a sample.b
    addExtGcdShape acc g (s * Int.ofNat sample.a + t * Int.ofNat sample.b)

/-- Summarize GMP-backed `HexArith.Int.extGcd` results on nonnegative inputs. -/
def intExtGcdShapes (input : ExtGcdInput) : ExtGcdShape :=
  input.samples.foldl (init := emptyExtGcdShape) fun acc sample =>
    let a := Int.ofNat sample.a
    let b := Int.ofNat sample.b
    let (g, s, t) := HexArith.Int.extGcd a b
    addExtGcdShape acc g (s * a + t * b)

/-- Summarize `HexArith.UInt64.extGcd` results over the prepared samples. -/
def uint64ExtGcdShapes (input : ExtGcdInput) : ExtGcdShape :=
  input.samples.foldl (init := emptyExtGcdShape) fun acc sample =>
    let a := UInt64.ofNat sample.a
    let b := UInt64.ofNat sample.b
    let (g, s, t) := HexArith.UInt64.extGcd a b
    addExtGcdShape acc g.toNat (s * Int.ofNat a.toNat + t * Int.ofNat b.toNat)

/-- Repeat a batch target by a fixed factor so scientific runs clear timer resolution. -/
def repeatExtGcdShapes (f : ExtGcdInput → ExtGcdShape)
    (input : ExtGcdInput) : ExtGcdShape :=
  let rec go (remaining : Nat) (last : ExtGcdShape) : ExtGcdShape :=
    match remaining with
    | 0 => last
    | k + 1 => go k (f input)
  go extGcdInnerRepeats emptyExtGcdShape

/-- Benchmark target: repeated `HexArith.extGcd` batch over prepared samples. -/
def runNatExtGcdShapes (input : ExtGcdInput) : ExtGcdShape :=
  repeatExtGcdShapes natExtGcdShapes input

/-- Benchmark target: repeated GMP-backed `HexArith.Int.extGcd` batch. -/
def runIntExtGcdShapes (input : ExtGcdInput) : ExtGcdShape :=
  repeatExtGcdShapes intExtGcdShapes input

/-- Benchmark target: repeated `HexArith.UInt64.extGcd` batch. -/
def runUInt64ExtGcdShapes (input : ExtGcdInput) : ExtGcdShape :=
  repeatExtGcdShapes uint64ExtGcdShapes input

setup_benchmark runBarrettMulChain n => n
  with prep := prepMulChainInput
  where {
    paramFloor := 8192
    paramCeiling := 131072
    paramSchedule := .custom #[8192, 16384, 32768, 65536, 131072]
    maxSecondsPerCall := 2.0
    targetInnerNanos := 500000000
  }

setup_benchmark runMontgomeryMulChain n => n
  with prep := prepMulChainInput
  where {
    paramFloor := 8192
    paramCeiling := 131072
    paramSchedule := .custom #[8192, 16384, 32768, 65536, 131072]
    maxSecondsPerCall := 2.0
    targetInnerNanos := 500000000
  }

setup_benchmark runPowMod n => n
  with prep := prepPowModInput
  where {
    paramFloor := 1024
    paramCeiling := 16384
    paramSchedule := .custom #[1024, 2048, 4096, 8192, 16384]
    maxSecondsPerCall := 2.0
    targetInnerNanos := 500000000
  }

setup_benchmark runNatExtGcdShapes n => n
  with prep := prepExtGcdInput
  where {
    paramFloor := 8192
    paramCeiling := 24576
    paramSchedule := .custom #[8192, 12288, 16384, 24576]
    maxSecondsPerCall := 8.0
    targetInnerNanos := 200000000
  }

setup_benchmark runIntExtGcdShapes n => n
  with prep := prepExtGcdInput
  where {
    paramFloor := 8192
    paramCeiling := 24576
    paramSchedule := .custom #[8192, 12288, 16384, 24576]
    maxSecondsPerCall := 8.0
    targetInnerNanos := 200000000
  }

setup_benchmark runUInt64ExtGcdShapes n => n
  with prep := prepExtGcdInput
  where {
    paramFloor := 8192
    paramCeiling := 24576
    paramSchedule := .custom #[8192, 12288, 16384, 24576]
    maxSecondsPerCall := 8.0
    targetInnerNanos := 200000000
  }

end Hex.ArithBench

def main (args : List String) : IO UInt32 :=
  LeanBench.Cli.dispatch args
