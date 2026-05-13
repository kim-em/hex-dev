import HexPoly
import Hex.BenchOracle.Flint
import LeanBench

/-!
Benchmark registrations for `hex-poly`.

This Phase 4 slice measures the dense core operations over deterministic
integer polynomials, with scalar-cost-sensitive operations over a fixed-size
prime field. Input construction is hoisted into `prep`, and each timed target
returns a small checksum or scalar observable rather than the full polynomial.

Scientific registrations:

* `runAddChecksum`: dense coefficientwise addition, `O(n)`.
* `runSubChecksum`: dense coefficientwise subtraction, `O(n)`.
* `runMulChecksum`: schoolbook dense multiplication, `O(n^2)`.
* `runEval`: Horner evaluation, `O(n)`.
* `runComposeChecksum`: Horner composition using schoolbook multiplication,
  `O(n^4)` for same-size dense inputs.
* `runDerivativeChecksum`: formal derivative, `O(n)`.
* `runDivModChecksum`: field-polynomial long division returning quotient and
  remainder, `O(n^2)`.
* `runDivChecksum`: quotient extraction from field-polynomial long division,
  `O(n^2)`.
* `runModChecksum`: remainder extraction from field-polynomial long division,
  `O(n^2)`.
* `runModByMonicChecksum`: remainder from division by a monic divisor,
  `O(n^2)`.
* `runGcdChecksum`: Euclidean gcd over a fixed-size field, `O(n^2)` worst
  case on the committed Fibonacci-style quotient-chain fixture.
* `runXGcdChecksum`: extended Euclidean algorithm over a fixed-size field,
  `O(n^2)` worst case on the committed Fibonacci-style quotient-chain fixture.
* `runContent`: integer coefficient content, `O(n)`.
* `runPrimitivePartChecksum`: integer primitive part, `O(n)`.
* `runPolyCRTChecksum`: polynomial CRT witness construction over coprime
  monic moduli, `O(n^2)` with the current schoolbook multiplication path.

Informational FLINT `fmpz_poly` comparator registrations:

* `runFlintAddChecksum`: paired with `runAddChecksum` on
  `dense-int-arithmetic`.
* `runFlintSubChecksum`: paired with `runSubChecksum` on
  `dense-int-arithmetic`.
* `runFlintMulChecksum`: paired with `runMulChecksum` on
  `dense-int-arithmetic`.
* `runFlintComposeChecksum`: paired with `runComposeChecksum` on
  `dense-int-arithmetic`.
* `runFlintDerivativeChecksum`: paired with `runDerivativeChecksum` on
  `dense-int-arithmetic`.
* `runFlintContent`: paired with `runContent` on `integer-content`.
* `runFlintPrimitivePartChecksum`: paired with
  `runPrimitivePartChecksum` on `integer-content`.
-/

namespace Hex.PolyBench

/-- Tiny fixed-size field used by Euclidean benchmarks to measure polynomial
operation counts without arbitrary-precision `Rat` coefficient growth. -/
structure F7 where
  val : Fin 7
  deriving DecidableEq, Hashable

namespace F7

def ofNat (n : Nat) : F7 :=
  { val := ⟨n % 7, Nat.mod_lt n (by decide)⟩ }

private def invNat : Nat → Nat
  | 1 => 1
  | 2 => 4
  | 3 => 5
  | 4 => 2
  | 5 => 3
  | 6 => 6
  | _ => 0

instance : Zero F7 where
  zero := ofNat 0

instance : One F7 where
  one := ofNat 1

instance : Add F7 where
  add a b := ofNat (a.val.val + b.val.val)

instance : Sub F7 where
  sub a b := ofNat (a.val.val + 7 - b.val.val)

instance : Mul F7 where
  mul a b := ofNat (a.val.val * b.val.val)

instance : Div F7 where
  div a b := ofNat (a.val.val * invNat b.val.val)

end F7

/-- Hash prepared dense-polynomial inputs by their normalized coefficient arrays. -/
instance [Hashable R] [Zero R] [DecidableEq R] : Hashable (DensePoly R) where
  hash p := hash p.toArray

/-- Prepared input for binary dense-polynomial operations. -/
structure BinaryInput where
  lhs : DensePoly Int
  rhs : DensePoly Int
  deriving Hashable

/-- Prepared input for unary dense-polynomial operations. -/
structure UnaryInput where
  poly : DensePoly Int
  deriving Hashable

/-- Prepared input for integer content and primitive-part operations. -/
structure ContentInput where
  poly : DensePoly Int
  deriving Hashable

/-- Prepared input for Horner evaluation. -/
structure EvalInput where
  poly : DensePoly F7
  point : F7
  deriving Hashable

/-- Prepared input for polynomial composition. -/
structure ComposeInput where
  outer : DensePoly Int
  inner : DensePoly Int
  deriving Hashable

/-- Prepared input for field-polynomial Euclidean operations. -/
structure EuclidInput where
  dividend : DensePoly F7
  divisor : DensePoly F7
  deriving Hashable

/-- Prepared input for division by a generated monic polynomial. -/
structure MonicInput where
  dividend : DensePoly F7
  divisorDegree : Nat
  deriving Hashable

/-- Prepared input for polynomial CRT witness construction. -/
structure PolyCRTInput where
  modulusA : DensePoly Rat
  modulusB : DensePoly Rat
  residueA : DensePoly Rat
  residueB : DensePoly Rat
  bezoutS : DensePoly Rat
  bezoutT : DensePoly Rat
  deriving Hashable

/-- Deterministic nonzero-ish coefficient generator keyed by size, index, and salt. -/
def coeffValue (n i salt : Nat) : Int :=
  let raw := ((i + 1) * (salt + 17) + (i + 3) * (i + 5) * 13 + n * 29) % 1009
  Int.ofNat (raw + 1)

/-- Deterministic dense polynomial with `n` generated coefficients. -/
def densePoly (n salt : Nat) : DensePoly Int :=
  DensePoly.ofCoeffs <| (Array.range n).map fun i => coeffValue n i salt

/-- Deterministic dense polynomial over `Rat` for field-operation benchmarks. -/
def denseRatPoly (n salt : Nat) : DensePoly Rat :=
  DensePoly.ofCoeffs <| (Array.range n).map fun i => (coeffValue n i salt : Rat)

/-- Deterministic dense polynomial over the fixed-size benchmark field. -/
def denseF7Poly (n salt : Nat) : DensePoly F7 :=
  DensePoly.ofCoeffs <| (Array.range n).map fun i => F7.ofNat (coeffValue n i salt).natAbs

/-- Deterministic primitive coefficient used inside nontrivial-content inputs. -/
def primitiveCoeffValue (n i salt : Nat) : Int :=
  let base : Int := if i = 0 then 1 else coeffValue n i salt
  if i % 2 = 0 then base else -base

/-- Deterministic integer polynomial whose coefficient content is nontrivial. -/
def contentPoly (n salt : Nat) : DensePoly Int :=
  let common : Int := Int.ofNat ((salt % 5) + 2)
  DensePoly.ofCoeffs <|
    (Array.range n).map fun i => common * primitiveCoeffValue n i salt

/-- Deterministic monic divisor used by `modByMonic` benchmarks. -/
def monicDivisor (degree : Nat) : DensePoly F7 :=
  { coeffs := (Array.replicate degree (0 : F7)).push 1
    normalized := by
      right
      have hone : ¬((1 : F7) = Zero.zero) := by decide
      simp [hone] }

/-- Generated monomial divisors are monic by construction. -/
theorem monicDivisor_monic (degree : Nat) : DensePoly.Monic (monicDivisor degree) := by
  simp [monicDivisor, DensePoly.Monic, DensePoly.leadingCoeff]

/-- Stable bounded observable for polynomial-valued benchmark results. -/
def checksum [Hashable R] [Zero R] [DecidableEq R] (p : DensePoly R) : UInt64 :=
  p.toArray.foldl (fun acc coeff => mixHash acc (hash coeff)) 0

/-- Stable bounded observable for pairs of polynomial-valued benchmark results. -/
def checksumPair [Hashable R] [Zero R] [DecidableEq R] (p q : DensePoly R) : UInt64 :=
  mixHash (checksum p) (checksum q)

/-- Per-parameter fixture for addition, subtraction, and multiplication. -/
def prepBinaryInput (n : Nat) : BinaryInput :=
  { lhs := densePoly n 11
    rhs := densePoly n 37 }

/-- Per-parameter fixture for derivative benchmarks. -/
def prepUnaryInput (n : Nat) : UnaryInput :=
  { poly := densePoly n 53 }

/-- Per-parameter fixture for integer content and primitive-part benchmarks. -/
def prepContentInput (n : Nat) : ContentInput :=
  { poly := contentPoly n 229 }

/-- Per-parameter fixture for Horner evaluation. -/
def prepEvalInput (n : Nat) : EvalInput :=
  { poly := denseF7Poly n 71
    point := F7.ofNat 3 }

/-- Per-parameter fixture for same-size dense polynomial composition. -/
def prepComposeInput (n : Nat) : ComposeInput :=
  { outer := densePoly n 89
    inner := densePoly n 107 }

/-- Per-parameter fixture for field-polynomial long division. -/
def prepEuclidInput (n : Nat) : EuclidInput :=
  { dividend := denseF7Poly (2 * n + 1) 131
    divisor := denseF7Poly (n + 1) 173 }

/-- Consecutive polynomial Fibonacci inputs force many Euclidean quotient steps. -/
def prepEuclidWorstInput (n : Nat) : EuclidInput :=
  let x := DensePoly.monomial 1 (1 : F7)
  let pair :=
    (List.range (n + 1)).foldl
      (fun state _ =>
        let prev := state.1
        let curr := state.2
        (curr, x * curr + prev))
      ((0 : DensePoly F7), (1 : DensePoly F7))
  { dividend := pair.2
    divisor := pair.1 }

/-- Per-parameter fixture for division by a monic polynomial. -/
def prepMonicInput (n : Nat) : MonicInput :=
  { dividend := denseF7Poly (2 * n + 1) 191
    divisorDegree := n + 1 }

/-- Per-parameter fixture for polynomial CRT witness construction. -/
def prepPolyCRTInput (n : Nat) : PolyCRTInput :=
  let modulusDegree := n + 1
  let monomial := DensePoly.monomial modulusDegree (1 : Rat)
  { modulusA := monomial
    modulusB := monomial + DensePoly.C (1 : Rat)
    residueA := denseRatPoly n 251
    residueB := denseRatPoly n 283
    bezoutS := DensePoly.C (-1 : Rat)
    bezoutT := DensePoly.C (1 : Rat) }

/-- Benchmark target: add two prepared dense polynomials and checksum the result. -/
def runAddChecksum (input : BinaryInput) : UInt64 :=
  checksum (input.lhs + input.rhs)

/-- Benchmark target: subtract two prepared dense polynomials and checksum the result. -/
def runSubChecksum (input : BinaryInput) : UInt64 :=
  checksum (input.lhs - input.rhs)

/-- Benchmark target: multiply two prepared dense polynomials and checksum the result. -/
def runMulChecksum (input : BinaryInput) : UInt64 :=
  checksum (input.lhs * input.rhs)

/-- Benchmark target: evaluate a prepared dense polynomial at a fixed point. -/
def runEval (input : EvalInput) : F7 :=
  DensePoly.eval input.poly input.point

/-- Benchmark target: compose two prepared same-size dense polynomials. -/
def runComposeChecksum (input : ComposeInput) : UInt64 :=
  checksum (DensePoly.compose input.outer input.inner)

/-- Benchmark target: compute the formal derivative and checksum the result. -/
def runDerivativeChecksum (input : UnaryInput) : UInt64 :=
  checksum (DensePoly.derivative input.poly)

/-- Benchmark target: compute quotient and remainder, then checksum both outputs. -/
def runDivModChecksum (input : EuclidInput) : UInt64 :=
  let qr := DensePoly.divMod input.dividend input.divisor
  checksumPair qr.1 qr.2

/-- Benchmark target: compute the quotient from field-polynomial long division. -/
def runDivChecksum (input : EuclidInput) : UInt64 :=
  checksum (input.dividend / input.divisor)

/-- Benchmark target: compute the remainder from field-polynomial long division. -/
def runModChecksum (input : EuclidInput) : UInt64 :=
  checksum (input.dividend % input.divisor)

/-- Benchmark target: compute the remainder from division by a monic polynomial. -/
def runModByMonicChecksum (input : MonicInput) : UInt64 :=
  let divisor := monicDivisor input.divisorDegree
  checksum (DensePoly.modByMonic input.dividend divisor (monicDivisor_monic input.divisorDegree))

/-- Benchmark target: compute the Euclidean gcd and checksum the result. -/
def runGcdChecksum (input : EuclidInput) : UInt64 :=
  checksum (DensePoly.gcd input.dividend input.divisor)

/-- Benchmark target: compute extended gcd and checksum gcd plus Bezout outputs. -/
def runXGcdChecksum (input : EuclidInput) : UInt64 :=
  let result := DensePoly.xgcd input.dividend input.divisor
  mixHash (checksum result.gcd) (checksumPair result.left result.right)

/-- Benchmark target: compute integer coefficient content. -/
def runContent (input : ContentInput) : Int :=
  DensePoly.content input.poly

/-- Benchmark target: compute integer primitive part and checksum the result. -/
def runPrimitivePartChecksum (input : ContentInput) : UInt64 :=
  checksum (DensePoly.primitivePart input.poly)

/-- Benchmark target: construct a polynomial CRT witness and checksum it. -/
def runPolyCRTChecksum (input : PolyCRTInput) : UInt64 :=
  checksum <|
    DensePoly.polyCRT
      input.modulusA input.modulusB input.residueA input.residueB input.bezoutS input.bezoutT

def polyIntToJson (p : DensePoly Int) : Lean.Json :=
  Hex.BenchOracle.Flint.intsToJson p.toArray.toList

def checksumIntJsonCoeffs (j : Lean.Json) : IO UInt64 := do
  let coeffs ← Hex.BenchOracle.Flint.jsonToInts j
  return checksum (DensePoly.ofCoeffs coeffs.toArray : DensePoly Int)

def runFlintBinaryChecksum (op : String) (input : BinaryInput) : IO UInt64 := do
  let result ← Hex.BenchOracle.Flint.runOp "fmpz_poly" op
    #[("a", polyIntToJson input.lhs), ("b", polyIntToJson input.rhs)]
  checksumIntJsonCoeffs result

def runFlintUnaryChecksum (op : String) (input : UnaryInput) : IO UInt64 := do
  let result ← Hex.BenchOracle.Flint.runOp "fmpz_poly" op
    #[("a", polyIntToJson input.poly)]
  checksumIntJsonCoeffs result

def runFlintContentChecksumOp (op : String) (input : ContentInput) : IO UInt64 := do
  let result ← Hex.BenchOracle.Flint.runOp "fmpz_poly" op
    #[("a", polyIntToJson input.poly)]
  checksumIntJsonCoeffs result

/-- FLINT comparator target: `fmpz_poly` addition. -/
def runFlintAddChecksum (input : BinaryInput) : IO UInt64 :=
  runFlintBinaryChecksum "add" input

/-- FLINT comparator target: `fmpz_poly` subtraction. -/
def runFlintSubChecksum (input : BinaryInput) : IO UInt64 :=
  runFlintBinaryChecksum "sub" input

/-- FLINT comparator target: `fmpz_poly` multiplication. -/
def runFlintMulChecksum (input : BinaryInput) : IO UInt64 :=
  runFlintBinaryChecksum "mul" input

/-- FLINT comparator target: `fmpz_poly` composition. -/
def runFlintComposeChecksum (input : ComposeInput) : IO UInt64 := do
  let result ← Hex.BenchOracle.Flint.runOp "fmpz_poly" "compose"
    #[("a", polyIntToJson input.outer), ("b", polyIntToJson input.inner)]
  checksumIntJsonCoeffs result

/-- FLINT comparator target: `fmpz_poly` derivative. -/
def runFlintDerivativeChecksum (input : UnaryInput) : IO UInt64 :=
  runFlintUnaryChecksum "derivative" input

/-- FLINT comparator target: `fmpz_poly` content. -/
def runFlintContent (input : ContentInput) : IO Int := do
  let result ← Hex.BenchOracle.Flint.runOp "fmpz_poly" "content"
    #[("a", polyIntToJson input.poly)]
  match result.getInt? with
  | Except.ok n => return n
  | Except.error msg =>
      throw <| IO.userError s!"FLINT content result was not an integer: {msg}"

/-- FLINT comparator target: `fmpz_poly` primitive part. -/
def runFlintPrimitivePartChecksum (input : ContentInput) : IO UInt64 :=
  runFlintContentChecksumOp "primitive_part" input

setup_benchmark runAddChecksum n => n
  with prep := prepBinaryInput
  where {
    paramFloor := 8192
    paramCeiling := 131072
    paramSchedule := .custom #[8192, 12288, 16384, 24576, 32768, 49152, 65536, 98304, 131072]
    maxSecondsPerCall := 2.0
    targetInnerNanos := 200000000
    signalFloorMultiplier := 1.0
  }

setup_benchmark runSubChecksum n => n
  with prep := prepBinaryInput
  where {
    paramFloor := 8192
    paramCeiling := 131072
    paramSchedule := .custom #[8192, 12288, 16384, 24576, 32768, 49152, 65536, 98304, 131072]
    maxSecondsPerCall := 2.0
    targetInnerNanos := 200000000
    signalFloorMultiplier := 1.0
  }

setup_benchmark runMulChecksum n => n * n
  with prep := prepBinaryInput
  where {
    paramFloor := 128
    paramCeiling := 512
    paramSchedule := .custom #[128, 160, 192, 224, 256, 320, 384, 448, 512]
    maxSecondsPerCall := 3.0
    targetInnerNanos := 200000000
    signalFloorMultiplier := 1.0
  }

setup_benchmark runEval n => n
  with prep := prepEvalInput
  where {
    paramFloor := 8192
    paramCeiling := 131072
    paramSchedule := .custom #[8192, 16384, 32768, 65536, 131072]
    maxSecondsPerCall := 2.0
    targetInnerNanos := 200000000
    signalFloorMultiplier := 1.0
  }

setup_benchmark runComposeChecksum n => n * n * n * n
  with prep := prepComposeInput
  where {
    paramFloor := 16
    paramCeiling := 64
    paramSchedule := .custom #[16, 20, 24, 28, 32, 40, 48, 56, 64]
    maxSecondsPerCall := 3.0
    targetInnerNanos := 200000000
    signalFloorMultiplier := 1.0
  }

setup_benchmark runDerivativeChecksum n => n
  with prep := prepUnaryInput
  where {
    paramFloor := 8192
    paramCeiling := 131072
    paramSchedule := .custom #[8192, 12288, 16384, 24576, 32768, 49152, 65536, 98304, 131072]
    maxSecondsPerCall := 2.0
    targetInnerNanos := 200000000
    signalFloorMultiplier := 1.0
  }

setup_benchmark runDivModChecksum n => n * n
  with prep := prepEuclidInput
  where {
    paramFloor := 64
    paramCeiling := 512
    paramSchedule := .custom #[64, 96, 128, 192, 256, 384, 512]
    maxSecondsPerCall := 3.0
    targetInnerNanos := 200000000
    signalFloorMultiplier := 1.0
  }

setup_benchmark runDivChecksum n => n * n
  with prep := prepEuclidInput
  where {
    paramFloor := 64
    paramCeiling := 512
    paramSchedule := .custom #[64, 96, 128, 192, 256, 384, 512]
    maxSecondsPerCall := 3.0
    targetInnerNanos := 200000000
    signalFloorMultiplier := 1.0
  }

setup_benchmark runModChecksum n => n * n
  with prep := prepEuclidInput
  where {
    paramFloor := 64
    paramCeiling := 512
    paramSchedule := .custom #[64, 96, 128, 192, 256, 384, 512]
    maxSecondsPerCall := 3.0
    targetInnerNanos := 200000000
    signalFloorMultiplier := 1.0
  }

setup_benchmark runModByMonicChecksum n => n * n
  with prep := prepMonicInput
  where {
    paramFloor := 64
    paramCeiling := 512
    paramSchedule := .custom #[64, 96, 128, 192, 256, 384, 512]
    maxSecondsPerCall := 3.0
    targetInnerNanos := 200000000
    signalFloorMultiplier := 1.0
  }

/-
The prepared inputs are consecutive polynomial Fibonacci values. That shape
intentionally forces the Euclidean worst case: Theta(n) quotient steps. Each
division in the chain has quotient `x` and spends linear work in the current
degree, so the decreasing-degree divisions sum to Theta(n^2).
-/
setup_benchmark runGcdChecksum n => n * n
  with prep := prepEuclidWorstInput
  where {
    paramFloor := 16
    paramCeiling := 96
    paramSchedule := .custom #[16, 24, 32, 48, 64, 96]
    maxSecondsPerCall := 4.0
    targetInnerNanos := 200000000
    signalFloorMultiplier := 1.0
  }

/-
This uses the same Fibonacci quotient-chain fixture as `runGcdChecksum`.
Extended gcd carries Bezout updates in the same Euclidean loop; here every
quotient is degree one, so each Bezout multiplication/update is linear in the
current coefficient length. Those updates and the divisions both sum to
Theta(n^2) over the decreasing-degree chain, matching the declared worst-case
polynomial Euclidean bound.
-/
setup_benchmark runXGcdChecksum n => n * n
  with prep := prepEuclidWorstInput
  where {
    paramFloor := 16
    paramCeiling := 96
    paramSchedule := .custom #[16, 24, 32, 48, 64, 96]
    maxSecondsPerCall := 4.0
    targetInnerNanos := 200000000
    signalFloorMultiplier := 1.0
  }

setup_benchmark runContent n => n
  with prep := prepContentInput
  where {
    paramFloor := 8192
    paramCeiling := 131072
    paramSchedule := .custom #[8192, 12288, 16384, 24576, 32768, 49152, 65536, 98304, 131072]
    maxSecondsPerCall := 2.0
    targetInnerNanos := 200000000
    signalFloorMultiplier := 1.0
  }

setup_benchmark runPrimitivePartChecksum n => n
  with prep := prepContentInput
  where {
    paramFloor := 8192
    paramCeiling := 131072
    paramSchedule := .custom #[8192, 12288, 16384, 24576, 32768, 49152, 65536, 98304, 131072]
    maxSecondsPerCall := 2.0
    targetInnerNanos := 200000000
    signalFloorMultiplier := 1.0
  }

setup_benchmark runPolyCRTChecksum n => n * n
  with prep := prepPolyCRTInput
  where {
    paramFloor := 128
    paramCeiling := 512
    paramSchedule := .custom #[128, 192, 256, 384, 512]
    maxSecondsPerCall := 3.0
    targetInnerNanos := 200000000
    signalFloorMultiplier := 1.0
  }

/-- Fixed Lean endpoint paired with FLINT `fmpz_poly` addition. -/
def runtimeNat (n : Nat) : IO Nat := do
  discard <| IO.monoNanosNow
  return n

def runFixedAddChecksum8192 : Unit → IO UInt64 := fun _ =>
  return runAddChecksum (prepBinaryInput (← runtimeNat 8192))

/-- Fixed FLINT `fmpz_poly` addition endpoint. -/
def runFixedFlintAddChecksum8192 : Unit → IO UInt64 := fun _ =>
  runFlintAddChecksum (prepBinaryInput 8192)

setup_fixed_benchmark runFixedAddChecksum8192 where {
  repeats := 5
  maxSecondsPerCall := 10.0
}

setup_fixed_benchmark runFixedFlintAddChecksum8192 where {
  repeats := 5
  maxSecondsPerCall := 10.0
}

def runFixedSubChecksum8192 : Unit → IO UInt64 := fun _ =>
  return runSubChecksum (prepBinaryInput (← runtimeNat 8192))

def runFixedFlintSubChecksum8192 : Unit → IO UInt64 := fun _ =>
  runFlintSubChecksum (prepBinaryInput 8192)

def runFixedDerivativeChecksum8192 : Unit → IO UInt64 := fun _ =>
  return runDerivativeChecksum (prepUnaryInput (← runtimeNat 8192))

def runFixedFlintDerivativeChecksum8192 : Unit → IO UInt64 := fun _ =>
  runFlintDerivativeChecksum (prepUnaryInput 8192)

def runFixedContent8192 : Unit → IO Int := fun _ =>
  return runContent (prepContentInput (← runtimeNat 8192))

def runFixedFlintContent8192 : Unit → IO Int := fun _ =>
  runFlintContent (prepContentInput 8192)

def runFixedPrimitivePartChecksum8192 : Unit → IO UInt64 := fun _ =>
  return runPrimitivePartChecksum (prepContentInput (← runtimeNat 8192))

def runFixedFlintPrimitivePartChecksum8192 : Unit → IO UInt64 := fun _ =>
  runFlintPrimitivePartChecksum (prepContentInput 8192)

def runFixedMulChecksum512 : Unit → IO UInt64 := fun _ =>
  return runMulChecksum (prepBinaryInput (← runtimeNat 512))

def runFixedFlintMulChecksum512 : Unit → IO UInt64 := fun _ =>
  runFlintMulChecksum (prepBinaryInput 512)

def runFixedComposeChecksum64 : Unit → IO UInt64 := fun _ =>
  return runComposeChecksum (prepComposeInput (← runtimeNat 64))

def runFixedFlintComposeChecksum64 : Unit → IO UInt64 := fun _ =>
  runFlintComposeChecksum (prepComposeInput 64)

setup_fixed_benchmark runFixedSubChecksum8192 where {
  repeats := 5
  maxSecondsPerCall := 10.0
}

setup_fixed_benchmark runFixedFlintSubChecksum8192 where {
  repeats := 5
  maxSecondsPerCall := 10.0
}

setup_fixed_benchmark runFixedDerivativeChecksum8192 where {
  repeats := 5
  maxSecondsPerCall := 10.0
}

setup_fixed_benchmark runFixedFlintDerivativeChecksum8192 where {
  repeats := 5
  maxSecondsPerCall := 10.0
}

setup_fixed_benchmark runFixedContent8192 where {
  repeats := 5
  maxSecondsPerCall := 10.0
}

setup_fixed_benchmark runFixedFlintContent8192 where {
  repeats := 5
  maxSecondsPerCall := 10.0
}

setup_fixed_benchmark runFixedPrimitivePartChecksum8192 where {
  repeats := 5
  maxSecondsPerCall := 10.0
}

setup_fixed_benchmark runFixedFlintPrimitivePartChecksum8192 where {
  repeats := 5
  maxSecondsPerCall := 10.0
}

setup_fixed_benchmark runFixedMulChecksum512 where {
  repeats := 5
  maxSecondsPerCall := 10.0
}

setup_fixed_benchmark runFixedFlintMulChecksum512 where {
  repeats := 5
  maxSecondsPerCall := 10.0
}

setup_fixed_benchmark runFixedComposeChecksum64 where {
  repeats := 5
  maxSecondsPerCall := 10.0
}

setup_fixed_benchmark runFixedFlintComposeChecksum64 where {
  repeats := 5
  maxSecondsPerCall := 10.0
}

end Hex.PolyBench

def main (args : List String) : IO UInt32 :=
  LeanBench.Cli.dispatch args
