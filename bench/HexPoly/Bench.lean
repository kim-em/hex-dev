/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import HexPoly
import Hex.BenchOracle.Flint
import Lean.Data.Json
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

Informational external comparators (FLINT `fmpz_poly` via the shared
persistent-subprocess python-flint driver, per
`SPEC/Libraries/hex-poly.md §"External comparators"` and
`SPEC/benchmarking.md §"External comparators" §"Process call"`):

* `runFlintAddChecksum*` ↔ `runAddChecksum*` (`fmpz_poly.add`)
* `runFlintSubChecksum*` ↔ `runSubChecksum*` (`fmpz_poly.sub`)
* `runFlintMulChecksum*` ↔ `runMulChecksum*` (`fmpz_poly.mul`)
* `runFlintDerivativeChecksum*` ↔ `runDerivativeChecksum*`
  (`fmpz_poly.derivative`)
* `runFlintComposeChecksum*` ↔ `runComposeChecksum*` (`fmpz_poly.compose`)
* `runFlintContent*` ↔ `runContent*` (`fmpz_poly.content`)
* `runFlintPrimitivePartChecksum*` ↔ `runPrimitivePartChecksum*`
  (`fmpz_poly.primitive_part`)

The non-`DensePoly Int` registrations (`runEval`, `runDivModChecksum`,
`runDivChecksum`, `runModChecksum`, `runModByMonicChecksum`,
`runGcdChecksum`, `runXGcdChecksum`, `runPolyCRTChecksum`) do not have
FLINT `fmpz_poly` pairings: they operate over `F7` or `Rat`, and the
SPEC names `fmpz_poly` (integer polynomial) as the comparator.
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
  simp [monicDivisor, DensePoly.Monic, DensePoly.leadingCoeff, Array.getElem_push] <;> rfl

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

/-- Stable bounded observable for a FLINT-returned coefficient list. Matches
`checksum (p : DensePoly Int)` whenever the list is the trimmed coefficient
list of `p`: `Array.foldl op init = Array.toList.foldl op init`, and the
FLINT driver and Hex normalisation both drop trailing zeros. -/
def checksumIntCoeffs (coeffs : List Int) : UInt64 :=
  coeffs.foldl (fun acc coeff => mixHash acc (hash coeff)) 0

/-- Encode a `DensePoly Int` as a JSON coefficient list (ascending degree). -/
def densePolyIntToFlintJson (p : DensePoly Int) : Lean.Json :=
  Hex.BenchOracle.Flint.intsToJson p.toArray.toList

/-- FLINT comparator: `fmpz_poly.add`. Returns the checksum of the result
coefficient list (matches `runAddChecksum` on the same prepared input). -/
def runFlintAddChecksum (input : BinaryInput) : IO UInt64 := do
  let result ← Hex.BenchOracle.Flint.runOp "fmpz_poly" "add"
    #[("a", densePolyIntToFlintJson input.lhs),
      ("b", densePolyIntToFlintJson input.rhs)]
  let coeffs ← Hex.BenchOracle.Flint.jsonToInts result
  return checksumIntCoeffs coeffs

/-- FLINT comparator: `fmpz_poly.sub`. -/
def runFlintSubChecksum (input : BinaryInput) : IO UInt64 := do
  let result ← Hex.BenchOracle.Flint.runOp "fmpz_poly" "sub"
    #[("a", densePolyIntToFlintJson input.lhs),
      ("b", densePolyIntToFlintJson input.rhs)]
  let coeffs ← Hex.BenchOracle.Flint.jsonToInts result
  return checksumIntCoeffs coeffs

/-- FLINT comparator: `fmpz_poly.mul`. -/
def runFlintMulChecksum (input : BinaryInput) : IO UInt64 := do
  let result ← Hex.BenchOracle.Flint.runOp "fmpz_poly" "mul"
    #[("a", densePolyIntToFlintJson input.lhs),
      ("b", densePolyIntToFlintJson input.rhs)]
  let coeffs ← Hex.BenchOracle.Flint.jsonToInts result
  return checksumIntCoeffs coeffs

/-- FLINT comparator: `fmpz_poly.derivative`. -/
def runFlintDerivativeChecksum (input : UnaryInput) : IO UInt64 := do
  let result ← Hex.BenchOracle.Flint.runOp "fmpz_poly" "derivative"
    #[("a", densePolyIntToFlintJson input.poly)]
  let coeffs ← Hex.BenchOracle.Flint.jsonToInts result
  return checksumIntCoeffs coeffs

/-- FLINT comparator: `fmpz_poly.compose`. -/
def runFlintComposeChecksum (input : ComposeInput) : IO UInt64 := do
  let result ← Hex.BenchOracle.Flint.runOp "fmpz_poly" "compose"
    #[("a", densePolyIntToFlintJson input.outer),
      ("b", densePolyIntToFlintJson input.inner)]
  let coeffs ← Hex.BenchOracle.Flint.jsonToInts result
  return checksumIntCoeffs coeffs

/-- FLINT comparator: `fmpz_poly.content`. Returns the integer content
directly (matches `runContent`). -/
def runFlintContent (input : ContentInput) : IO Int := do
  let result ← Hex.BenchOracle.Flint.runOp "fmpz_poly" "content"
    #[("a", densePolyIntToFlintJson input.poly)]
  match result.getInt? with
  | Except.ok n => return n
  | Except.error msg =>
      throw <| IO.userError s!"FLINT fmpz_poly.content result not integer: {msg}"

/-- FLINT comparator: `fmpz_poly.primitive_part`. -/
def runFlintPrimitivePartChecksum (input : ContentInput) : IO UInt64 := do
  let result ← Hex.BenchOracle.Flint.runOp "fmpz_poly" "primitive_part"
    #[("a", densePolyIntToFlintJson input.poly)]
  let coeffs ← Hex.BenchOracle.Flint.jsonToInts result
  return checksumIntCoeffs coeffs

/-! Per-rung wrappers for paired fixed-benchmark registrations. Each
`runFooAt n` calls the Hex target on `prepFooInput n`; each
`runFlintFooAt n` calls the FLINT comparator on the same prepared input
so wall-times are comparable in the same harness. -/

/-- Adapter thunk: build `prepBinaryInput n` and run the Hex addition checksum target. -/
def runAddChecksumAt (n : Nat) : Unit → IO UInt64 := fun _ =>
  return runAddChecksum (prepBinaryInput n)
/-- Adapter thunk: build `prepBinaryInput n` and run the FLINT addition comparator. -/
def runFlintAddChecksumAt (n : Nat) : Unit → IO UInt64 := fun _ =>
  runFlintAddChecksum (prepBinaryInput n)

/-- Adapter thunk: build `prepBinaryInput n` and run the Hex subtraction checksum target. -/
def runSubChecksumAt (n : Nat) : Unit → IO UInt64 := fun _ =>
  return runSubChecksum (prepBinaryInput n)
/-- Adapter thunk: build `prepBinaryInput n` and run the FLINT subtraction comparator. -/
def runFlintSubChecksumAt (n : Nat) : Unit → IO UInt64 := fun _ =>
  runFlintSubChecksum (prepBinaryInput n)

/-- Adapter thunk: build `prepBinaryInput n` and run the Hex multiplication checksum target. -/
def runMulChecksumAt (n : Nat) : Unit → IO UInt64 := fun _ =>
  return runMulChecksum (prepBinaryInput n)
/-- Adapter thunk: build `prepBinaryInput n` and run the FLINT multiplication comparator. -/
def runFlintMulChecksumAt (n : Nat) : Unit → IO UInt64 := fun _ =>
  runFlintMulChecksum (prepBinaryInput n)

/-- Adapter thunk: build `prepUnaryInput n` and run the Hex derivative checksum target. -/
def runDerivativeChecksumAt (n : Nat) : Unit → IO UInt64 := fun _ =>
  return runDerivativeChecksum (prepUnaryInput n)
/-- Adapter thunk: build `prepUnaryInput n` and run the FLINT derivative comparator. -/
def runFlintDerivativeChecksumAt (n : Nat) : Unit → IO UInt64 := fun _ =>
  runFlintDerivativeChecksum (prepUnaryInput n)

/-- Adapter thunk: build `prepComposeInput n` and run the Hex composition checksum target. -/
def runComposeChecksumAt (n : Nat) : Unit → IO UInt64 := fun _ =>
  return runComposeChecksum (prepComposeInput n)
/-- Adapter thunk: build `prepComposeInput n` and run the FLINT composition comparator. -/
def runFlintComposeChecksumAt (n : Nat) : Unit → IO UInt64 := fun _ =>
  runFlintComposeChecksum (prepComposeInput n)

/-- Adapter thunk: build `prepContentInput n` and run the Hex content target. -/
def runContentAt (n : Nat) : Unit → IO Int := fun _ =>
  return runContent (prepContentInput n)
/-- Adapter thunk: build `prepContentInput n` and run the FLINT content comparator. -/
def runFlintContentAt (n : Nat) : Unit → IO Int := fun _ =>
  runFlintContent (prepContentInput n)

/-- Adapter thunk: build `prepContentInput n` and run the Hex primitive-part checksum target. -/
def runPrimitivePartChecksumAt (n : Nat) : Unit → IO UInt64 := fun _ =>
  return runPrimitivePartChecksum (prepContentInput n)
/-- Adapter thunk: build `prepContentInput n` and run the FLINT primitive-part comparator. -/
def runFlintPrimitivePartChecksumAt (n : Nat) : Unit → IO UInt64 := fun _ =>
  runFlintPrimitivePartChecksum (prepContentInput n)

/-! Per-rung concrete bindings used by `setup_fixed_benchmark`. The rung
ladders are densified inside the existing parametric ranges so the
ratio's shape across the eligible range is unambiguous from the data
alone (per `SPEC/benchmarking.md §"Headline reports" §"Comparator
ratios"`). -/

-- O(n) targets over `DensePoly Int`: shared input family
-- `dense-int-arithmetic` (Add/Sub/Derivative) and `integer-content`
-- (Content/PrimitivePart); densified rungs inside `[8192, 131072]`.
def runAddChecksum16384 : Unit → IO UInt64 := runAddChecksumAt 16384
def runFlintAddChecksum16384 : Unit → IO UInt64 := runFlintAddChecksumAt 16384
def runAddChecksum32768 : Unit → IO UInt64 := runAddChecksumAt 32768
def runFlintAddChecksum32768 : Unit → IO UInt64 := runFlintAddChecksumAt 32768
def runAddChecksum49152 : Unit → IO UInt64 := runAddChecksumAt 49152
def runFlintAddChecksum49152 : Unit → IO UInt64 := runFlintAddChecksumAt 49152
def runAddChecksum65536 : Unit → IO UInt64 := runAddChecksumAt 65536
def runFlintAddChecksum65536 : Unit → IO UInt64 := runFlintAddChecksumAt 65536
def runAddChecksum98304 : Unit → IO UInt64 := runAddChecksumAt 98304
def runFlintAddChecksum98304 : Unit → IO UInt64 := runFlintAddChecksumAt 98304
def runAddChecksum131072 : Unit → IO UInt64 := runAddChecksumAt 131072
def runFlintAddChecksum131072 : Unit → IO UInt64 := runFlintAddChecksumAt 131072

def runSubChecksum16384 : Unit → IO UInt64 := runSubChecksumAt 16384
def runFlintSubChecksum16384 : Unit → IO UInt64 := runFlintSubChecksumAt 16384
def runSubChecksum32768 : Unit → IO UInt64 := runSubChecksumAt 32768
def runFlintSubChecksum32768 : Unit → IO UInt64 := runFlintSubChecksumAt 32768
def runSubChecksum49152 : Unit → IO UInt64 := runSubChecksumAt 49152
def runFlintSubChecksum49152 : Unit → IO UInt64 := runFlintSubChecksumAt 49152
def runSubChecksum65536 : Unit → IO UInt64 := runSubChecksumAt 65536
def runFlintSubChecksum65536 : Unit → IO UInt64 := runFlintSubChecksumAt 65536
def runSubChecksum98304 : Unit → IO UInt64 := runSubChecksumAt 98304
def runFlintSubChecksum98304 : Unit → IO UInt64 := runFlintSubChecksumAt 98304
def runSubChecksum131072 : Unit → IO UInt64 := runSubChecksumAt 131072
def runFlintSubChecksum131072 : Unit → IO UInt64 := runFlintSubChecksumAt 131072

def runDerivativeChecksum16384 : Unit → IO UInt64 := runDerivativeChecksumAt 16384
def runFlintDerivativeChecksum16384 : Unit → IO UInt64 :=
  runFlintDerivativeChecksumAt 16384
def runDerivativeChecksum32768 : Unit → IO UInt64 := runDerivativeChecksumAt 32768
def runFlintDerivativeChecksum32768 : Unit → IO UInt64 :=
  runFlintDerivativeChecksumAt 32768
def runDerivativeChecksum49152 : Unit → IO UInt64 := runDerivativeChecksumAt 49152
def runFlintDerivativeChecksum49152 : Unit → IO UInt64 :=
  runFlintDerivativeChecksumAt 49152
def runDerivativeChecksum65536 : Unit → IO UInt64 := runDerivativeChecksumAt 65536
def runFlintDerivativeChecksum65536 : Unit → IO UInt64 :=
  runFlintDerivativeChecksumAt 65536
def runDerivativeChecksum98304 : Unit → IO UInt64 := runDerivativeChecksumAt 98304
def runFlintDerivativeChecksum98304 : Unit → IO UInt64 :=
  runFlintDerivativeChecksumAt 98304
def runDerivativeChecksum131072 : Unit → IO UInt64 := runDerivativeChecksumAt 131072
def runFlintDerivativeChecksum131072 : Unit → IO UInt64 :=
  runFlintDerivativeChecksumAt 131072

def runContent16384 : Unit → IO Int := runContentAt 16384
def runFlintContent16384 : Unit → IO Int := runFlintContentAt 16384
def runContent32768 : Unit → IO Int := runContentAt 32768
def runFlintContent32768 : Unit → IO Int := runFlintContentAt 32768
def runContent49152 : Unit → IO Int := runContentAt 49152
def runFlintContent49152 : Unit → IO Int := runFlintContentAt 49152
def runContent65536 : Unit → IO Int := runContentAt 65536
def runFlintContent65536 : Unit → IO Int := runFlintContentAt 65536
def runContent98304 : Unit → IO Int := runContentAt 98304
def runFlintContent98304 : Unit → IO Int := runFlintContentAt 98304
def runContent131072 : Unit → IO Int := runContentAt 131072
def runFlintContent131072 : Unit → IO Int := runFlintContentAt 131072

def runPrimitivePartChecksum16384 : Unit → IO UInt64 :=
  runPrimitivePartChecksumAt 16384
def runFlintPrimitivePartChecksum16384 : Unit → IO UInt64 :=
  runFlintPrimitivePartChecksumAt 16384
def runPrimitivePartChecksum32768 : Unit → IO UInt64 :=
  runPrimitivePartChecksumAt 32768
def runFlintPrimitivePartChecksum32768 : Unit → IO UInt64 :=
  runFlintPrimitivePartChecksumAt 32768
def runPrimitivePartChecksum49152 : Unit → IO UInt64 :=
  runPrimitivePartChecksumAt 49152
def runFlintPrimitivePartChecksum49152 : Unit → IO UInt64 :=
  runFlintPrimitivePartChecksumAt 49152
def runPrimitivePartChecksum65536 : Unit → IO UInt64 :=
  runPrimitivePartChecksumAt 65536
def runFlintPrimitivePartChecksum65536 : Unit → IO UInt64 :=
  runFlintPrimitivePartChecksumAt 65536
def runPrimitivePartChecksum98304 : Unit → IO UInt64 :=
  runPrimitivePartChecksumAt 98304
def runFlintPrimitivePartChecksum98304 : Unit → IO UInt64 :=
  runFlintPrimitivePartChecksumAt 98304
def runPrimitivePartChecksum131072 : Unit → IO UInt64 :=
  runPrimitivePartChecksumAt 131072
def runFlintPrimitivePartChecksum131072 : Unit → IO UInt64 :=
  runFlintPrimitivePartChecksumAt 131072

-- O(n²) mul: densified rungs inside `[128, 512]`.
def runMulChecksum128 : Unit → IO UInt64 := runMulChecksumAt 128
def runFlintMulChecksum128 : Unit → IO UInt64 := runFlintMulChecksumAt 128
def runMulChecksum192 : Unit → IO UInt64 := runMulChecksumAt 192
def runFlintMulChecksum192 : Unit → IO UInt64 := runFlintMulChecksumAt 192
def runMulChecksum256 : Unit → IO UInt64 := runMulChecksumAt 256
def runFlintMulChecksum256 : Unit → IO UInt64 := runFlintMulChecksumAt 256
def runMulChecksum320 : Unit → IO UInt64 := runMulChecksumAt 320
def runFlintMulChecksum320 : Unit → IO UInt64 := runFlintMulChecksumAt 320
def runMulChecksum384 : Unit → IO UInt64 := runMulChecksumAt 384
def runFlintMulChecksum384 : Unit → IO UInt64 := runFlintMulChecksumAt 384
def runMulChecksum448 : Unit → IO UInt64 := runMulChecksumAt 448
def runFlintMulChecksum448 : Unit → IO UInt64 := runFlintMulChecksumAt 448
def runMulChecksum512 : Unit → IO UInt64 := runMulChecksumAt 512
def runFlintMulChecksum512 : Unit → IO UInt64 := runFlintMulChecksumAt 512

-- O(n^4) compose: densified rungs inside `[16, 64]`.
def runComposeChecksum16 : Unit → IO UInt64 := runComposeChecksumAt 16
def runFlintComposeChecksum16 : Unit → IO UInt64 := runFlintComposeChecksumAt 16
def runComposeChecksum24 : Unit → IO UInt64 := runComposeChecksumAt 24
def runFlintComposeChecksum24 : Unit → IO UInt64 := runFlintComposeChecksumAt 24
def runComposeChecksum32 : Unit → IO UInt64 := runComposeChecksumAt 32
def runFlintComposeChecksum32 : Unit → IO UInt64 := runFlintComposeChecksumAt 32
def runComposeChecksum40 : Unit → IO UInt64 := runComposeChecksumAt 40
def runFlintComposeChecksum40 : Unit → IO UInt64 := runFlintComposeChecksumAt 40
def runComposeChecksum48 : Unit → IO UInt64 := runComposeChecksumAt 48
def runFlintComposeChecksum48 : Unit → IO UInt64 := runFlintComposeChecksumAt 48
def runComposeChecksum56 : Unit → IO UInt64 := runComposeChecksumAt 56
def runFlintComposeChecksum56 : Unit → IO UInt64 := runFlintComposeChecksumAt 56
def runComposeChecksum64 : Unit → IO UInt64 := runComposeChecksumAt 64
def runFlintComposeChecksum64 : Unit → IO UInt64 := runFlintComposeChecksumAt 64

setup_benchmark runAddChecksum n => n
  with prep := prepBinaryInput
  where {
    paramFloor := 8192
    paramCeiling := 131072
    paramSchedule := .custom #[8192, 16384, 32768, 65536, 131072]
    maxSecondsPerCall := 2.0
    targetInnerNanos := 200000000
    signalFloorMultiplier := 1.0
  }

setup_benchmark runSubChecksum n => n
  with prep := prepBinaryInput
  where {
    paramFloor := 8192
    paramCeiling := 131072
    paramSchedule := .custom #[8192, 16384, 32768, 65536, 131072]
    maxSecondsPerCall := 2.0
    targetInnerNanos := 200000000
    signalFloorMultiplier := 1.0
  }

setup_benchmark runMulChecksum n => n * n
  with prep := prepBinaryInput
  where {
    paramFloor := 128
    paramCeiling := 512
    paramSchedule := .custom #[128, 192, 256, 384, 512]
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
    paramSchedule := .custom #[16, 24, 32, 48, 64]
    maxSecondsPerCall := 3.0
    targetInnerNanos := 200000000
    signalFloorMultiplier := 1.0
  }

setup_benchmark runDerivativeChecksum n => n
  with prep := prepUnaryInput
  where {
    paramFloor := 8192
    paramCeiling := 131072
    paramSchedule := .custom #[8192, 16384, 32768, 65536, 131072]
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

/-! ## FLINT `fmpz_poly` informational comparator fixed registrations

Each parametric Lean target on `DensePoly Int` is paired with the
matching FLINT `fmpz_poly` op via the shared persistent-subprocess
driver. The pairs are registered as `setup_fixed_benchmark` rungs at the
same parameter inside the densified eligible range so the headline
report can record raw and overhead-adjusted ratios at each rung and a
trend across the ladder. The comparator is `informational` per
`SPEC/Libraries/hex-poly.md §"External comparators"`: no gating-goal
verdict is required, the ratios are recorded for orientation. -/

setup_fixed_benchmark runAddChecksum16384 where { repeats := 5, maxSecondsPerCall := 6.0 }
setup_fixed_benchmark runFlintAddChecksum16384 where { repeats := 5, maxSecondsPerCall := 6.0 }
setup_fixed_benchmark runAddChecksum32768 where { repeats := 5, maxSecondsPerCall := 6.0 }
setup_fixed_benchmark runFlintAddChecksum32768 where { repeats := 5, maxSecondsPerCall := 6.0 }
setup_fixed_benchmark runAddChecksum49152 where { repeats := 5, maxSecondsPerCall := 6.0 }
setup_fixed_benchmark runFlintAddChecksum49152 where { repeats := 5, maxSecondsPerCall := 6.0 }
setup_fixed_benchmark runAddChecksum65536 where { repeats := 5, maxSecondsPerCall := 6.0 }
setup_fixed_benchmark runFlintAddChecksum65536 where { repeats := 5, maxSecondsPerCall := 6.0 }
setup_fixed_benchmark runAddChecksum98304 where { repeats := 5, maxSecondsPerCall := 6.0 }
setup_fixed_benchmark runFlintAddChecksum98304 where { repeats := 5, maxSecondsPerCall := 6.0 }
setup_fixed_benchmark runAddChecksum131072 where { repeats := 5, maxSecondsPerCall := 6.0 }
setup_fixed_benchmark runFlintAddChecksum131072 where { repeats := 5, maxSecondsPerCall := 6.0 }

setup_fixed_benchmark runSubChecksum16384 where { repeats := 5, maxSecondsPerCall := 6.0 }
setup_fixed_benchmark runFlintSubChecksum16384 where { repeats := 5, maxSecondsPerCall := 6.0 }
setup_fixed_benchmark runSubChecksum32768 where { repeats := 5, maxSecondsPerCall := 6.0 }
setup_fixed_benchmark runFlintSubChecksum32768 where { repeats := 5, maxSecondsPerCall := 6.0 }
setup_fixed_benchmark runSubChecksum49152 where { repeats := 5, maxSecondsPerCall := 6.0 }
setup_fixed_benchmark runFlintSubChecksum49152 where { repeats := 5, maxSecondsPerCall := 6.0 }
setup_fixed_benchmark runSubChecksum65536 where { repeats := 5, maxSecondsPerCall := 6.0 }
setup_fixed_benchmark runFlintSubChecksum65536 where { repeats := 5, maxSecondsPerCall := 6.0 }
setup_fixed_benchmark runSubChecksum98304 where { repeats := 5, maxSecondsPerCall := 6.0 }
setup_fixed_benchmark runFlintSubChecksum98304 where { repeats := 5, maxSecondsPerCall := 6.0 }
setup_fixed_benchmark runSubChecksum131072 where { repeats := 5, maxSecondsPerCall := 6.0 }
setup_fixed_benchmark runFlintSubChecksum131072 where { repeats := 5, maxSecondsPerCall := 6.0 }

setup_fixed_benchmark runMulChecksum128 where { repeats := 5, maxSecondsPerCall := 6.0 }
setup_fixed_benchmark runFlintMulChecksum128 where { repeats := 5, maxSecondsPerCall := 6.0 }
setup_fixed_benchmark runMulChecksum192 where { repeats := 5, maxSecondsPerCall := 6.0 }
setup_fixed_benchmark runFlintMulChecksum192 where { repeats := 5, maxSecondsPerCall := 6.0 }
setup_fixed_benchmark runMulChecksum256 where { repeats := 5, maxSecondsPerCall := 6.0 }
setup_fixed_benchmark runFlintMulChecksum256 where { repeats := 5, maxSecondsPerCall := 6.0 }
setup_fixed_benchmark runMulChecksum320 where { repeats := 5, maxSecondsPerCall := 6.0 }
setup_fixed_benchmark runFlintMulChecksum320 where { repeats := 5, maxSecondsPerCall := 6.0 }
setup_fixed_benchmark runMulChecksum384 where { repeats := 5, maxSecondsPerCall := 6.0 }
setup_fixed_benchmark runFlintMulChecksum384 where { repeats := 5, maxSecondsPerCall := 6.0 }
setup_fixed_benchmark runMulChecksum448 where { repeats := 5, maxSecondsPerCall := 6.0 }
setup_fixed_benchmark runFlintMulChecksum448 where { repeats := 5, maxSecondsPerCall := 6.0 }
setup_fixed_benchmark runMulChecksum512 where { repeats := 5, maxSecondsPerCall := 6.0 }
setup_fixed_benchmark runFlintMulChecksum512 where { repeats := 5, maxSecondsPerCall := 6.0 }

setup_fixed_benchmark runDerivativeChecksum16384 where { repeats := 5, maxSecondsPerCall := 6.0 }
setup_fixed_benchmark runFlintDerivativeChecksum16384 where { repeats := 5, maxSecondsPerCall := 6.0 }
setup_fixed_benchmark runDerivativeChecksum32768 where { repeats := 5, maxSecondsPerCall := 6.0 }
setup_fixed_benchmark runFlintDerivativeChecksum32768 where { repeats := 5, maxSecondsPerCall := 6.0 }
setup_fixed_benchmark runDerivativeChecksum49152 where { repeats := 5, maxSecondsPerCall := 6.0 }
setup_fixed_benchmark runFlintDerivativeChecksum49152 where { repeats := 5, maxSecondsPerCall := 6.0 }
setup_fixed_benchmark runDerivativeChecksum65536 where { repeats := 5, maxSecondsPerCall := 6.0 }
setup_fixed_benchmark runFlintDerivativeChecksum65536 where { repeats := 5, maxSecondsPerCall := 6.0 }
setup_fixed_benchmark runDerivativeChecksum98304 where { repeats := 5, maxSecondsPerCall := 6.0 }
setup_fixed_benchmark runFlintDerivativeChecksum98304 where { repeats := 5, maxSecondsPerCall := 6.0 }
setup_fixed_benchmark runDerivativeChecksum131072 where { repeats := 5, maxSecondsPerCall := 6.0 }
setup_fixed_benchmark runFlintDerivativeChecksum131072 where { repeats := 5, maxSecondsPerCall := 6.0 }

setup_fixed_benchmark runComposeChecksum16 where { repeats := 5, maxSecondsPerCall := 6.0 }
setup_fixed_benchmark runFlintComposeChecksum16 where { repeats := 5, maxSecondsPerCall := 6.0 }
setup_fixed_benchmark runComposeChecksum24 where { repeats := 5, maxSecondsPerCall := 6.0 }
setup_fixed_benchmark runFlintComposeChecksum24 where { repeats := 5, maxSecondsPerCall := 6.0 }
setup_fixed_benchmark runComposeChecksum32 where { repeats := 5, maxSecondsPerCall := 6.0 }
setup_fixed_benchmark runFlintComposeChecksum32 where { repeats := 5, maxSecondsPerCall := 6.0 }
setup_fixed_benchmark runComposeChecksum40 where { repeats := 5, maxSecondsPerCall := 6.0 }
setup_fixed_benchmark runFlintComposeChecksum40 where { repeats := 5, maxSecondsPerCall := 6.0 }
setup_fixed_benchmark runComposeChecksum48 where { repeats := 5, maxSecondsPerCall := 6.0 }
setup_fixed_benchmark runFlintComposeChecksum48 where { repeats := 5, maxSecondsPerCall := 6.0 }
setup_fixed_benchmark runComposeChecksum56 where { repeats := 5, maxSecondsPerCall := 6.0 }
setup_fixed_benchmark runFlintComposeChecksum56 where { repeats := 5, maxSecondsPerCall := 6.0 }
setup_fixed_benchmark runComposeChecksum64 where { repeats := 5, maxSecondsPerCall := 6.0 }
setup_fixed_benchmark runFlintComposeChecksum64 where { repeats := 5, maxSecondsPerCall := 6.0 }

setup_fixed_benchmark runContent16384 where { repeats := 5, maxSecondsPerCall := 6.0 }
setup_fixed_benchmark runFlintContent16384 where { repeats := 5, maxSecondsPerCall := 6.0 }
setup_fixed_benchmark runContent32768 where { repeats := 5, maxSecondsPerCall := 6.0 }
setup_fixed_benchmark runFlintContent32768 where { repeats := 5, maxSecondsPerCall := 6.0 }
setup_fixed_benchmark runContent49152 where { repeats := 5, maxSecondsPerCall := 6.0 }
setup_fixed_benchmark runFlintContent49152 where { repeats := 5, maxSecondsPerCall := 6.0 }
setup_fixed_benchmark runContent65536 where { repeats := 5, maxSecondsPerCall := 6.0 }
setup_fixed_benchmark runFlintContent65536 where { repeats := 5, maxSecondsPerCall := 6.0 }
setup_fixed_benchmark runContent98304 where { repeats := 5, maxSecondsPerCall := 6.0 }
setup_fixed_benchmark runFlintContent98304 where { repeats := 5, maxSecondsPerCall := 6.0 }
setup_fixed_benchmark runContent131072 where { repeats := 5, maxSecondsPerCall := 6.0 }
setup_fixed_benchmark runFlintContent131072 where { repeats := 5, maxSecondsPerCall := 6.0 }

setup_fixed_benchmark runPrimitivePartChecksum16384 where { repeats := 5, maxSecondsPerCall := 6.0 }
setup_fixed_benchmark runFlintPrimitivePartChecksum16384 where { repeats := 5, maxSecondsPerCall := 6.0 }
setup_fixed_benchmark runPrimitivePartChecksum32768 where { repeats := 5, maxSecondsPerCall := 6.0 }
setup_fixed_benchmark runFlintPrimitivePartChecksum32768 where { repeats := 5, maxSecondsPerCall := 6.0 }
setup_fixed_benchmark runPrimitivePartChecksum49152 where { repeats := 5, maxSecondsPerCall := 6.0 }
setup_fixed_benchmark runFlintPrimitivePartChecksum49152 where { repeats := 5, maxSecondsPerCall := 6.0 }
setup_fixed_benchmark runPrimitivePartChecksum65536 where { repeats := 5, maxSecondsPerCall := 6.0 }
setup_fixed_benchmark runFlintPrimitivePartChecksum65536 where { repeats := 5, maxSecondsPerCall := 6.0 }
setup_fixed_benchmark runPrimitivePartChecksum98304 where { repeats := 5, maxSecondsPerCall := 6.0 }
setup_fixed_benchmark runFlintPrimitivePartChecksum98304 where { repeats := 5, maxSecondsPerCall := 6.0 }
setup_fixed_benchmark runPrimitivePartChecksum131072 where { repeats := 5, maxSecondsPerCall := 6.0 }
setup_fixed_benchmark runFlintPrimitivePartChecksum131072 where { repeats := 5, maxSecondsPerCall := 6.0 }

end Hex.PolyBench

def main (args : List String) : IO UInt32 :=
  LeanBench.Cli.dispatch args
