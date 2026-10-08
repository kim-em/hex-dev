/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import HexRealAlgebraic
import LeanBench
import Hex.BenchOracle.Flint

/-! Scalar size axes for the shipped API. Inputs and expected polynomial fingerprints are
prepared outside timed requests. Arithmetic checks minimal polynomial/sign;
comparison/rounding return their exact result. External arms check exact annihilation and sign, without a preconstructed
expected nonrational result for add/sqrt, and include JSON transport and temporary cleanup, with separately measured protocol controls.
These fixed ladders are descriptive performance observations, not cost-model or
budget attestations. No forward comparison-strategy extension is implemented. -/
namespace Hex.RealAlgebraicScaling
open RealAlgebraicNumber

private def real (a : AlgebraicNumber) : RealAlgebraicNumber :=
  (ofAlgebraic? a).getD (Hex.panicWith 0 "nonreal scaling fixture")

private structure Input where
  a : RealAlgebraicNumber
  b : RealAlgebraicNumber
  -- Rational reference or near-integer rounding operand; unused for add/sqrt.
  expected : RealAlgebraicNumber
  q : Rat
  polynomial : Array Int := #[]

initialize inputs : IO.Ref (Array (String × Nat × Input)) ← IO.mkRef #[]

private def prepare (operation : String) (size : Nat) : IO Input := do
  if let some entry := (← inputs.get).find? (fun e => e.1 == operation && e.2.1 == size) then
    return entry.2.2
  let input := if operation == "rational" then
    let q : Rat := Rat.ofInt ((2 ^ size - 1) / 3 : Nat) / Rat.ofInt (2 ^ size + 1 : Nat)
    let a := ofRat q
    { a := a, b := a, expected := a, q := q : Input }
  else if operation == "add" || operation == "sqrt" then
    let p : ZPoly := DensePoly.ofCoeffs ((Array.replicate size (0 : Int)).push 1 |>.set! 0 (-2))
    let a := real (p.rootNear (3 / 2))
    let polynomial := if operation == "add" then
      (DensePoly.natPow (#p[-1, 1] : ZPoly) size - DensePoly.C 2).toArray
      else (Array.replicate (2 * size) (0 : Int)).push 1 |>.set! 0 (-2)
    { a := a, b := 1, expected := 0, q := 0, polynomial := polynomial : Input }
  else
    let a := real (ZPoly.rootNear #p[-2, 0, 1] (3 / 2))
    let shift := ofRat (1 / (2 ^ size : Rat))
    { a := a, b := a + shift, expected := 1 + a * shift, q := 0 : Input }
  inputs.modify (·.push (operation, size, input))
  return input

private def native (operation : String) (size : Nat) : IO Bool := do
  let i ← prepare operation size
  match operation with
  | "add" =>
      let result := i.a + i.b
      return result.toAlgebraic.p.toArray == i.polynomial && result.sign == 1
  | "sqrt" =>
      let some result := i.a.sqrt? | return false
      return result.toAlgebraic.p.toArray == i.polynomial && result.sign == 1
  | "compare" => return RealAlgebraicNumber.compare i.a i.b == Ordering.lt
  | "floor" => return i.expected.floor == 1
  | "ceil" => return i.expected.ceil == 2
  | "rational" => return ofRat i.q == i.expected
  | _ => throw (IO.userError "unsupported scalar operation")

initialize comparators : IO.Ref (Array (String × Hex.BenchOracle.Flint.PersistentComparator)) ← IO.mkRef #[]

private def external (tool operation : String) (size : Nat) (control : Bool) : IO Bool := do
  let driver ← match (← comparators.get).find? (fun e => e.1 == tool) with
    | some e => pure e.2
    | none => do
      let python := (← IO.getEnv "HEX_FLINT_BENCH_PYTHON").getD "python3"
      let path : System.FilePath := "scripts/oracle/real_algebraic_scaling_bench.py"
      let script := if (← path.pathExists) then path.toString else "../scripts/oracle/real_algebraic_scaling_bench.py"
      let driver ← Hex.BenchOracle.Flint.PersistentComparator.spawn python #[script, "--tool", tool]
      comparators.modify (·.push (tool, driver))
      pure driver
  let reply ← driver.requestLine (Lean.Json.mkObj [("operation", Lean.toJson operation),
    ("size", Lean.toJson size), ("control", Lean.toJson control)]).compress
  let parsed ← IO.ofExcept (Lean.Json.parse reply)
  unless (← IO.ofExcept (parsed.getObjValAs? Bool "ok")) do
    throw (IO.userError reply)
  IO.ofExcept (parsed.getObjValAs? Bool "result")

private def observations : LeanBench.FixedBenchmarkConfig := {
  repeats := 4, maxSecondsPerCall := 60, killGraceMs := 0,
  warmupFirstIter := true, expectedHash := some (hash true)
}

def runAdd2 : Unit → IO Bool := fun _ => native "add" 2
setup_fixed_benchmark runAdd2 where observations

def runFlintAdd2 : Unit → IO Bool := fun _ => external "flint" "add" 2 false
setup_fixed_benchmark runFlintAdd2 where observations

def runFlintAdd2Protocol : Unit → IO Bool := fun _ => external "flint" "add" 2 true
setup_fixed_benchmark runFlintAdd2Protocol where observations

def runZ3Add2 : Unit → IO Bool := fun _ => external "z3" "add" 2 false
setup_fixed_benchmark runZ3Add2 where observations

def runZ3Add2Protocol : Unit → IO Bool := fun _ => external "z3" "add" 2 true
setup_fixed_benchmark runZ3Add2Protocol where observations

def runAdd4 : Unit → IO Bool := fun _ => native "add" 4
setup_fixed_benchmark runAdd4 where observations

def runFlintAdd4 : Unit → IO Bool := fun _ => external "flint" "add" 4 false
setup_fixed_benchmark runFlintAdd4 where observations

def runFlintAdd4Protocol : Unit → IO Bool := fun _ => external "flint" "add" 4 true
setup_fixed_benchmark runFlintAdd4Protocol where observations

def runZ3Add4 : Unit → IO Bool := fun _ => external "z3" "add" 4 false
setup_fixed_benchmark runZ3Add4 where observations

def runZ3Add4Protocol : Unit → IO Bool := fun _ => external "z3" "add" 4 true
setup_fixed_benchmark runZ3Add4Protocol where observations

def runAdd8 : Unit → IO Bool := fun _ => native "add" 8
setup_fixed_benchmark runAdd8 where observations

def runFlintAdd8 : Unit → IO Bool := fun _ => external "flint" "add" 8 false
setup_fixed_benchmark runFlintAdd8 where observations

def runFlintAdd8Protocol : Unit → IO Bool := fun _ => external "flint" "add" 8 true
setup_fixed_benchmark runFlintAdd8Protocol where observations

def runZ3Add8 : Unit → IO Bool := fun _ => external "z3" "add" 8 false
setup_fixed_benchmark runZ3Add8 where observations

def runZ3Add8Protocol : Unit → IO Bool := fun _ => external "z3" "add" 8 true
setup_fixed_benchmark runZ3Add8Protocol where observations

def runSqrt2 : Unit → IO Bool := fun _ => native "sqrt" 2
setup_fixed_benchmark runSqrt2 where observations

def runFlintSqrt2 : Unit → IO Bool := fun _ => external "flint" "sqrt" 2 false
setup_fixed_benchmark runFlintSqrt2 where observations

def runFlintSqrt2Protocol : Unit → IO Bool := fun _ => external "flint" "sqrt" 2 true
setup_fixed_benchmark runFlintSqrt2Protocol where observations

def runZ3Sqrt2 : Unit → IO Bool := fun _ => external "z3" "sqrt" 2 false
setup_fixed_benchmark runZ3Sqrt2 where observations

def runZ3Sqrt2Protocol : Unit → IO Bool := fun _ => external "z3" "sqrt" 2 true
setup_fixed_benchmark runZ3Sqrt2Protocol where observations

def runSqrt4 : Unit → IO Bool := fun _ => native "sqrt" 4
setup_fixed_benchmark runSqrt4 where observations

def runFlintSqrt4 : Unit → IO Bool := fun _ => external "flint" "sqrt" 4 false
setup_fixed_benchmark runFlintSqrt4 where observations

def runFlintSqrt4Protocol : Unit → IO Bool := fun _ => external "flint" "sqrt" 4 true
setup_fixed_benchmark runFlintSqrt4Protocol where observations

def runZ3Sqrt4 : Unit → IO Bool := fun _ => external "z3" "sqrt" 4 false
setup_fixed_benchmark runZ3Sqrt4 where observations

def runZ3Sqrt4Protocol : Unit → IO Bool := fun _ => external "z3" "sqrt" 4 true
setup_fixed_benchmark runZ3Sqrt4Protocol where observations

def runSqrt8 : Unit → IO Bool := fun _ => native "sqrt" 8
setup_fixed_benchmark runSqrt8 where observations

def runFlintSqrt8 : Unit → IO Bool := fun _ => external "flint" "sqrt" 8 false
setup_fixed_benchmark runFlintSqrt8 where observations

def runFlintSqrt8Protocol : Unit → IO Bool := fun _ => external "flint" "sqrt" 8 true
setup_fixed_benchmark runFlintSqrt8Protocol where observations

def runZ3Sqrt8 : Unit → IO Bool := fun _ => external "z3" "sqrt" 8 false
setup_fixed_benchmark runZ3Sqrt8 where observations

def runZ3Sqrt8Protocol : Unit → IO Bool := fun _ => external "z3" "sqrt" 8 true
setup_fixed_benchmark runZ3Sqrt8Protocol where observations

def runCompare4 : Unit → IO Bool := fun _ => native "compare" 4
setup_fixed_benchmark runCompare4 where observations

def runFlintCompare4 : Unit → IO Bool := fun _ => external "flint" "compare" 4 false
setup_fixed_benchmark runFlintCompare4 where observations

def runFlintCompare4Protocol : Unit → IO Bool := fun _ => external "flint" "compare" 4 true
setup_fixed_benchmark runFlintCompare4Protocol where observations

def runZ3Compare4 : Unit → IO Bool := fun _ => external "z3" "compare" 4 false
setup_fixed_benchmark runZ3Compare4 where observations

def runZ3Compare4Protocol : Unit → IO Bool := fun _ => external "z3" "compare" 4 true
setup_fixed_benchmark runZ3Compare4Protocol where observations

def runCompare16 : Unit → IO Bool := fun _ => native "compare" 16
setup_fixed_benchmark runCompare16 where observations

def runFlintCompare16 : Unit → IO Bool := fun _ => external "flint" "compare" 16 false
setup_fixed_benchmark runFlintCompare16 where observations

def runFlintCompare16Protocol : Unit → IO Bool := fun _ => external "flint" "compare" 16 true
setup_fixed_benchmark runFlintCompare16Protocol where observations

def runZ3Compare16 : Unit → IO Bool := fun _ => external "z3" "compare" 16 false
setup_fixed_benchmark runZ3Compare16 where observations

def runZ3Compare16Protocol : Unit → IO Bool := fun _ => external "z3" "compare" 16 true
setup_fixed_benchmark runZ3Compare16Protocol where observations

def runCompare64 : Unit → IO Bool := fun _ => native "compare" 64
setup_fixed_benchmark runCompare64 where observations

def runFlintCompare64 : Unit → IO Bool := fun _ => external "flint" "compare" 64 false
setup_fixed_benchmark runFlintCompare64 where observations

def runFlintCompare64Protocol : Unit → IO Bool := fun _ => external "flint" "compare" 64 true
setup_fixed_benchmark runFlintCompare64Protocol where observations

def runZ3Compare64 : Unit → IO Bool := fun _ => external "z3" "compare" 64 false
setup_fixed_benchmark runZ3Compare64 where observations

def runZ3Compare64Protocol : Unit → IO Bool := fun _ => external "z3" "compare" 64 true
setup_fixed_benchmark runZ3Compare64Protocol where observations

def runCompare256 : Unit → IO Bool := fun _ => native "compare" 256
setup_fixed_benchmark runCompare256 where observations

def runFlintCompare256 : Unit → IO Bool := fun _ => external "flint" "compare" 256 false
setup_fixed_benchmark runFlintCompare256 where observations

def runFlintCompare256Protocol : Unit → IO Bool := fun _ => external "flint" "compare" 256 true
setup_fixed_benchmark runFlintCompare256Protocol where observations

def runZ3Compare256 : Unit → IO Bool := fun _ => external "z3" "compare" 256 false
setup_fixed_benchmark runZ3Compare256 where observations

def runZ3Compare256Protocol : Unit → IO Bool := fun _ => external "z3" "compare" 256 true
setup_fixed_benchmark runZ3Compare256Protocol where observations

def runFloor4 : Unit → IO Bool := fun _ => native "floor" 4
setup_fixed_benchmark runFloor4 where observations

def runFlintFloor4 : Unit → IO Bool := fun _ => external "flint" "floor" 4 false
setup_fixed_benchmark runFlintFloor4 where observations

def runFlintFloor4Protocol : Unit → IO Bool := fun _ => external "flint" "floor" 4 true
setup_fixed_benchmark runFlintFloor4Protocol where observations

def runFloor16 : Unit → IO Bool := fun _ => native "floor" 16
setup_fixed_benchmark runFloor16 where observations

def runFlintFloor16 : Unit → IO Bool := fun _ => external "flint" "floor" 16 false
setup_fixed_benchmark runFlintFloor16 where observations

def runFlintFloor16Protocol : Unit → IO Bool := fun _ => external "flint" "floor" 16 true
setup_fixed_benchmark runFlintFloor16Protocol where observations

def runFloor64 : Unit → IO Bool := fun _ => native "floor" 64
setup_fixed_benchmark runFloor64 where observations

def runFlintFloor64 : Unit → IO Bool := fun _ => external "flint" "floor" 64 false
setup_fixed_benchmark runFlintFloor64 where observations

def runFlintFloor64Protocol : Unit → IO Bool := fun _ => external "flint" "floor" 64 true
setup_fixed_benchmark runFlintFloor64Protocol where observations

def runFloor256 : Unit → IO Bool := fun _ => native "floor" 256
setup_fixed_benchmark runFloor256 where observations

def runFlintFloor256 : Unit → IO Bool := fun _ => external "flint" "floor" 256 false
setup_fixed_benchmark runFlintFloor256 where observations

def runFlintFloor256Protocol : Unit → IO Bool := fun _ => external "flint" "floor" 256 true
setup_fixed_benchmark runFlintFloor256Protocol where observations

def runCeil4 : Unit → IO Bool := fun _ => native "ceil" 4
setup_fixed_benchmark runCeil4 where observations

def runFlintCeil4 : Unit → IO Bool := fun _ => external "flint" "ceil" 4 false
setup_fixed_benchmark runFlintCeil4 where observations

def runFlintCeil4Protocol : Unit → IO Bool := fun _ => external "flint" "ceil" 4 true
setup_fixed_benchmark runFlintCeil4Protocol where observations

def runCeil16 : Unit → IO Bool := fun _ => native "ceil" 16
setup_fixed_benchmark runCeil16 where observations

def runFlintCeil16 : Unit → IO Bool := fun _ => external "flint" "ceil" 16 false
setup_fixed_benchmark runFlintCeil16 where observations

def runFlintCeil16Protocol : Unit → IO Bool := fun _ => external "flint" "ceil" 16 true
setup_fixed_benchmark runFlintCeil16Protocol where observations

def runCeil64 : Unit → IO Bool := fun _ => native "ceil" 64
setup_fixed_benchmark runCeil64 where observations

def runFlintCeil64 : Unit → IO Bool := fun _ => external "flint" "ceil" 64 false
setup_fixed_benchmark runFlintCeil64 where observations

def runFlintCeil64Protocol : Unit → IO Bool := fun _ => external "flint" "ceil" 64 true
setup_fixed_benchmark runFlintCeil64Protocol where observations

def runCeil256 : Unit → IO Bool := fun _ => native "ceil" 256
setup_fixed_benchmark runCeil256 where observations

def runFlintCeil256 : Unit → IO Bool := fun _ => external "flint" "ceil" 256 false
setup_fixed_benchmark runFlintCeil256 where observations

def runFlintCeil256Protocol : Unit → IO Bool := fun _ => external "flint" "ceil" 256 true
setup_fixed_benchmark runFlintCeil256Protocol where observations

def runRational16 : Unit → IO Bool := fun _ => native "rational" 16
setup_fixed_benchmark runRational16 where observations

def runFlintRational16 : Unit → IO Bool := fun _ => external "flint" "rational" 16 false
setup_fixed_benchmark runFlintRational16 where observations

def runFlintRational16Protocol : Unit → IO Bool := fun _ => external "flint" "rational" 16 true
setup_fixed_benchmark runFlintRational16Protocol where observations

def runZ3Rational16 : Unit → IO Bool := fun _ => external "z3" "rational" 16 false
setup_fixed_benchmark runZ3Rational16 where observations

def runZ3Rational16Protocol : Unit → IO Bool := fun _ => external "z3" "rational" 16 true
setup_fixed_benchmark runZ3Rational16Protocol where observations

def runRational64 : Unit → IO Bool := fun _ => native "rational" 64
setup_fixed_benchmark runRational64 where observations

def runFlintRational64 : Unit → IO Bool := fun _ => external "flint" "rational" 64 false
setup_fixed_benchmark runFlintRational64 where observations

def runFlintRational64Protocol : Unit → IO Bool := fun _ => external "flint" "rational" 64 true
setup_fixed_benchmark runFlintRational64Protocol where observations

def runZ3Rational64 : Unit → IO Bool := fun _ => external "z3" "rational" 64 false
setup_fixed_benchmark runZ3Rational64 where observations

def runZ3Rational64Protocol : Unit → IO Bool := fun _ => external "z3" "rational" 64 true
setup_fixed_benchmark runZ3Rational64Protocol where observations

def runRational256 : Unit → IO Bool := fun _ => native "rational" 256
setup_fixed_benchmark runRational256 where observations

def runFlintRational256 : Unit → IO Bool := fun _ => external "flint" "rational" 256 false
setup_fixed_benchmark runFlintRational256 where observations

def runFlintRational256Protocol : Unit → IO Bool := fun _ => external "flint" "rational" 256 true
setup_fixed_benchmark runFlintRational256Protocol where observations

def runZ3Rational256 : Unit → IO Bool := fun _ => external "z3" "rational" 256 false
setup_fixed_benchmark runZ3Rational256 where observations

def runZ3Rational256Protocol : Unit → IO Bool := fun _ => external "z3" "rational" 256 true
setup_fixed_benchmark runZ3Rational256Protocol where observations

def runRational1024 : Unit → IO Bool := fun _ => native "rational" 1024
setup_fixed_benchmark runRational1024 where observations

def runFlintRational1024 : Unit → IO Bool := fun _ => external "flint" "rational" 1024 false
setup_fixed_benchmark runFlintRational1024 where observations

def runFlintRational1024Protocol : Unit → IO Bool := fun _ => external "flint" "rational" 1024 true
setup_fixed_benchmark runFlintRational1024Protocol where observations

def runZ3Rational1024 : Unit → IO Bool := fun _ => external "z3" "rational" 1024 false
setup_fixed_benchmark runZ3Rational1024 where observations

def runZ3Rational1024Protocol : Unit → IO Bool := fun _ => external "z3" "rational" 1024 true
setup_fixed_benchmark runZ3Rational1024Protocol where observations

/-- Untimed boundary diagnostic for the retained larger square-root fixture.
Its setup marker lets a whole-child cap distinguish construction from operation. -/
def sqrtProbe : IO UInt32 := do
  let start ← IO.monoNanosNow
  let _ ← prepare "sqrt" 8
  IO.println (Lean.Json.mkObj [("stage", Lean.toJson ("prepared" : String)),
    ("elapsed_ns", Lean.toJson ((← IO.monoNanosNow) - start))]).compress
  (← IO.getStdout).flush
  let start ← IO.monoNanosNow
  let result ← runSqrt8 ()
  IO.println (Lean.Json.mkObj [("stage", Lean.toJson ("operation" : String)),
    ("elapsed_ns", Lean.toJson ((← IO.monoNanosNow) - start)),
    ("result", Lean.toJson result)]).compress
  return if result then 0 else 1

end Hex.RealAlgebraicScaling


/-! Compiled coverage of the shipped real subtype, independent of real closure.
Canonical inputs are supplied through IO references, preventing closed-expression
constant folding. Construction of arithmetic operands is outside timed bodies;
The rational, repeated-root, complex norm/projection and root-solving cases
include the explicitly named construction in their timed bodies. The forward
comparison-strategy extension is excluded from these registrations.

These fixed cases are coverage and baseline observations. A fixed observation
alone is not Phase-4 performance evidence: the report must justify its selected
mode and an operation-specific budget, or retain the operation as a Concern.
-/

namespace Hex.RealAlgebraicBench
open RealAlgebraicNumber

private def real (a : AlgebraicNumber) : RealAlgebraicNumber :=
  (ofAlgebraic? a).getD (Hex.panicWith 0 "benchmark input is nonreal")

initialize rationalRef : IO.Ref Rat ← IO.mkRef (-3 / 2)
initialize pairRef : IO.Ref (RealAlgebraicNumber × RealAlgebraicNumber) ←
  IO.mkRef (real (ZPoly.rootNear #p[-2, 0, 1] (3 / 2)),
    real (ZPoly.rootNear #p[-3, 0, 1] (7 / 4)))
initialize integerPolyRef : IO.Ref (Array Int) ← IO.mkRef #[1, 0, -10, 0, 1]

private def algebraicChecksum (a : AlgebraicNumber) : UInt64 :=
  hash (a.p.toArray, a.rep.1.square.re.toRat, a.rep.1.square.im.toRat, a.rep.1.square.prec)

private def checksum (a : RealAlgebraicNumber) : UInt64 := algebraicChecksum a.toAlgebraic

private def optionChecksum (a : Option RealAlgebraicNumber) : UInt64 :=
  (a.map checksum).getD 0

private def rootsChecksum : RealRootSet → UInt64
  | .all => 1
  | .finite entries => hash (entries.map fun r => (checksum r.root, r.multiplicity))

initialize closeRef : IO.Ref (Option (RealAlgebraicNumber × RealAlgebraicNumber)) ←
  IO.mkRef none

private def closePair : IO (RealAlgebraicNumber × RealAlgebraicNumber) := do
  if let some pair ← closeRef.get then return pair
  let (a, _) ← pairRef.get
  let shift := 50
  let pair := (a, a + ofRat (1 / (2 ^ shift : Rat)))
  unless (Hex.Interval.realOrder? pair.1.toAlgebraic.rep.1.square
      pair.2.toAlgebraic.rep.1.square).isNone do
    throw (IO.userError "close-comparison fixture must have overlapping stored intervals")
  closeRef.set (some pair)
  return pair

initialize branchRef : IO.Ref (Option (RealAlgebraicNumber × RealAlgebraicNumber ×
    RealAlgebraicNumber)) ← IO.mkRef none

private def branches : IO (RealAlgebraicNumber × RealAlgebraicNumber × RealAlgebraicNumber) := do
  if let some values ← branchRef.get then return values
  let (a, _) ← pairRef.get
  let nearZero := a * ofRat (1 / (2 ^ (50 : Nat) : Rat))
  let values := (-a, nearZero, 1 + nearZero)
  branchRef.set (some values)
  return values

initialize rootsRef : IO.Ref (Option RootSet) ← IO.mkRef none

private def mixedRoots : IO RootSet := do
  if let some roots ← rootsRef.get then return roots
  let roots := (AlgebraicPoly.ofArray #[(-1 : AlgebraicNumber), 0, 0, 0, 1]).roots
  rootsRef.set (some roots)
  return roots

initialize comparatorRef : IO.Ref (Option Hex.BenchOracle.Flint.PersistentComparator) ←
  IO.mkRef none

private def qqbarCompare (fixture : String) : IO UInt64 := do
  let driver ← match (← comparatorRef.get) with
    | some driver => pure driver
    | none => do
      let python := (← IO.getEnv "HEX_FLINT_BENCH_PYTHON").getD "python3"
      let path : System.FilePath := "scripts/oracle/real_algebraic_bench.py"
      let script := if (← path.pathExists) then path.toString
        else "../scripts/oracle/real_algebraic_bench.py"
      let driver ← Hex.BenchOracle.Flint.PersistentComparator.spawn python #[script]
      comparatorRef.set (some driver)
      pure driver
  let reply ← driver.requestLine (Lean.Json.mkObj [("case", Lean.toJson fixture)]).compress
  let parsed ← IO.ofExcept (Lean.Json.parse reply)
  let value ← IO.ofExcept (parsed.getObjValAs? Nat "result")
  return hash value

def runQqbarCompare : Unit → IO UInt64 := fun _ => qqbarCompare "separated"
def runQqbarCloseCompare : Unit → IO UInt64 := fun _ => qqbarCompare "close"
def runQqbarProtocol : Unit → IO UInt64 := fun _ => qqbarCompare "protocol"

private def observations : LeanBench.FixedBenchmarkConfig := {
  repeats := 4
  maxSecondsPerCall := 1
  killGraceMs := 0
  warmupFirstIter := true
}

private structure FieldInput where
  generator : RealAlgebraicNumber
  values : Array (QAdjoin generator.toAlgebraic)

initialize fieldRef : IO.Ref (Option FieldInput) ← IO.mkRef none

private def fieldInput : IO FieldInput := do
  if let some input ← fieldRef.get then return input
  let (a, _) ← pairRef.get
  let x := a.toAlgebraic.toQAdjoin
  let input : FieldInput := ⟨a, #[0, 1, -1, x, -x, x - 1, 1 - x, x + 2, x ^ 3 - 2]⟩
  fieldRef.set (some input)
  return input

/-- The shipped fixed-field sign wrapper on constants and nonconstant coordinates
in the positive square-root-of-two embedding. Scientific warmup prepares the
coordinates; smoke verification includes that first preparation. -/
def runFieldSign : Unit → IO (Array Int) := fun _ => do
  let input ← fieldInput
  return input.values.map input.generator.signField

-- Complete exact-result anchor for the implemented signField API, not a cost model or budget.
setup_fixed_benchmark runFieldSign where { observations with
  expectedHash := some (hash (#[0, 1, -1, 1, -1, 1, -1, 1, 1] : Array Int)) }

def runConstructors : Unit → IO UInt64 := fun _ => do
  let (a, _) ← pairRef.get
  return hash (optionChecksum (ofAlgebraic? a.toAlgebraic),
    checksum (ofAlgebraic a.toAlgebraic a.property), optionChecksum (ofRoot? a.toAlgebraic.toRoot),
    (ofAlgebraic? AlgebraicNumber.I).isNone)

def runCasts : Unit → IO UInt64 := fun _ => do
  let q ← rationalRef.get
  return hash (checksum (ofRat q), checksum (q.num : RealAlgebraicNumber),
    checksum (q.den : RealAlgebraicNumber))

def runEquality : Unit → IO UInt64 := fun _ => do
  let (a, b) ← pairRef.get
  return hash (a == a, a == b)

def runAdd : Unit → IO UInt64 := fun _ => do
  let (a, b) ← pairRef.get
  return checksum (a + b)

def runSub : Unit → IO UInt64 := fun _ => do
  let (a, b) ← pairRef.get
  return checksum (a - b)

def runMul : Unit → IO UInt64 := fun _ => do
  let (a, b) ← pairRef.get
  return checksum (a * b)

def runNeg : Unit → IO UInt64 := fun _ => do
  let (a, _) ← pairRef.get
  return checksum (-a)

def runInv : Unit → IO UInt64 := fun _ => do
  let (a, _) ← pairRef.get
  return checksum a⁻¹

def runDiv : Unit → IO UInt64 := fun _ => do
  let (a, b) ← pairRef.get
  return checksum (a / b)

def runNatPow : Unit → IO UInt64 := fun _ => do
  let (a, _) ← pairRef.get
  return checksum (a ^ (7 : Nat))

def runIntPow : Unit → IO UInt64 := fun _ => do
  let (a, _) ← pairRef.get
  return checksum (a ^ (-7 : Int))

def runScalars : Unit → IO UInt64 := fun _ => do
  let (a, _) ← pairRef.get
  let q ← rationalRef.get
  return hash (checksum (q • a), checksum (q.num • a), checksum (q.den • a))

def runCompare : Unit → IO UInt64 := fun _ => do
  let (a, b) ← pairRef.get
  return hash (match RealAlgebraicNumber.compare a b with | .lt => (0 : Nat) | .eq => 1 | .gt => 2)

def runCompareExact : Unit → IO UInt64 := fun _ => do
  let (a, b) ← pairRef.get
  return hash (match a.toAlgebraic.realCompareExact b.toAlgebraic with | .lt => (0 : Nat) | .eq => 1 | .gt => 2)

def runCloseCompare : Unit → IO UInt64 := fun _ => do
  let (a, b) ← closePair
  return hash (match RealAlgebraicNumber.compare a b with | .lt => (0 : Nat) | .eq => 1 | .gt => 2)

def runCloseExact : Unit → IO UInt64 := fun _ => do
  let (a, b) ← closePair
  return hash (match a.toAlgebraic.realCompareExact b.toAlgebraic with | .lt => (0 : Nat) | .eq => 1 | .gt => 2)

def runOrder : Unit → IO UInt64 := fun _ => do
  let (a, b) ← pairRef.get
  return hash (decide (a < b), decide (a ≤ b), checksum (RealAlgebraicNumber.min a b), checksum (RealAlgebraicNumber.max a b))

def runSign : Unit → IO UInt64 := fun _ => do
  let (a, _) ← pairRef.get
  let (negative, nearZero, _) ← branches
  return hash (a.sign, negative.sign, nearZero.sign, (0 : RealAlgebraicNumber).sign)

def runAbs : Unit → IO UInt64 := fun _ => do
  let (a, _) ← pairRef.get
  let (negative, _, _) ← branches
  return hash (checksum a.abs, checksum negative.abs, checksum (0 : RealAlgebraicNumber).abs)

def runConj : Unit → IO UInt64 := fun _ => do
  let (a, _) ← pairRef.get
  return checksum a.conj

def runRational : Unit → IO UInt64 := fun _ => do
  let q ← rationalRef.get
  let a := ofRat q
  return hash (a.toRat?, a.floor, a.ceil, checksum (a + 1), checksum (a * a))

def runRounding : Unit → IO UInt64 := fun _ => do
  let (a, _) ← pairRef.get
  let (_, _, nearInteger) ← branches
  return hash (a.floor, a.ceil, a.toRat?, nearInteger.floor, nearInteger.ceil)

def runApprox : Unit → IO UInt64 := fun _ => do
  let (a, _) ← pairRef.get
  let b := a.approxBall 100
  return hash ((a.approx 100).toRat, b.re.toRat, b.im.toRat, b.radius.toRat)

def runSqrt : Unit → IO UInt64 := fun _ => do
  let (a, _) ← pairRef.get
  return optionChecksum a.sqrt?

def runSqrtTotal : Unit → IO UInt64 := fun _ => do
  let (a, _) ← pairRef.get
  return if h : 0 ≤ a then checksum (a.sqrt h)
    else Hex.panicWith 0 "positive square-root fixture"


def runRoots : Unit → IO UInt64 := fun _ => do
  let (a, _) ← pairRef.get
  return rootsChecksum (RealAlgebraicPoly.ofArray #[-a, 0, 1]).roots

def runRepeatedRoots : Unit → IO UInt64 := fun _ => do
  let q ← rationalRef.get
  let a := ofRat q
  return rootsChecksum (RealAlgebraicPoly.ofArray #[a*a, -(2*a), 1]).roots

def runIntegerRoots : Unit → IO UInt64 := fun _ => do
  let p : ZPoly := DensePoly.ofCoeffs (← integerPolyRef.get)
  return hash (p.realAlgebraicRoots.map checksum)


def runRepr : Unit → IO UInt64 := fun _ => do
  let (a, _) ← pairRef.get
  return hash (repr a).pretty

def runNorm : Unit → IO UInt64 := fun _ => do
  let (a, _) ← pairRef.get
  let q ← rationalRef.get
  return hash (checksum a.toAlgebraic.normSq,
    checksum (AlgebraicNumber.ofPoint q 1).normSq)

def runProjections : Unit → IO UInt64 := fun _ => do
  let q ← rationalRef.get
  let (a, _) ← pairRef.get
  let z := AlgebraicNumber.ofPoint q 1
  return hash (checksum z.re, checksum z.im,
    checksum (real (AlgebraicNumber.ofReal a)))

def runComplexAbs : Unit → IO UInt64 := fun _ => do
  let q ← rationalRef.get
  return checksum (AlgebraicNumber.ofPoint q 1).abs

/-- Exactification, nonreal filtering and real-value sorting of a supplied
quartic root set, independently of polynomial solving. -/
def runFilterRoots : Unit → IO UInt64 := fun _ => do
  return rootsChecksum (RealAlgebraicPoly.realRoots (← mixedRoots))

/-- Eight distinct real roots of the required independent quadratic product. -/
initialize eightRootsRef : IO.Ref (Array Int) ← IO.mkRef #[2, 3, 5, 7]

def runEightRoots : Unit → IO UInt64 := fun _ => do
  let p : ZPoly := (← eightRootsRef.get).foldl (fun p d => p * DensePoly.ofCoeffs #[-d, 0, 1]) 1
  return hash (p.realAlgebraicRoots.map checksum)

/-- Bare dependency route, using the same dynamic operands and checksum. -/
def runBareAdd : Unit → IO UInt64 := fun _ => do
  let (x, y) ← pairRef.get
  let a := x.toAlgebraic
  let b := y.toAlgebraic
  return algebraicChecksum (a + b)

/-- Bare dependency route, using the same dynamic operands and checksum. -/
def runBareSub : Unit → IO UInt64 := fun _ => do
  let (x, y) ← pairRef.get
  let a := x.toAlgebraic
  let b := y.toAlgebraic
  return algebraicChecksum (a - b)

/-- Bare dependency route, using the same dynamic operands and checksum. -/
def runBareMul : Unit → IO UInt64 := fun _ => do
  let (x, y) ← pairRef.get
  let a := x.toAlgebraic
  let b := y.toAlgebraic
  return algebraicChecksum (a * b)

/-- Bare dependency route, using the same dynamic operands and checksum. -/
def runBareDiv : Unit → IO UInt64 := fun _ => do
  let (x, y) ← pairRef.get
  let a := x.toAlgebraic
  let b := y.toAlgebraic
  return algebraicChecksum (a / b)

/-- Bare dependency route, using the same dynamic operands and checksum. -/
def runBareNeg : Unit → IO UInt64 := fun _ => do
  let (x, _) ← pairRef.get
  let a := x.toAlgebraic
  return algebraicChecksum (-a)

/-- Bare dependency route, using the same dynamic operands and checksum. -/
def runBareInv : Unit → IO UInt64 := fun _ => do
  let (x, _) ← pairRef.get
  let a := x.toAlgebraic
  return algebraicChecksum (a⁻¹)

/-- Bare dependency route, using the same dynamic operands and checksum. -/
def runBareNatPow : Unit → IO UInt64 := fun _ => do
  let (x, _) ← pairRef.get
  let a := x.toAlgebraic
  return algebraicChecksum (a ^ (7 : Nat))

/-- Bare dependency route, using the same dynamic operands and checksum. -/
def runBareIntPow : Unit → IO UInt64 := fun _ => do
  let (x, _) ← pairRef.get
  let a := x.toAlgebraic
  return algebraicChecksum (a ^ (-7 : Int))

-- API coverage anchor; this operational cap makes no performance claim.
setup_fixed_benchmark runConstructors where observations
-- API coverage anchor; this operational cap makes no performance claim.
setup_fixed_benchmark runCasts where observations
-- API coverage anchor; this operational cap makes no performance claim.
setup_fixed_benchmark runEquality where observations
-- API coverage anchor; this operational cap makes no performance claim.
setup_fixed_benchmark runBareAdd where observations
setup_fixed_benchmark runBareSub where observations
setup_fixed_benchmark runBareMul where observations
setup_fixed_benchmark runBareDiv where observations
setup_fixed_benchmark runBareNeg where observations
setup_fixed_benchmark runBareInv where observations
setup_fixed_benchmark runBareNatPow where observations
setup_fixed_benchmark runBareIntPow where observations
setup_fixed_benchmark runAdd where observations
-- API coverage anchor; this operational cap makes no performance claim.
setup_fixed_benchmark runSub where observations
-- API coverage anchor; this operational cap makes no performance claim.
setup_fixed_benchmark runMul where observations
-- API coverage anchor; this operational cap makes no performance claim.
setup_fixed_benchmark runNeg where observations
-- API coverage anchor; this operational cap makes no performance claim.
setup_fixed_benchmark runInv where observations
-- API coverage anchor; this operational cap makes no performance claim.
setup_fixed_benchmark runDiv where observations
-- API coverage anchor; this operational cap makes no performance claim.
setup_fixed_benchmark runNatPow where observations
-- API coverage anchor; this operational cap makes no performance claim.
setup_fixed_benchmark runIntPow where observations
-- API coverage anchor; this operational cap makes no performance claim.
setup_fixed_benchmark runScalars where observations
-- API coverage anchor; this operational cap makes no performance claim.
setup_fixed_benchmark runCompare where { observations with expectedHash := some 0 }
-- API coverage anchor; this operational cap makes no performance claim.
setup_fixed_benchmark runCompareExact where { observations with expectedHash := some 0 }
-- API coverage anchor; this operational cap makes no performance claim.
setup_fixed_benchmark runOrder where observations
-- API coverage anchor; this operational cap makes no performance claim.
setup_fixed_benchmark runSign where observations
-- API coverage anchor; this operational cap makes no performance claim.
setup_fixed_benchmark runAbs where observations
-- API coverage anchor; this operational cap makes no performance claim.
setup_fixed_benchmark runConj where observations
-- API coverage anchor; this operational cap makes no performance claim.
setup_fixed_benchmark runRational where observations
-- API coverage anchor; this operational cap makes no performance claim.
setup_fixed_benchmark runRounding where observations
-- API coverage anchor; this operational cap makes no performance claim.
setup_fixed_benchmark runApprox where observations
-- API coverage anchor; this operational cap makes no performance claim.
setup_fixed_benchmark runSqrt where observations
-- API coverage anchor; this operational cap makes no performance claim.
setup_fixed_benchmark runSqrtTotal where observations
-- API coverage anchor; this operational cap makes no performance claim.
setup_fixed_benchmark runRoots where observations
-- API coverage anchor; this operational cap makes no performance claim.
setup_fixed_benchmark runRepeatedRoots where observations
-- API coverage anchor; this operational cap makes no performance claim.
setup_fixed_benchmark runIntegerRoots where observations
-- API coverage anchor; this operational cap makes no performance claim.
setup_fixed_benchmark runRepr where observations
-- API coverage anchor; this operational cap makes no performance claim.
setup_fixed_benchmark runNorm where observations
-- API coverage anchor; this operational cap makes no performance claim.
setup_fixed_benchmark runComplexAbs where observations

-- Fixed close-value and coordinate-projection coverage, including overlap.
setup_fixed_benchmark runFilterRoots where observations
setup_fixed_benchmark runEightRoots where { observations with maxSecondsPerCall := 10 }
setup_fixed_benchmark runQqbarCompare where { observations with expectedHash := some 0 }
setup_fixed_benchmark runQqbarCloseCompare where { observations with expectedHash := some 0 }
setup_fixed_benchmark runQqbarProtocol where { observations with expectedHash := some 0 }
setup_fixed_benchmark runCloseCompare where { observations with expectedHash := some 0 }
setup_fixed_benchmark runCloseExact where { observations with expectedHash := some 0 }
setup_fixed_benchmark runProjections where observations

structure ArrayInput where
  coefficients : Array RealAlgebraicNumber
  roots : RealRootSet
  absent : RealAlgebraicNumber

instance : Hashable ArrayInput where
  hash i := hash (i.coefficients.map checksum, checksum i.absent)

def arrayInput (n : Nat) : ArrayInput :=
  let values := (List.range n).toArray.map fun k => ofRat (k + 1 : Nat)
  { coefficients := values,
    roots := .finite (values.map fun a => ⟨a, 1, by decide⟩),
    absent := ofRat (n + 1 : Nat) }

def runPolyConstructors (i : ArrayInput) : Nat × Bool :=
  let f := RealAlgebraicPoly.ofArray i.coefficients
  (f.toAlgebraic.coeffs.size, (RealAlgebraicPoly.ofAlgebraic? f.toAlgebraic).isSome)

def runMembership (i : ArrayInput) : Bool := i.roots.contains i.absent

def runRootSet (i : ArrayInput) : Bool × Nat :=
  (i.roots.finite?.isSome, i.roots.toArray.size)

-- Cost model: normalization maps n nonzero coefficients once; the reality
-- check scans the n stored coefficients. Their bounded rational isolations
-- make each projection/reality test constant word work on this ladder.
setup_benchmark runPolyConstructors n => n
  with prep := arrayInput
  where {
    paramSchedule := .custom #[16, 32, 64, 128, 256]
    paramFloor := 16
    paramCeiling := 256
    outerTrials := 4
    targetInnerNanos := 100000000
    signalFloorMultiplier := 1
    maxSecondsPerCall := 3
  }

-- Cost model: the absent value forces all n Boolean canonical comparisons.
-- Each polynomial has degree one and bounded coefficients in this ladder.
setup_benchmark runMembership n => n
  with prep := arrayInput
  where {
    paramSchedule := .custom #[16, 32, 64, 128, 256]
    paramFloor := 16
    paramCeiling := 256
    outerTrials := 4
    targetInnerNanos := 100000000
    signalFloorMultiplier := 1
    maxSecondsPerCall := 3
  }

-- Cost model: finite? and toArray inspect the root-set tag and project the
-- existing array. Reading its stored size takes constant work for all n.
setup_benchmark runRootSet _n => 1
  with prep := arrayInput
  where {
    paramSchedule := .custom #[16, 32, 64, 128, 256]
    paramFloor := 16
    paramCeiling := 256
    outerTrials := 4
    targetInnerNanos := 100000000
    signalFloorMultiplier := 1
    maxSecondsPerCall := 3
  }

/-- Independent calls of the actual per-root exactification phase. Each input
is a valid root witness; this batch is not asserted to be one polynomial's
complete root set. Fixed degree and height make each call constant work. -/
def exactifyInput (n : Nat) : Array RootCount :=
  let root := (ZPoly.rootNear #p[-2, 0, 1] (3 / 2)).toRoot
  Array.replicate n ⟨root, 1, by decide⟩

instance : Hashable RootCount where
  hash r := hash (r.root.p.toArray, r.root.rep.1.square.re.toRat,
    r.root.rep.1.square.im.toRat, r.multiplicity)

def runExactifyRoots (roots : Array RootCount) : Array UInt64 :=
  roots.map fun r => (RealAlgebraicPoly.realRoot? r).map
    (fun a => hash (checksum a.root, a.multiplicity)) |>.getD 0

-- Diagnostic batching control: n calls with identical fixed-size witnesses.
-- Its linear verdict measures array traversal and repeated fixed calls, not
-- growth of the polynomial or the leaf exactification problem. It does not
-- satisfy Phase-4 operation coverage.
setup_benchmark runExactifyRoots n => n
  with prep := exactifyInput
  where {
    paramSchedule := .custom #[8, 16, 32, 64, 128]
    paramFloor := 8
    paramCeiling := 128
    outerTrials := 4
    targetInnerNanos := 100000000
    signalFloorMultiplier := 1
    maxSecondsPerCall := 60
  }

private def reverseBits (width value : Nat) : Nat :=
  (List.range width).foldl (fun acc k => 2 * acc + (value / 2 ^ k) % 2) 0

def sortInput (n : Nat) : Array RealRootCount :=
  (List.range n).toArray.map fun k =>
    ⟨ofRat (reverseBits (Nat.log2 n) k + 1 : Nat), 1, by decide⟩

instance : Hashable RealRootCount where
  hash r := hash (checksum r.root, r.multiplicity)

def runSortRoots (roots : Array RealRootCount) : Array RealRootCount :=
  (roots.toList.mergeSort (fun a b => decide (a.root ≤ b.root))).toArray

-- Two-sided cost model: the same mergeSort/comparator expression used by realRoots.
-- Bit-reversal at power-of-two rungs forces interleaving at every merge.
-- Rational roots 1..n have disjoint stored intervals and word-size heights;
-- each comparison/hash is constant word work. Sorting costs Θ(n log n),
-- and consuming all n resulting roots adds Θ(n) work.
setup_benchmark runSortRoots n => n * (Nat.log2 n + 1)
  with prep := sortInput
  where {
    paramSchedule := .custom #[16, 32, 64, 128, 256]
    paramFloor := 16
    paramCeiling := 256
    outerTrials := 4
    targetInnerNanos := 100000000
    signalFloorMultiplier := 1
    maxSecondsPerCall := 60
  }

/-- Erased-witness packaging, checked packaging, rational recognition and
real projections on word-size rational leaves in a growing coefficient array.
These operations inspect fixed-size canonical leaves, rather than traversing
that array. The results include semantic checks and the recognized rational. -/
def runLeafChecks (i : ArrayInput) : Bool × Bool × Bool × Bool × Option Rat :=
  let a := i.coefficients.getD (i.coefficients.size / 2) 0
  ((ofAlgebraic? a.toAlgebraic).isSome,
    ofAlgebraic a.toAlgebraic a.property == a,
    a.conj == a,
    a.toAlgebraic.re == a.toAlgebraic && a.toAlgebraic.im == 0,
    a.toRat?)

-- Cost-model interpretation, diagnostic control: the array parameter does not drive the leaf operations.
-- Its constant verdict does not satisfy Phase-4 operation coverage.
setup_benchmark runLeafChecks _n => 1
  with prep := arrayInput
  where {
    paramSchedule := .custom #[16, 32, 64, 128, 256]
    paramFloor := 16
    paramCeiling := 256
    outerTrials := 4
    targetInnerNanos := 100000000
    signalFloorMultiplier := 1
    maxSecondsPerCall := 60
  }

initialize hardRef : IO.Ref (Option (RealAlgebraicNumber × RealAlgebraicNumber)) ←
  IO.mkRef none

/-- Positive real member of the parent's degree-product-12 addition family.
This keeps the owner's actual isolator and exactification pipeline. -/
private def hardPair : IO (RealAlgebraicNumber × RealAlgebraicNumber) := do
  if let some pair ← hardRef.get then return pair
  let degree := 6
  let p : ZPoly := DensePoly.ofCoeffs ((Array.replicate (max degree 2) (0 : Int)).push 1 |>.set! 0 (-2))
  let (_, b) ← pairRef.get
  let pair := (real (ZPoly.rootNear p (11 / 10)), b)
  hardRef.set (some pair)
  return pair

private def hardArithmetic (op : Nat) (bare : Bool) : IO UInt64 := do
  let (a, b) ← hardPair
  if bare then
    let a := a.toAlgebraic
    let b := b.toAlgebraic
    let c := match op with
      | 0 => a + b | 1 => a - b | 2 => a * b | 3 => a / b
      | 4 => -a | 5 => a⁻¹ | 6 => a ^ (7 : Nat) | _ => a ^ (-7 : Int)
    return algebraicChecksum c
  else
    let c := match op with
      | 0 => a + b | 1 => a - b | 2 => a * b | 3 => a / b
      | 4 => -a | 5 => a⁻¹ | 6 => a ^ (7 : Nat) | _ => a ^ (-7 : Int)
    return checksum c

def runHardAdd : Unit → IO UInt64 := fun _ => hardArithmetic 0 false
def runHardBareAdd : Unit → IO UInt64 := fun _ => hardArithmetic 0 true
def runHardSub : Unit → IO UInt64 := fun _ => hardArithmetic 1 false
def runHardBareSub : Unit → IO UInt64 := fun _ => hardArithmetic 1 true
def runHardMul : Unit → IO UInt64 := fun _ => hardArithmetic 2 false
def runHardBareMul : Unit → IO UInt64 := fun _ => hardArithmetic 2 true
def runHardDiv : Unit → IO UInt64 := fun _ => hardArithmetic 3 false
def runHardBareDiv : Unit → IO UInt64 := fun _ => hardArithmetic 3 true
def runHardNeg : Unit → IO UInt64 := fun _ => hardArithmetic 4 false
def runHardBareNeg : Unit → IO UInt64 := fun _ => hardArithmetic 4 true
def runHardInv : Unit → IO UInt64 := fun _ => hardArithmetic 5 false
def runHardBareInv : Unit → IO UInt64 := fun _ => hardArithmetic 5 true
def runHardNatPow : Unit → IO UInt64 := fun _ => hardArithmetic 6 false
def runHardBareNatPow : Unit → IO UInt64 := fun _ => hardArithmetic 6 true
def runHardIntPow : Unit → IO UInt64 := fun _ => hardArithmetic 7 false
def runHardBareIntPow : Unit → IO UInt64 := fun _ => hardArithmetic 7 true

-- Canonical-input calibration anchors. No absolute budget or Phase-4 claim
-- is inferred from the operational cap; the report must discharge mode choice.
setup_fixed_benchmark runHardAdd where { observations with maxSecondsPerCall := 60, expectedHash := some 0x7cc18faa80303c8 }
setup_fixed_benchmark runHardBareAdd where { observations with maxSecondsPerCall := 60, expectedHash := some 0x7cc18faa80303c8 }
setup_fixed_benchmark runHardSub where { observations with maxSecondsPerCall := 60, expectedHash := some 0xcfcded9e67ef422a }
setup_fixed_benchmark runHardBareSub where { observations with maxSecondsPerCall := 60, expectedHash := some 0xcfcded9e67ef422a }
setup_fixed_benchmark runHardMul where { observations with maxSecondsPerCall := 60, expectedHash := some 0x7b833c10aa349c1 }
setup_fixed_benchmark runHardBareMul where { observations with maxSecondsPerCall := 60, expectedHash := some 0x7b833c10aa349c1 }
setup_fixed_benchmark runHardDiv where { observations with maxSecondsPerCall := 60, expectedHash := some 0xf93e953cb46d6203 }
setup_fixed_benchmark runHardBareDiv where { observations with maxSecondsPerCall := 60, expectedHash := some 0xf93e953cb46d6203 }
setup_fixed_benchmark runHardNeg where { observations with maxSecondsPerCall := 60, expectedHash := some 0x90151aeb609428ad }
setup_fixed_benchmark runHardBareNeg where { observations with maxSecondsPerCall := 60, expectedHash := some 0x90151aeb609428ad }
setup_fixed_benchmark runHardInv where { observations with maxSecondsPerCall := 60, expectedHash := some 0x7f480553f9384a48 }
setup_fixed_benchmark runHardBareInv where { observations with maxSecondsPerCall := 60, expectedHash := some 0x7f480553f9384a48 }
setup_fixed_benchmark runHardNatPow where { observations with maxSecondsPerCall := 60, expectedHash := some 0xfac774ca5ef39829 }
setup_fixed_benchmark runHardBareNatPow where { observations with maxSecondsPerCall := 60, expectedHash := some 0xfac774ca5ef39829 }
setup_fixed_benchmark runHardIntPow where { observations with maxSecondsPerCall := 60, expectedHash := some 0xee54fcb23d356212 }
setup_fixed_benchmark runHardBareIntPow where { observations with maxSecondsPerCall := 60, expectedHash := some 0xee54fcb23d356212 }

/-- A single degree-one leaf with growing coefficient height. At the even
scientific parameters, the odd numerator `A=(2^b-1)/3` and denominator `D=2^b+1`
satisfy `D=3*A+2` and are coprime. Values approach 1/3 rather than the dyadic value one.
Preparation checks canonical construction and recognition against the rational. -/
structure RationalLeaf where
  value : RealAlgebraicNumber
  rational : Rat

instance : Hashable RationalLeaf where
  hash i := hash (checksum i.value, i.rational)

def rationalLeaf (bits : Nat) : RationalLeaf :=
  let power := 2 ^ (Nat.max bits 2)
  let q : Rat := (((power - 1) / 3 : Nat) : Rat) / ((power + 1 : Nat) : Rat)
  let a := ofRat q
  if a.toAlgebraic.p.natDegree == 1 && a.toRat? == some q then
    ⟨a, q⟩
  else Hex.panicWith ⟨0, 0⟩ "rational-leaf fixture failed its degree/recognition check"

def runRationalRecognition (i : RationalLeaf) : Option Rat := i.value.toRat?

/-- The former coefficient-quotient expression, only as a comparison control.
It uses the same prepared input and core rational arithmetic. -/
def runRationalQuotient (i : RationalLeaf) : Option Rat :=
  let p := i.value.toAlgebraic.p
  if p.natDegree = 1 then some (-(p.coeff 0 : Rat) / (p.coeff 1 : Rat)) else none
def runRationalFloor (i : RationalLeaf) : Int := i.value.floor
def runRationalCeil (i : RationalLeaf) : Int := i.value.ceil

-- Two-sided derivation before measurement: the canonical linear polynomial for
-- q=((2^b-1)/3)/(2^b+1) at even b has primitive coefficients D=3*A+2.
-- Recognition constructs the
-- reduced Rat directly. Negating its borrowed b-bit constant coefficient
-- copies Θ(b) bits in the pinned runtime. Positive-denominator natAbs and
-- record construction add no higher-order work. Rat's structural output hash
-- also performs linear-size Int arithmetic; it does not increase the order.
-- Floor/ceil retain that recognition cost and add at most linear division.
-- These rational-only models do not cover construction or nonrational rounding.
-- The 600-second child cap is an operational safeguard, not a regression
-- budget. The retained first-rung preparation probe exceeded it; this ladder
-- remains unmeasured and unadmitted. Verify's parameters 0 and 1 use two bits
-- so that their fixtures exercise nonzero rational recognition and rounding.
setup_benchmark runRationalRecognition b => b
  with prep := rationalLeaf
  where {
    paramSchedule := .custom #[262144, 524288, 1048576, 2097152]
    paramFloor := 262144
    paramCeiling := 2097152
    outerTrials := 4
    targetInnerNanos := 100000000
    signalFloorMultiplier := 1
    maxSecondsPerCall := 600
  }

-- The same independently derived linear bit-volume model, with rational floor.
setup_benchmark runRationalFloor b => b
  with prep := rationalLeaf
  where {
    paramSchedule := .custom #[262144, 524288, 1048576, 2097152]
    paramFloor := 262144
    paramCeiling := 2097152
    outerTrials := 4
    targetInnerNanos := 100000000
    signalFloorMultiplier := 1
    maxSecondsPerCall := 600
  }

-- The same independently derived linear bit-volume model, with rational ceiling.
setup_benchmark runRationalCeil b => b
  with prep := rationalLeaf
  where {
    paramSchedule := .custom #[262144, 524288, 1048576, 2097152]
    paramFloor := 262144
    paramCeiling := 2097152
    outerTrials := 4
    targetInnerNanos := 100000000
    signalFloorMultiplier := 1
    maxSecondsPerCall := 600
  }

-- Comparison control: D mod A=2, A mod 2=1, so the former normalization
-- has a bounded Euclidean quotient sequence. Single-limb division, reduction
-- and the actual structural result hash require linear Θ(b) limb work on this family.
setup_benchmark runRationalQuotient b => b
  with prep := rationalLeaf
  where {
    paramSchedule := .custom #[262144, 524288, 1048576, 2097152]
    paramFloor := 262144
    paramCeiling := 2097152
    outerTrials := 4
    targetInnerNanos := 100000000
    signalFloorMultiplier := 1
    maxSecondsPerCall := 600
  }

/-! Actual polynomial-root API coverage. `X^n−2` and `X^n−√2` have
exactly one negative and one positive real root at even degree, and only the
positive root at degree one.
Their canonical minimal polynomials are respectively `X^n−2` and `X^(2n)−2`,
by Eisenstein at 2. The complete ordered polynomial/sign/multiplicity array
therefore identifies every output root on these fixtures. This is a benchmark
fingerprint, not a new root representation. No complexity/budget admission is
claimed by these fixed registrations. -/
initialize polyRootsRef : IO.Ref (Array (Nat × Bool × RealAlgebraicPoly)) ← IO.mkRef #[]

private def rootPolynomial (degree : Nat) (quadratic : Bool) : IO RealAlgebraicPoly := do
  let cached ← polyRootsRef.get
  if let some entry := cached.find? (fun entry => entry.1 == degree && entry.2.1 == quadratic) then
    return entry.2.2
  let constant ← if quadratic then do
    let (a, _) ← pairRef.get
    pure (-a)
    else pure (ofRat (-2))
  let f := RealAlgebraicPoly.ofArray ((Array.replicate degree (0 : RealAlgebraicNumber)).push 1 |>.set! 0 constant)
  polyRootsRef.modify (·.push (degree, quadratic, f))
  return f

private def expectedRoots (degree : Nat) (quadratic : Bool) : Array (Array Int × Int × Nat) :=
  let poly := (Array.replicate (if quadratic then 2 * degree else degree) (0 : Int)).push 1 |>.set! 0 (-2)
  if degree == 1 then #[(poly, 1, 1)] else #[(poly, -1, 1), (poly, 1, 1)]

private def polynomialRoots (degree : Nat) (quadratic : Bool) : IO (Array (Array Int × Int × Nat)) := do
  let f ← rootPolynomial degree quadratic
  let some roots := f.roots.finite? | throw (IO.userError "nonzero polynomial returned all roots")
  return roots.map fun entry =>
    (entry.root.toAlgebraic.p.toArray, entry.root.sign, entry.multiplicity)

def runRationalRoots2 : Unit → IO (Array (Array Int × Int × Nat)) := fun _ => polynomialRoots 2 false
setup_fixed_benchmark runRationalRoots2 where { observations with maxSecondsPerCall := 60, expectedHash := some (hash (expectedRoots 2 false)) }

def runRationalRoots4 : Unit → IO (Array (Array Int × Int × Nat)) := fun _ => polynomialRoots 4 false
setup_fixed_benchmark runRationalRoots4 where { observations with maxSecondsPerCall := 60, expectedHash := some (hash (expectedRoots 4 false)) }

def runRationalRoots8 : Unit → IO (Array (Array Int × Int × Nat)) := fun _ => polynomialRoots 8 false
setup_fixed_benchmark runRationalRoots8 where { observations with maxSecondsPerCall := 60, expectedHash := some (hash (expectedRoots 8 false)) }

def runQuadraticRoots1 : Unit → IO (Array (Array Int × Int × Nat)) := fun _ => polynomialRoots 1 true
setup_fixed_benchmark runQuadraticRoots1 where { observations with maxSecondsPerCall := 60, expectedHash := some (hash (expectedRoots 1 true)) }

def runQuadraticRoots2 : Unit → IO (Array (Array Int × Int × Nat)) := fun _ => polynomialRoots 2 true
setup_fixed_benchmark runQuadraticRoots2 where { observations with maxSecondsPerCall := 60, expectedHash := some (hash (expectedRoots 2 true)) }

def runQuadraticRoots4 : Unit → IO (Array (Array Int × Int × Nat)) := fun _ => polynomialRoots 4 true
setup_fixed_benchmark runQuadraticRoots4 where { observations with maxSecondsPerCall := 60, expectedHash := some (hash (expectedRoots 4 true)) }

/- Totally real irreducible heads: start at X and repeatedly square then
subtract two. At degrees 2/4/8 they are Eisenstein at two and have exactly
that many distinct real roots. This varies the number of real entries sharing
one parent, unlike X^n-2. Fixed observations make no timing-model claim. -/
initialize totallyRealRef : IO.Ref (Array (Nat × ZPoly × RealAlgebraicPoly)) ← IO.mkRef #[]

private def totallyRealInput (degree : Nat) : IO (ZPoly × RealAlgebraicPoly) := do
  if let some entry := (← totallyRealRef.get).find? (fun entry => entry.1 == degree) then
    return entry.2
  let p := (List.range (Nat.log2 degree)).foldl (fun (p : ZPoly) _ => p * p - 2) ZPoly.X
  let f := RealAlgebraicPoly.ofArray (p.toArray.map fun (c : Int) => ofRat (c : Rat))
  totallyRealRef.modify (·.push (degree, p, f))
  return (p, f)

/-- The original independent selectors and sorting, without the realRoots
compiler replacement. Both arms include the same lazy root production. -/
@[noinline] private def independentRoots (f : RealAlgebraicPoly) : RealRootSet :=
  match f.toAlgebraic.roots with
  | .all => .all
  | .finite roots => .finite
    (((roots.filterMap RealAlgebraicPoly.realRoot?).toList.mergeSort
      (fun a b => decide (a.root ≤ b.root))).toArray)

private def totallyRealRoots (degree : Nat) (reuse : Bool) : IO Bool := do
  let (p, f) ← totallyRealInput degree
  let roots := if reuse then f.roots else independentRoots f
  let some entries := roots.finite? | throw (IO.userError "nonzero totally real head returned all")
  -- Complete identity on these irreducible heads: degree many distinct sorted
  -- roots with this minimal polynomial and multiplicity one exhaust its roots.
  return entries.size == degree &&
    entries.all (fun r => r.root.toAlgebraic.p == p && r.multiplicity == 1) &&
    (entries.toList.zip entries.toList.tail).all (fun (a, b) => decide (a.root < b.root))

def runTotallyReal2 : Unit → IO Bool := fun _ => totallyRealRoots 2 true
setup_fixed_benchmark runTotallyReal2 where { observations with maxSecondsPerCall := 60, expectedHash := some (hash true) }
def runIndependent2 : Unit → IO Bool := fun _ => totallyRealRoots 2 false
setup_fixed_benchmark runIndependent2 where { observations with maxSecondsPerCall := 60, expectedHash := some (hash true) }
def runTotallyReal4 : Unit → IO Bool := fun _ => totallyRealRoots 4 true
setup_fixed_benchmark runTotallyReal4 where { observations with maxSecondsPerCall := 60, expectedHash := some (hash true) }
def runIndependent4 : Unit → IO Bool := fun _ => totallyRealRoots 4 false
setup_fixed_benchmark runIndependent4 where { observations with maxSecondsPerCall := 60, expectedHash := some (hash true) }
def runTotallyReal8 : Unit → IO Bool := fun _ => totallyRealRoots 8 true
setup_fixed_benchmark runTotallyReal8 where { observations with maxSecondsPerCall := 60, expectedHash := some (hash true) }
def runIndependent8 : Unit → IO Bool := fun _ => totallyRealRoots 8 false
setup_fixed_benchmark runIndependent8 where { observations with maxSecondsPerCall := 60, expectedHash := some (hash true) }

/- A reducible degree-eight control with four distinct quadratic factors.
The existing factor fallback repeats factor-level certification; observe its
practical cost without claiming irreducible-parent reuse applies to it. -/
initialize reducibleRef : IO.Ref (Option (Array ZPoly × RealAlgebraicPoly)) ← IO.mkRef none

private def reducibleRoots (reuse : Bool) : IO Bool := do
  let (factors, f) ← match ← reducibleRef.get with
    | some input => pure input
    | none => do
      let factors := #[2, 3, 5, 7].map (fun (c : Int) => ZPoly.X * ZPoly.X - DensePoly.C c)
      let p := factors.foldl (· * ·) 1
      let f := RealAlgebraicPoly.ofArray (p.toArray.map fun (c : Int) => ofRat (c : Rat))
      let input := (factors, f)
      reducibleRef.set (some input)
      pure input
  let roots := if reuse then f.roots else independentRoots f
  let some entries := roots.finite? | throw (IO.userError "nonzero reducible head returned all")
  return entries.size == 8 && entries.all (fun r => r.multiplicity == 1) &&
    factors.all (fun p => entries.countP (fun r => r.root.toAlgebraic.p == p) == 2) &&
    (entries.toList.zip entries.toList.tail).all (fun (a, b) => decide (a.root < b.root))

def runReducible8 : Unit → IO Bool := fun _ => reducibleRoots true
setup_fixed_benchmark runReducible8 where { observations with maxSecondsPerCall := 60, expectedHash := some (hash true) }
def runIndependentReducible8 : Unit → IO Bool := fun _ => reducibleRoots false
setup_fixed_benchmark runIndependentReducible8 where { observations with maxSecondsPerCall := 60, expectedHash := some (hash true) }

initialize rootsFlintRef : IO.Ref (Option Hex.BenchOracle.Flint.PersistentComparator) ← IO.mkRef none
initialize rootsZ3Ref : IO.Ref (Option Hex.BenchOracle.Flint.PersistentComparator) ← IO.mkRef none

private def externalRoots (tool : String) (degree : Nat) (quadratic : Bool)
    (control := false) : IO (Array (Array Int × Int × Nat)) := do
  let ref := if tool == "flint" then rootsFlintRef else rootsZ3Ref
  let driver ← match (← ref.get) with
    | some driver => pure driver
    | none => do
      let python := (← IO.getEnv "HEX_FLINT_BENCH_PYTHON").getD "python3"
      let path : System.FilePath := "scripts/oracle/real_algebraic_roots_bench.py"
      let script := if (← path.pathExists) then path.toString
        else "../scripts/oracle/real_algebraic_roots_bench.py"
      let driver ← Hex.BenchOracle.Flint.PersistentComparator.spawn python
        (#[script, "--tool", tool] ++ if tool == "flint" then #["--self-test"] else #[])
      ref.set (some driver)
      pure driver
  let reply ← driver.requestLine (Lean.Json.mkObj [
    ("degree", Lean.toJson degree), ("quadratic", Lean.toJson quadratic),
    ("control", Lean.toJson control)]).compress
  let parsed ← IO.ofExcept (Lean.Json.parse reply)
  unless (← IO.ofExcept (parsed.getObjValAs? Bool "ok")) do
    throw (IO.userError s!"exact {tool} roots failed: {reply}")
  return (← IO.ofExcept (parsed.getObjValAs? (Array (Array Int × Int × Nat)) "result"))

def runFlintRationalRoots2 : Unit → IO (Array (Array Int × Int × Nat)) := fun _ => externalRoots "flint" 2 false false
setup_fixed_benchmark runFlintRationalRoots2 where { observations with maxSecondsPerCall := 60, expectedHash := some (hash (expectedRoots 2 false)) }

def runFlintRationalRoots2Protocol : Unit → IO (Array (Array Int × Int × Nat)) := fun _ => externalRoots "flint" 2 false true
setup_fixed_benchmark runFlintRationalRoots2Protocol where { observations with maxSecondsPerCall := 60, expectedHash := some (hash (expectedRoots 2 false)) }

def runZ3RationalRoots2 : Unit → IO (Array (Array Int × Int × Nat)) := fun _ => externalRoots "z3" 2 false false
setup_fixed_benchmark runZ3RationalRoots2 where { observations with maxSecondsPerCall := 60, expectedHash := some (hash (expectedRoots 2 false)) }

def runZ3RationalRoots2Protocol : Unit → IO (Array (Array Int × Int × Nat)) := fun _ => externalRoots "z3" 2 false true
setup_fixed_benchmark runZ3RationalRoots2Protocol where { observations with maxSecondsPerCall := 60, expectedHash := some (hash (expectedRoots 2 false)) }

def runFlintRationalRoots4 : Unit → IO (Array (Array Int × Int × Nat)) := fun _ => externalRoots "flint" 4 false false
setup_fixed_benchmark runFlintRationalRoots4 where { observations with maxSecondsPerCall := 60, expectedHash := some (hash (expectedRoots 4 false)) }

def runFlintRationalRoots4Protocol : Unit → IO (Array (Array Int × Int × Nat)) := fun _ => externalRoots "flint" 4 false true
setup_fixed_benchmark runFlintRationalRoots4Protocol where { observations with maxSecondsPerCall := 60, expectedHash := some (hash (expectedRoots 4 false)) }

def runZ3RationalRoots4 : Unit → IO (Array (Array Int × Int × Nat)) := fun _ => externalRoots "z3" 4 false false
setup_fixed_benchmark runZ3RationalRoots4 where { observations with maxSecondsPerCall := 60, expectedHash := some (hash (expectedRoots 4 false)) }

def runZ3RationalRoots4Protocol : Unit → IO (Array (Array Int × Int × Nat)) := fun _ => externalRoots "z3" 4 false true
setup_fixed_benchmark runZ3RationalRoots4Protocol where { observations with maxSecondsPerCall := 60, expectedHash := some (hash (expectedRoots 4 false)) }

def runFlintRationalRoots8 : Unit → IO (Array (Array Int × Int × Nat)) := fun _ => externalRoots "flint" 8 false false
setup_fixed_benchmark runFlintRationalRoots8 where { observations with maxSecondsPerCall := 60, expectedHash := some (hash (expectedRoots 8 false)) }

def runFlintRationalRoots8Protocol : Unit → IO (Array (Array Int × Int × Nat)) := fun _ => externalRoots "flint" 8 false true
setup_fixed_benchmark runFlintRationalRoots8Protocol where { observations with maxSecondsPerCall := 60, expectedHash := some (hash (expectedRoots 8 false)) }

def runZ3RationalRoots8 : Unit → IO (Array (Array Int × Int × Nat)) := fun _ => externalRoots "z3" 8 false false
setup_fixed_benchmark runZ3RationalRoots8 where { observations with maxSecondsPerCall := 60, expectedHash := some (hash (expectedRoots 8 false)) }

def runZ3RationalRoots8Protocol : Unit → IO (Array (Array Int × Int × Nat)) := fun _ => externalRoots "z3" 8 false true
setup_fixed_benchmark runZ3RationalRoots8Protocol where { observations with maxSecondsPerCall := 60, expectedHash := some (hash (expectedRoots 8 false)) }

def runFlintQuadraticRoots1 : Unit → IO (Array (Array Int × Int × Nat)) := fun _ => externalRoots "flint" 1 true false
setup_fixed_benchmark runFlintQuadraticRoots1 where { observations with maxSecondsPerCall := 60, expectedHash := some (hash (expectedRoots 1 true)) }

def runFlintQuadraticRoots1Protocol : Unit → IO (Array (Array Int × Int × Nat)) := fun _ => externalRoots "flint" 1 true true
setup_fixed_benchmark runFlintQuadraticRoots1Protocol where { observations with maxSecondsPerCall := 60, expectedHash := some (hash (expectedRoots 1 true)) }

def runZ3QuadraticRoots1 : Unit → IO (Array (Array Int × Int × Nat)) := fun _ => externalRoots "z3" 1 true false
setup_fixed_benchmark runZ3QuadraticRoots1 where { observations with maxSecondsPerCall := 60, expectedHash := some (hash (expectedRoots 1 true)) }

def runZ3QuadraticRoots1Protocol : Unit → IO (Array (Array Int × Int × Nat)) := fun _ => externalRoots "z3" 1 true true
setup_fixed_benchmark runZ3QuadraticRoots1Protocol where { observations with maxSecondsPerCall := 60, expectedHash := some (hash (expectedRoots 1 true)) }

def runFlintQuadraticRoots2 : Unit → IO (Array (Array Int × Int × Nat)) := fun _ => externalRoots "flint" 2 true false
setup_fixed_benchmark runFlintQuadraticRoots2 where { observations with maxSecondsPerCall := 60, expectedHash := some (hash (expectedRoots 2 true)) }

def runFlintQuadraticRoots2Protocol : Unit → IO (Array (Array Int × Int × Nat)) := fun _ => externalRoots "flint" 2 true true
setup_fixed_benchmark runFlintQuadraticRoots2Protocol where { observations with maxSecondsPerCall := 60, expectedHash := some (hash (expectedRoots 2 true)) }

def runZ3QuadraticRoots2 : Unit → IO (Array (Array Int × Int × Nat)) := fun _ => externalRoots "z3" 2 true false
setup_fixed_benchmark runZ3QuadraticRoots2 where { observations with maxSecondsPerCall := 60, expectedHash := some (hash (expectedRoots 2 true)) }

def runZ3QuadraticRoots2Protocol : Unit → IO (Array (Array Int × Int × Nat)) := fun _ => externalRoots "z3" 2 true true
setup_fixed_benchmark runZ3QuadraticRoots2Protocol where { observations with maxSecondsPerCall := 60, expectedHash := some (hash (expectedRoots 2 true)) }

def runFlintQuadraticRoots4 : Unit → IO (Array (Array Int × Int × Nat)) := fun _ => externalRoots "flint" 4 true false
setup_fixed_benchmark runFlintQuadraticRoots4 where { observations with maxSecondsPerCall := 60, expectedHash := some (hash (expectedRoots 4 true)) }

def runFlintQuadraticRoots4Protocol : Unit → IO (Array (Array Int × Int × Nat)) := fun _ => externalRoots "flint" 4 true true
setup_fixed_benchmark runFlintQuadraticRoots4Protocol where { observations with maxSecondsPerCall := 60, expectedHash := some (hash (expectedRoots 4 true)) }

def runZ3QuadraticRoots4 : Unit → IO (Array (Array Int × Int × Nat)) := fun _ => externalRoots "z3" 4 true false
setup_fixed_benchmark runZ3QuadraticRoots4 where { observations with maxSecondsPerCall := 60, expectedHash := some (hash (expectedRoots 4 true)) }

def runZ3QuadraticRoots4Protocol : Unit → IO (Array (Array Int × Int × Nat)) := fun _ => externalRoots "z3" 4 true true
setup_fixed_benchmark runZ3QuadraticRoots4Protocol where { observations with maxSecondsPerCall := 60, expectedHash := some (hash (expectedRoots 4 true)) }

/-- Manual larger-fixture correctness probe, including input preparation.
It is outside the fixed CI registrations and is not operation-only timing. -/
def rootProbe (degree : Nat) (quadratic : Bool) : IO UInt32 := do
  let result ← polynomialRoots degree quadratic
  unless result == expectedRoots degree quadratic do
    throw (IO.userError "larger root probe disagrees with the complete expected result")
  IO.println (Lean.Json.mkObj [("degree", Lean.toJson degree),
    ("quadratic", Lean.toJson quadratic), ("roots", Lean.toJson result)]).compress
  return 0

end Hex.RealAlgebraicBench

unsafe def main (args : List String) : IO UInt32 :=
  match args with
  | ["probe-scalar-sqrt8"] => Hex.RealAlgebraicScaling.sqrtProbe
  | ["probe-rational16"] => Hex.RealAlgebraicBench.rootProbe 16 false
  | ["probe-quadratic8"] => Hex.RealAlgebraicBench.rootProbe 8 true
  | _ => LeanBench.Cli.dispatch args
