/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import HexRealAlgebraic
import LeanBench
import Hex.BenchOracle.Flint

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

-- Mode 1: the same mergeSort/comparator expression used by realRoots.
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

-- Diagnostic control: the array parameter does not drive the leaf operations.
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

end Hex.RealAlgebraicBench

unsafe def main (args : List String) : IO UInt32 := LeanBench.Cli.dispatch args
