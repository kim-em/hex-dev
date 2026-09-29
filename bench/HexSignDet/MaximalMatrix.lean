/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import HexSignDet.Maximal
import LeanBench

namespace Hex.SignDetBench.MaximalMatrix
open Hex.SignDet
open scoped Hex

/-- The complete finite moment system, with every ternary word occurring once.
Preparation uses the actual solver and validates all counts before timing.
No polynomial or Tarski-query work is included in these matrix callbacks. -/
structure Input where
  arity : Nat
  size : Nat
  system : System size

instance : Hashable Input where
  hash i := hash (i.arity, i.size, i.system.rows.toArray, i.system.columns.toArray,
    i.system.counts.toArray, i.system.values.toArray,
    matrixHash i.system.inverse, i.system.denominator)

private def build (s : Nat) : Except String Input := do
  let r := 3^s
  let es := (words [0, 1, 2] s).toArray
  let cs := (words [-1, 0, 1] s).toArray
  if es.size != r || cs.size != r then throw "wrong full-system dimensions"
  let rows : Vector (List Nat) r := Vector.ofFn fun i => es[i.val]!
  let cols : Vector (List Int) r := Vector.ofFn fun i => cs[i.val]!
  let values := moments rows cols.toList
  let .ok system := solveSystem s rows cols values | throw "full-system solve failed"
  if !system.counts.toList.all (· == 1) || !system.check s then
    throw "wrong full-support counts or inverse"
  return ⟨s, r, system⟩

/-- The zero smoke input is the one-by-one empty-word system. Failure is
retained as `none`, and scientific input inspection rejects it. -/
def input (s : Nat) : Option Input := (build s).toOption

/-- Re-run the library's rational solve, integer conversion and literal checks. -/
@[noinline] def runSolve (i : Option Input) : Option UInt64 := do
  let i ← i
  match solveSystem i.arity i.system.rows i.system.columns i.system.values with
  | .error _ => none
  | .ok system => some (hash (entries system))

/-- Check the supplied integer inverse and moment identities in their
literal row/column order, using the actual `System.check`. -/
@[noinline] def runCheck (i : Option Input) : Bool :=
  match i with
  | none => false
  | some i => i.system.check i.arity

/- Both operations execute the dense inverse identity check: r^3 integer
multiply/add pairs, including zero entries. All other checker work is
O(r^2 s): constructing entries and checking distinct columns. Gauss-Jordan
solve takes O(r^3) rational coefficient operations, and finishes with the same
r^3 integer check. Thus both are Θ(r^3)=Θ(27^s) coefficient operations.
This is not a constant-bit or general Tarski-query wall-time claim. -/

-- Declared cost-model: Θ(27^s) coefficient operations, dense exact inverse identity plus Gauss-Jordan solve.
setup_benchmark runSolve s => 27^s
  with prep := input
  where {
    paramSchedule := .custom #[1, 2, 3, 4, 5]
    paramFloor := 1
    paramCeiling := 5
    outerTrials := 6
    targetInnerNanos := 100000000
    signalFloorMultiplier := 1
    maxSecondsPerCall := 180
  }

-- Declared cost-model: Θ(27^s) integer coefficient operations, dense scaled-inverse identity check.
setup_benchmark runCheck s => 27^s
  with prep := input
  where {
    paramSchedule := .custom #[1, 2, 3, 4, 5]
    paramFloor := 1
    paramCeiling := 5
    outerTrials := 6
    targetInnerNanos := 100000000
    signalFloorMultiplier := 1
    maxSecondsPerCall := 180
  }

/-- Prepare the same full system by its literal matrix dimension. Unsupported
sizes return `none`; scientific inspection validates every scheduled input. -/
def dimensionInput (r : Nat) : Option Input := do
  let s ← #[1, 2, 3, 4, 5, 6].find? (fun s => 3^s == r)
  input s

/-- The existing complete solver, with matrix dimension as the parameter. -/
@[noinline] def runSolveDimension (i : Option Input) : Option UInt64 := runSolve i

/-- The existing literal checker, with matrix dimension as the parameter. -/
@[noinline] def runCheckDimension (i : Option Input) : Bool := runCheck i

-- Declared cost-model: Θ(r^3) coefficient operations, the same dense inverse identity plus Gauss-Jordan solve.
setup_benchmark runSolveDimension r => r^3
  with prep := dimensionInput
  where {
    paramSchedule := .custom #[3, 9, 27, 81, 243, 729]
    paramFloor := 3
    paramCeiling := 729
    outerTrials := 6
    targetInnerNanos := 100000000
    signalFloorMultiplier := 1
    maxSecondsPerCall := 180
  }

-- Declared cost-model: Θ(r^3) integer coefficient operations, the same dense scaled-inverse identity check.
setup_benchmark runCheckDimension r => r^3
  with prep := dimensionInput
  where {
    paramSchedule := .custom #[3, 9, 27, 81, 243, 729]
    paramFloor := 3
    paramCeiling := 729
    outerTrials := 6
    targetInnerNanos := 100000000
    signalFloorMultiplier := 1
    maxSecondsPerCall := 180
  }

private def bits (z : Int) : Nat := if z = 0 then 0 else z.natAbs.log2 + 1

/-- Untimed dimensions, output checks and literal witness sizes. For the
first three inputs, compare the complete system with the actual polynomial
reference producer on the existing maximal-support interpolation family. -/
private def inspectFor (arities : Array Nat) : IO UInt32 := do
  for s in arities do
    let .ok i := build s | throw (IO.userError s!"invalid maximal matrix input {s}")
    let expected := (words [-1, 0, 1] s).map fun word => (word, (1 : Int))
    unless runSolve (some i) == some (hash expected) && runCheck (some i) do
      throw (IO.userError s!"incorrect maximal matrix callback {s}")
    let mut matchesPolynomial : Option Bool := none
    if s ≤ 3 then
      let .ok p := buildMaximal s | throw (IO.userError "maximal polynomial input failed")
      let some domain := p.domain | throw (IO.userError "missing polynomial domain")
      let .ok full := referencePrepared (10377 : Nat) domain p.queries
        | throw (IO.userError "polynomial reference failed")
      -- Compare dimension-dependent systems after casting the separately
      -- constructed reference size. The check also retains exact witnesses.
      if h : full.size = i.size then
        let system : System i.size := h ▸ full.system
        unless system == i.system do throw (IO.userError "polynomial moment system differs")
        matchesPolynomial := some true
      else throw (IO.userError "polynomial matrix dimension differs")
    let inverseBits := i.system.inverse.rows.toArray.foldl (fun n row =>
      row.toArray.foldl (fun n z => max n (bits z)) n) 0
    IO.println <| (Lean.Json.mkObj [
      ("queries", Lean.toJson s), ("matrixSize", Lean.toJson i.size),
      ("supportSize", Lean.toJson i.system.counts.toList.length),
      ("countSum", Lean.toJson i.system.counts.toList.sum),
      ("inverseIdentityScalarPairs", Lean.toJson (i.size^3)),
      ("inverseBits", Lean.toJson inverseBits),
      ("denominatorBits", Lean.toJson (bits i.system.denominator)),
      ("valuesBits", Lean.toJson (i.system.values.toList.foldl (fun n z => max n (bits z)) 0)),
      ("matchesPolynomialSystem", Lean.toJson matchesPolynomial),
      ("inputHash", Lean.toJson (hash (some i)).toNat),
      ("solveResultHash", Lean.toJson (hash (some (hash expected))).toNat),
      ("checkResultHash", Lean.toJson (hash true).toNat)]).compress
    (← IO.getStdout).flush
  return 0

/-- Inspect the original query-count schedule. -/
def inspect : IO UInt32 := inspectFor #[1, 2, 3, 4, 5]

/-- Inspect every matrix-dimension input, including the 729-column system. -/
def inspectDimension : IO UInt32 := inspectFor #[1, 2, 3, 4, 5, 6]

end Hex.SignDetBench.MaximalMatrix
