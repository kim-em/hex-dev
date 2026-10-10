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
Reference checks use the actual solver and validate all counts; their tiny
preparation is included in the fixed callback. Tensor checker preparation
happens before timing.
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
r^3 integer check. This gives a cubic total scalar-operation count, but the
structured reference solve mixes zero-skipping rational elimination with
cheap integer checks. That count does not supply a useful wall-time model
on its small-input comparison domain. Production uses rational inversion
only at leaves of size at most three; parents use their child tensor inverses.
Keep reference solves as small fixed checks. The production-relevant integer
checker retains its independently derived cubic scaling registration, `runTensorCheck`.
The earlier checker registrations are superseded by that same callback with
tensor preparation; their archived verdicts and finite-range disposition
are retained in reports/sign-det-matrix-wide.md. -/

/- Fixed reference checks include their tiny preparation. Keeping it inside
these callbacks avoids running reference solves at every executable startup. -/
@[noinline] private def referenceAt (s : Nat) (_ : Unit) : IO (Option UInt64) :=
  return runSolve (input s)

def reference1 := referenceAt 1
def reference2 := referenceAt 2
def reference3 := referenceAt 3

private def referenceConfig (s : Nat) : LeanBench.FixedBenchmarkConfig :=
  let expected := (words [-1, 0, 1] s).map fun word => (word, (1 : Int))
  { repeats := 2, maxSecondsPerCall := 10, minTotalSeconds := 0.01,
    expectedHash := some (hash (some (hash expected))) }

setup_fixed_benchmark reference1 where referenceConfig 1
setup_fixed_benchmark reference2 where referenceConfig 2
setup_fixed_benchmark reference3 where referenceConfig 3

/-- Prepare the same complete system with the library's existing Kronecker
product. Only preparation changes: the measured callback remains System.check.
The small-input inspection compares every literal with the ordinary solver. -/
def tensorInput : Nat → Option Input
  | 0 => input 0
  | s + 1 => do
    let left ← tensorInput s
    let right ← input 1
    let rows := productVector left.system.rows right.system.rows
    let columns := productVector left.system.columns right.system.columns
    let system : System (left.size * right.size) := {
      rows := rows
      columns := columns
      counts := Vector.replicate _ 1
      values := moments rows columns.toList
      inverse := tensor left.system.inverse right.system.inverse
      denominator := left.system.denominator * right.system.denominator }
    return ⟨s + 1, left.size * right.size, system⟩

def wideDimensions : Array Nat := #[243, 729, 2187, 6561]

def tensorDimensionInput (r : Nat) : Option Input := do
  let s ← #[0, 1, 2, 3, 4, 5, 6, 7, 8].find? (fun s => 3^s == r)
  tensorInput s

@[noinline] def runTensorCheck (i : Option Input) : Bool := runCheck i

-- Declared cost-model: Θ(r^3), the unchanged dense exact integer inverse check.
-- Tensor preparation allows a wider range without timing rational inversion.
setup_benchmark runTensorCheck r => r^3
  with prep := tensorDimensionInput
  where {
    paramSchedule := .custom wideDimensions
    paramFloor := 243
    paramCeiling := 6561
    outerTrials := 6
    targetInnerNanos := 100000000
    signalFloorMultiplier := 1
    maxSecondsPerCall := 3600
  }

/-- Compare complete witnesses, moments and literal orders with the existing
solver on the overlap. Includes the empty-word one-by-one system. -/
def inspectTensorsFor (arities : Array Nat) : IO UInt32 := do
  for s in arities do
    let some prepared := tensorInput s | throw (IO.userError "tensor preparation failed")
    let some original := input s | throw (IO.userError "ordinary preparation failed")
    if h : prepared.size = original.size then
      let system : System original.size := h ▸ prepared.system
      unless system == original.system && runCheck (some prepared) do
        throw (IO.userError s!"tensor witness differs from ordinary solve at {s}")
    else throw (IO.userError "tensor matrix dimension differs")
    IO.println s!"tensor matrix {prepared.size}: complete witness matches ordinary solve"
    (← IO.getStdout).flush
  return 0

def inspectTensors : IO UInt32 := inspectTensorsFor #[0, 1, 2, 3, 4, 5, 6]

private def bits (z : Int) : Nat := if z = 0 then 0 else z.natAbs.log2 + 1

/-- Inspect complete literal row/column orders, the closed finite-observation
moments and both exact identities before collecting the wider checker ladder. -/
def inspectWideChecks (arities : Array Nat := #[5, 6, 7, 8]) : IO UInt32 := do
  for s in arities do
    let some i := tensorInput s | throw (IO.userError "tensor preparation failed")
    let exponents := words [0, 1, 2] s
    let columns := words [-1, 0, 1] s
    let expected := exponents.map fun word =>
      (word.map fun k => if k == 0 then (3 : Int) else if k == 1 then 0 else 2).foldr (· * ·) 1
    unless i.size == 3^s && i.system.rows.toList == exponents &&
        i.system.columns.toList == columns && i.system.counts.toList.all (· == 1) &&
        i.system.values.toList == expected && i.system.denominator == (2^s : Nat) do
      throw (IO.userError "tensor subject or moments differ from the finite full-support oracle")
    let checked := runCheck (some i)
    unless checked do throw (IO.userError "tensor inverse or moment identities rejected")
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
      ("literalOrders", Lean.toJson true), ("finiteMoments", Lean.toJson true),
      ("inputHash", Lean.toJson (hash (some i)).toNat),
      ("checkResultHash", Lean.toJson (hash checked).toNat)]).compress
    (← IO.getStdout).flush
  return 0

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
