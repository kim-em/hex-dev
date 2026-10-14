/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import HexRealClosure.Trivial
import LeanBench
import Lean.Data.Json

namespace Hex.RealClosure.TrivialMeasurements

inductive Family where
  | repeated | rational | quadratic
  deriving DecidableEq

private def Family.label : Family → String
  | .repeated => "repeated"
  | .rational => "rational"
  | .quadratic => "quadratic"

structure Input where
  index : Nat
  polynomial : DensePoly Rat
  canonical : RealAlgebraicPoly
  multiplicity : Nat
  family : Family
  rootCount : Nat

inductive Method where
  | generic | canonical

private def Method.label : Method → String
  | .generic => "generic"
  | .canonical => "canonical"

private def radicands : Array Nat := #[2, 3, 5, 7]

private def prepare (index : Nat) : Input :=
  if index < 6 then
    let multiplicity := if index < 2 then 0 else 2 ^ (index - 2)
    let quadratic : DensePoly Rat := DensePoly.ofCoeffs #[-2, 0, 1]
    let polynomial := if index == 0 then 0 else if index == 1 then DensePoly.C 5
      else (List.range multiplicity).foldl (fun p _ => p * quadratic) 1
    ⟨index, polynomial, Trivial.Rational.polynomial polynomial, multiplicity, .repeated,
      if index < 2 then 0 else 2⟩
  else if index < 10 then
    let count := 2 * (index - 5)
    let polynomial := (List.range count).foldl (fun p i =>
      p * DensePoly.ofCoeffs #[-((i + 1 : Nat) : Rat), 1]) 1
    ⟨index, polynomial, Trivial.Rational.polynomial polynomial, 1, .rational, count⟩
  else
    let count := 2 * (index - 9)
    let polynomial := (List.range (count / 2)).foldl (fun p i =>
      p * DensePoly.ofCoeffs #[-((radicands.getD i 0 : Nat) : Rat), 0, 1]) 1
    ⟨index, polynomial, Trivial.Rational.polynomial polynomial, 1, .quadratic, count⟩

initialize inputs : IO.Ref (Option (Array Input)) ← IO.mkRef none

def install : IO Unit := inputs.set (some ((List.range 14).toArray.map prepare))

private def getInput (index : Nat) : IO Input := do
  let some prepared ← inputs.get | throw (IO.userError "trivial inputs are not installed")
  let some input := prepared[index]? | throw (IO.userError "trivial input index is not registered")
  return input

/-- The generic route includes checked generic isolation and conversion of each
selected descriptor. The canonical arm uses the existing complete backend. -/
def roots (input : Input) : Method → RealRootSet
  | .generic => Trivial.Rational.roots 10378 input.polynomial
  | .canonical => input.canonical.roots

/-- Force the complete result, root order, exact square identities and Yun
multiplicities, retaining the zero polynomial's distinct `all` result. -/
def check (input : Input) : RealRootSet → Bool
  | .all => input.index == 0
  | .finite values =>
    if input.family == .repeated then
      if input.index == 1 then values.isEmpty
      else if input.index < 2 then false
      else match values.toList with
        | [lower, upper] =>
          lower.multiplicity == input.multiplicity && upper.multiplicity == input.multiplicity &&
          RealAlgebraicNumber.compare lower.root upper.root == .lt &&
          lower.root.sign == -1 && upper.root.sign == 1 &&
          lower.root * lower.root == RealAlgebraicNumber.ofRat 2 &&
          upper.root * upper.root == RealAlgebraicNumber.ofRat 2
        | _ => false
    else
      let entries := values.toList
      values.size == input.rootCount &&
        (entries.zip (entries.drop 1)).all (fun (a, b) =>
          RealAlgebraicNumber.compare a.root b.root == .lt) &&
        entries.zipIdx.all (fun (entry, index) =>
          entry.multiplicity == 1 &&
            if input.family == .rational then
              entry.root == RealAlgebraicNumber.ofRat ((index + 1 : Nat) : Rat)
            else
              let half := input.rootCount / 2
              let i := if index < half then half - 1 - index else index - half
              let expectedSign : Int := if index < half then -1 else 1
              entry.root.sign == expectedSign &&
                entry.root * entry.root == RealAlgebraicNumber.ofRat (radicands.getD i 0 : Rat))

/-- The timing includes complete root construction and the common exact
consumer; input construction and rational-to-canonical lifting are outside. -/
def measure (index : Nat) (method : Method) (_ : Unit) : IO UInt64 := do
  let input ← getInput index
  unless check input (roots input method) do throw (IO.userError "trivial result mismatch")
  return 1

namespace Zero

def generic := measure 0 .generic
def canonical := measure 0 .canonical
setup_fixed_benchmark generic where { expectedHash := some 1, warmupFirstIter := true, maxSecondsPerCall := 120.0 }
setup_fixed_benchmark canonical where { expectedHash := some 1, warmupFirstIter := true, maxSecondsPerCall := 120.0 }
end Zero

namespace Constant

def generic := measure 1 .generic
def canonical := measure 1 .canonical
setup_fixed_benchmark generic where { expectedHash := some 1, warmupFirstIter := true, maxSecondsPerCall := 120.0 }
setup_fixed_benchmark canonical where { expectedHash := some 1, warmupFirstIter := true, maxSecondsPerCall := 120.0 }
end Constant

namespace Multiplicity1

def generic := measure 2 .generic
def canonical := measure 2 .canonical
setup_fixed_benchmark generic where { expectedHash := some 1, warmupFirstIter := true, maxSecondsPerCall := 120.0 }
setup_fixed_benchmark canonical where { expectedHash := some 1, warmupFirstIter := true, maxSecondsPerCall := 120.0 }
end Multiplicity1

namespace Multiplicity2

def generic := measure 3 .generic
def canonical := measure 3 .canonical
setup_fixed_benchmark generic where { expectedHash := some 1, warmupFirstIter := true, maxSecondsPerCall := 120.0 }
setup_fixed_benchmark canonical where { expectedHash := some 1, warmupFirstIter := true, maxSecondsPerCall := 120.0 }
end Multiplicity2

namespace Multiplicity4

def generic := measure 4 .generic
def canonical := measure 4 .canonical
setup_fixed_benchmark generic where { expectedHash := some 1, warmupFirstIter := true, maxSecondsPerCall := 120.0 }
setup_fixed_benchmark canonical where { expectedHash := some 1, warmupFirstIter := true, maxSecondsPerCall := 120.0 }
end Multiplicity4

namespace Multiplicity8

def generic := measure 5 .generic
def canonical := measure 5 .canonical
setup_fixed_benchmark generic where { expectedHash := some 1, warmupFirstIter := true, maxSecondsPerCall := 120.0 }
setup_fixed_benchmark canonical where { expectedHash := some 1, warmupFirstIter := true, maxSecondsPerCall := 120.0 }
end Multiplicity8

/- These fixed comparisons increase distinct-root count and squarefree
input degree together. They make no asymptotic timing claim. -/
namespace Rational2

def generic := measure 6 .generic
def canonical := measure 6 .canonical
setup_fixed_benchmark generic where { expectedHash := some 1, warmupFirstIter := true, maxSecondsPerCall := 120.0 }
setup_fixed_benchmark canonical where { expectedHash := some 1, warmupFirstIter := true, maxSecondsPerCall := 120.0 }
end Rational2

namespace Rational4

def generic := measure 7 .generic
def canonical := measure 7 .canonical
setup_fixed_benchmark generic where { expectedHash := some 1, warmupFirstIter := true, maxSecondsPerCall := 120.0 }
setup_fixed_benchmark canonical where { expectedHash := some 1, warmupFirstIter := true, maxSecondsPerCall := 120.0 }
end Rational4

namespace Rational6

def generic := measure 8 .generic
def canonical := measure 8 .canonical
setup_fixed_benchmark generic where { expectedHash := some 1, warmupFirstIter := true, maxSecondsPerCall := 120.0 }
setup_fixed_benchmark canonical where { expectedHash := some 1, warmupFirstIter := true, maxSecondsPerCall := 120.0 }
end Rational6

namespace Rational8

def generic := measure 9 .generic
def canonical := measure 9 .canonical
setup_fixed_benchmark generic where { expectedHash := some 1, warmupFirstIter := true, maxSecondsPerCall := 120.0 }
setup_fixed_benchmark canonical where { expectedHash := some 1, warmupFirstIter := true, maxSecondsPerCall := 120.0 }
end Rational8

namespace Quadratic2

def generic := measure 10 .generic
def canonical := measure 10 .canonical
setup_fixed_benchmark generic where { expectedHash := some 1, warmupFirstIter := true, maxSecondsPerCall := 120.0 }
setup_fixed_benchmark canonical where { expectedHash := some 1, warmupFirstIter := true, maxSecondsPerCall := 120.0 }
end Quadratic2

namespace Quadratic4

def generic := measure 11 .generic
def canonical := measure 11 .canonical
setup_fixed_benchmark generic where { expectedHash := some 1, warmupFirstIter := true, maxSecondsPerCall := 120.0 }
setup_fixed_benchmark canonical where { expectedHash := some 1, warmupFirstIter := true, maxSecondsPerCall := 120.0 }
end Quadratic4

namespace Quadratic6

def generic := measure 12 .generic
def canonical := measure 12 .canonical
setup_fixed_benchmark generic where { expectedHash := some 1, warmupFirstIter := true, maxSecondsPerCall := 120.0 }
setup_fixed_benchmark canonical where { expectedHash := some 1, warmupFirstIter := true, maxSecondsPerCall := 120.0 }
end Quadratic6

namespace Quadratic8

def generic := measure 13 .generic
def canonical := measure 13 .canonical
setup_fixed_benchmark generic where { expectedHash := some 1, warmupFirstIter := true, maxSecondsPerCall := 120.0 }
setup_fixed_benchmark canonical where { expectedHash := some 1, warmupFirstIter := true, maxSecondsPerCall := 120.0 }
end Quadratic8

private def rat (value : Rat) : Lean.Json := Lean.toJson [value.num, (value.den : Int)]

/-- Serialize exact rational inputs and canonical root presentations separately
from timing. The independent oracle verifies exact roots and multiplicities. -/
def emit (start count : Nat) : IO Unit := do
  for offset in List.range count do
    let index := start + offset
    let input ← getInput index
    let sourceCounts := if index < 6 then (0, 0) else
      match Roots.roots Sturm.orderSign (10378 : Nat) input.polynomial with
      | .all => (0, 0)
      | .finite entries => entries.foldl (fun (points, selected) entry =>
        match entry.root with
        | .point _ => (points + 1, selected)
        | .selected _ => (points, selected + 1)) (0, 0)
    for method in [Method.generic, .canonical] do
      let result := roots input method
      unless check input result do throw (IO.userError "trivial functional result mismatch")
      let output := match result with
        | .all => Lean.Json.null
        | .finite values => Lean.Json.arr (values.map fun value =>
          let square := value.root.toAlgebraic.rep.1.square
          Lean.Json.mkObj [
            ("polynomial", Lean.toJson value.root.toAlgebraic.p.toArray),
            ("re", rat square.re.toRat), ("im", rat square.im.toRat),
            ("precision", Lean.toJson square.prec),
            ("sign", Lean.toJson value.root.sign),
            ("multiplicity", Lean.toJson value.multiplicity)])
      let fields := [
        ("index", Lean.toJson index), ("method", Lean.toJson method.label),
        ("coefficients", Lean.Json.arr (input.polynomial.toArray.map rat)),
        ("multiplicity", Lean.toJson input.multiplicity), ("roots", output)]
      let fields := if input.family == .repeated then fields else fields ++ [
        ("family", Lean.toJson input.family.label), ("root_count", Lean.toJson input.rootCount),
        ("generic_points", Lean.toJson sourceCounts.1),
        ("generic_selected", Lean.toJson sourceCounts.2)]
      IO.println <| (Lean.Json.mkObj fields).compress

/-- Untimed inventory of the actual native descriptors. Eligible pairs count
all unordered descriptor pairs, not the comparisons taken by the sorter. -/
def emitSelection : IO Unit := do
  for offset in List.range 8 do
    let index := offset + 6
    let input ← getInput index
    let .finite entries := Roots.roots Sturm.orderSign (10378 : Nat) input.polynomial
      | throw (IO.userError "distinct input returned all roots")
    unless entries.length == input.rootCount do
      throw (IO.userError "native selection inventory lost a root")
    let selected := entries.filterMap fun entry => match entry.root with
      | .point _ => none
      | .selected descriptor => some descriptor
    let full := fun (descriptor : SignDet.Descriptor Rat Nat Sturm.orderSign 10378) =>
      descriptor.raw.indices == (List.range descriptor.raw.head.natDegree).map (· + 1)
    let eligible := selected.zipIdx.foldl (fun count (descriptor, i) =>
      count + ((selected.drop (i + 1)).filter fun other =>
        (descriptor.fullOrder other).isSome).length) 0
    IO.println <| (Lean.Json.mkObj [
      ("index", Lean.toJson index), ("family", Lean.toJson input.family.label),
      ("degree", Lean.toJson input.polynomial.natDegree),
      ("points", Lean.toJson (entries.length - selected.length)),
      ("selected", Lean.toJson selected.length),
      ("full", Lean.toJson (selected.filter full).length),
      ("eligible_pairs", Lean.toJson eligible),
      ("all_selected_pairs", Lean.toJson (selected.length * (selected.length - 1) / 2)),
      ("descriptors", Lean.toJson (selected.map fun descriptor => Lean.Json.mkObj [
        ("head", Lean.Json.arr (descriptor.raw.head.toArray.map rat)),
        ("indices", Lean.toJson descriptor.raw.indices),
        ("signs", Lean.toJson descriptor.raw.signs)]))]).compress

private abbrev IndexedEntry := Roots.Entry (E := Rat) Sturm.orderSign (10378 : Nat) × Nat

private def comparisonRoute (left right : Isolation.Root (E := Rat) Sturm.orderSign (10378 : Nat)) :
    String :=
  match left, right with
  | .point _, .point _ => "points"
  | .selected a, .selected b =>
    if a.raw.head.size = 2 ∧ a.raw.head.leadingCoeff = 1 ∧
        b.raw.head.size = 2 ∧ b.raw.head.leadingCoeff = 1 then "linear"
    else if (a.fullOrder b).isSome then "full"
    else if (Isolation.Root.intervalOrder? a b).isSome then "interval"
    else "common-product"
  | _, _ => "mixed"

/-- Untimed insertion replay calls the actual comparator on the actual assembly
entries. Original indices let the caller check its entire output against the
production sorter without comparing proof fields. -/
private def traceInsert (root : IndexedEntry) : List IndexedEntry →
    Except SignDet.BuildError (List IndexedEntry × List Lean.Json)
  | [] => .ok ([root], [])
  | first :: rest => do
    let order ← root.1.root.compare first.1.root
    let event := Lean.Json.mkObj [
      ("left", Lean.toJson root.2), ("right", Lean.toJson first.2),
      ("route", Lean.toJson (comparisonRoute root.1.root first.1.root)),
      ("order", Lean.toJson (match order with | .lt => "lt" | .eq => "eq" | .gt => "gt"))]
    match order with
    | .lt => return (root :: first :: rest, [event])
    | .eq => .error .system
    | .gt =>
      let (result, events) ← traceInsert root rest
      return (first :: result, event :: events)

private def traceSort : List IndexedEntry →
    Except SignDet.BuildError (List IndexedEntry × List Lean.Json)
  | [] => .ok ([], [])
  | root :: rest => do
    let (sorted, earlier) ← traceSort rest
    let (result, later) ← traceInsert root sorted
    return (result, earlier ++ later)

private def endpointJson : Endpoint Rat → Lean.Json
  | .negInf => .str "negInf"
  | .posInf => .str "posInf"
  | .finite value => Lean.Json.mkObj [("finite", rat value)]

private def entryJson (entry : IndexedEntry) : Lean.Json :=
  Lean.Json.mkObj [("index", Lean.toJson entry.2),
    ("root", match entry.1.root with
      | .point value => Lean.Json.mkObj [("point", rat value)]
      | .selected descriptor => Lean.Json.mkObj [
        ("head", Lean.Json.arr (descriptor.raw.head.toArray.map rat)),
        ("lower", endpointJson descriptor.raw.lower),
        ("upper", endpointJson descriptor.raw.upper),
        ("indices", Lean.toJson descriptor.raw.indices),
        ("signs", Lean.toJson descriptor.raw.signs)])]

/-- Replay the outer entry sort from its actual unsorted assembly input, then
check every output index against `Root.sortBy`. This is a later untimed
diagnostic, separate from the frozen paired executables. -/
def emitSort : IO Unit := do
  for offset in List.range 8 do
    let input ← getInput (offset + 6)
    let .ok (.finite assembled) := Roots.assemble Sturm.orderSign (10378 : Nat) input.polynomial
      | throw (IO.userError "sort inventory assembly failed")
    let indexed := assembled.zipIdx
    let .ok (replayed, events) := traceSort indexed
      | throw (IO.userError "sort inventory replay failed")
    let .ok actual := Isolation.Root.sortBy (fun entry : IndexedEntry => entry.1.root) indexed
      | throw (IO.userError "sort inventory actual sort failed")
    unless replayed.map Prod.snd == actual.map Prod.snd do
      throw (IO.userError "sort inventory replay differs from production")
    IO.println <| (Lean.Json.mkObj [
      ("comparison_schema", Lean.toJson (2 : Nat)),
      ("index", Lean.toJson input.index), ("family", Lean.toJson input.family.label),
      ("degree", Lean.toJson input.polynomial.natDegree),
      ("assembled", Lean.toJson (indexed.map entryJson)),
      ("sorted_indices", Lean.toJson (actual.map Prod.snd)),
      ("comparisons", Lean.toJson events)]).compress

end Hex.RealClosure.TrivialMeasurements

def main (args : List String) : IO UInt32 := do
  Hex.RealClosure.TrivialMeasurements.install
  if args.isEmpty || args == ["emit"] then
    Hex.RealClosure.TrivialMeasurements.emit 0 6
    return 0
  if args == ["emit-distinct"] then
    Hex.RealClosure.TrivialMeasurements.emit 6 8
    return 0
  if args == ["emit-selection"] then
    Hex.RealClosure.TrivialMeasurements.emitSelection
    return 0
  if args == ["emit-sort"] then
    Hex.RealClosure.TrivialMeasurements.emitSort
    return 0
  LeanBench.Cli.dispatch args
