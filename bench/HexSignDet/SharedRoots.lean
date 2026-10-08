/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexSignDet.Small
public import HexSignDet.Height
public import LeanBench

public section

namespace Hex.SignDetBench.SharedRoots
open Hex.SignDet

abbrev Root := Descriptor Rat Nat Sturm.orderSign 10377

/-- Both comparisons retain their actual common products and re-encodings. -/
structure Case where
  left : Root
  same : Root
  last : Root
  equal : Comparison left same
  strict : Comparison left last

@[noinline, never_extract] private def select (p : DensePoly Rat) (lo hi : Rat) : Option Root := do
  let raw : RawDescriptor Rat Nat := ⟨10377, p, .finite lo, .finite hi, [], []⟩
  let .ok (.ok d) := Descriptor.build Sturm.orderSign 10377 raw | none
  return d

/-- P=X²−2; Q=P times the distinct factors X−3,...,X−(n+2).
The interval (0,2) selects sqrt(2) in both heads. The half-integer interval
around n+2 selects Q's largest root and has no root at either endpoint. -/
@[noinline, never_extract] def input (n : Nat) : Option Case := do
  if n < 1 || n > 3 then none else do
    let x : DensePoly Rat := DensePoly.ofCoeffs #[0, 1]
    let p := x * x - DensePoly.C 2
    let q := (List.range n).foldl (fun q (k : Nat) => q * (x - DensePoly.C ((k : Rat) + 3))) p
    let left ← select p 0 2
    let same ← select q 0 2
    let last ← select q ((n : Rat) + 3/2) ((n : Rat) + 5/2)
    let .ok equal := left.buildComparison same | none
    let .ok strict := left.buildComparison last | none
    if equal.order != .eq || strict.order != .lt ||
        equal.common.factor.natDegree != 2 || strict.common.factor.natDegree != 2 ||
        equal.common.head.natDegree != n+2 || strict.common.head.natDegree != n+2 then none
    else return ⟨left, same, last, equal, strict⟩

private def result (i : Case) : UInt64 :=
  hash (polyHash i.left.raw.head, polyHash i.same.raw.head,
    polyHash i.equal.common.head, polyHash i.strict.common.head,
    i.equal.leftEncoding.target.raw.signs, i.equal.rightEncoding.target.raw.signs,
    i.strict.leftEncoding.target.raw.signs, i.strict.rightEncoding.target.raw.signs)

/-- End-to-end examples include descriptor validation, both common-product
constructions, joint tables and all checking performed by the public APIs. -/
@[noinline, never_extract] def run (n : Nat) : Option UInt64 := result <$> input n

-- Keep closed fixed calls inside the measured loop rather than cached values.
@[noinline, never_extract] def runOne : Unit → Option UInt64 := fun () => run 1
@[noinline, never_extract] def runTwo : Unit → Option UInt64 := fun () => run 2
@[noinline, never_extract] def runThree : Unit → Option UInt64 := fun () => run 3

-- Fixed examples: degrees three, four and five. No asymptotic timing law.
setup_fixed_benchmark runOne where { repeats := 6, minTotalSeconds := 0.1, maxSecondsPerCall := 10 }
setup_fixed_benchmark runTwo where { repeats := 6, minTotalSeconds := 0.1, maxSecondsPerCall := 10 }
setup_fixed_benchmark runThree where { repeats := 6, minTotalSeconds := 0.1, maxSecondsPerCall := 10 }

private def polynomial (p : DensePoly Rat) : Lean.Json := Lean.toJson <|
  p.toArray.toList.map fun c => (c.num, c.den)

/-- Literal polynomial/gcd inventory, finite endpoints and both known orders.
The polynomial gcd count concerns CommonProduct.build alone, not internal
query preparation or rational normalization. -/
def inspect : IO UInt32 := do
  for n in #[1, 2, 3] do
    let some i := input n | throw (IO.userError s!"shared-root case failed at {n}")
    let ts := [i.equal.leftEncoding.evidence, i.equal.rightEncoding.evidence,
      i.strict.leftEncoding.evidence, i.strict.rightEncoding.evidence]
    let queryCounts := ts.map fun t => (nodes t).foldl (fun k node => k + node.size) 0
    let widths := ts.map fun t => (nodes t).foldl (fun k node => max k node.size) 0
    IO.println <| (Lean.Json.mkObj [
      ("extraFactors", Lean.toJson n), ("left", polynomial i.left.raw.head),
      ("right", polynomial i.same.raw.head), ("factor", polynomial i.equal.common.factor),
      ("commonHead", polynomial i.equal.common.head),
      ("equalOrder", Lean.toJson "eq"), ("strictOrder", Lean.toJson "lt"),
      ("sourceInterval", Lean.toJson ([0, 2] : List Int)),
      ("lastIntervalTwice", Lean.toJson ([2*n+3, 2*n+5] : List Nat)),
      ("commonProductGcdCalls", Lean.toJson (2 : Nat)),
      ("jointMomentCounts", Lean.toJson queryCounts), ("maxMatrixWidths", Lean.toJson widths),
      ("resultHash", Lean.toJson (hash (some (result i))).toNat)]).compress
  return 0

private def bitLength (z : Int) : Nat := if z == 0 then 0 else z.natAbs.log2 + 1
private def coefficientBits (p : DensePoly Rat) : Nat := p.toArray.foldl (fun b q =>
  max b (max (bitLength q.num) (q.den.log2 + 1))) 0
private def orderLabel : Ordering → String
  | .lt => "lt" | .eq => "eq" | .gt => "gt"
private def interval (d : Root) : Lean.Json :=
  match d.raw.lower, d.raw.upper with
  | .finite lo, .finite hi => Lean.toJson ((lo.num, lo.den), (hi.num, hi.den))
  | _, _ => .null

/-- All eleven table constructions in the callback: three initial descriptors,
four target validations, and four joint re-encodings. Counts describe literal
work returned by those actual constructors, not instrumented arithmetic calls. -/
def inspectWork : IO UInt32 := do
  for n in #[1, 2, 3] do
    let some i := input n | throw (IO.userError s!"shared-root case failed at {n}")
    let ts := [i.left.evidence, i.same.evidence, i.last.evidence,
      i.equal.leftEncoding.target.evidence, i.equal.rightEncoding.target.evidence,
      i.strict.leftEncoding.target.evidence, i.strict.rightEncoding.target.evidence,
      i.equal.leftEncoding.evidence, i.equal.rightEncoding.evidence,
      i.strict.leftEncoding.evidence, i.strict.rightEncoding.evidence]
    let queryCounts := ts.map fun t => (nodes t).foldl (fun k node => k + node.size) 0
    let literalBits := ts.foldl (fun b t => max b <| max (Height.witnessBits t)
      ((nodes t).foldl (fun b node =>
        node.queries.foldl (fun b q => max b (coefficientBits q))
          (max b (coefficientBits node.head))) 0)) 0
    IO.println <| (Lean.Json.mkObj [
      ("extraFactors", Lean.toJson n), ("left", polynomial i.left.raw.head),
      ("right", polynomial i.same.raw.head), ("lastHead", polynomial i.last.raw.head),
      ("factor", polynomial i.equal.common.factor),
      ("commonHead", polynomial i.equal.common.head),
      ("strictFactor", polynomial i.strict.common.factor),
      ("strictCommonHead", polynomial i.strict.common.head),
      ("equalOrder", Lean.toJson (orderLabel i.equal.order)),
      ("strictOrder", Lean.toJson (orderLabel i.strict.order)),
      ("leftInterval", interval i.left), ("sameInterval", interval i.same),
      ("lastInterval", interval i.last),
      ("tableLabels", Lean.toJson (["source-left", "source-same", "source-last",
        "target-equal-left", "target-equal-right", "target-strict-left", "target-strict-right",
        "joint-equal-left", "joint-equal-right", "joint-strict-left", "joint-strict-right"] : List String)),
      ("tableMomentCounts", Lean.toJson queryCounts),
      ("totalTableMoments", Lean.toJson queryCounts.sum),
      ("maxTableCoefficientBits", Lean.toJson literalBits),
      ("resultHash", Lean.toJson (hash (some (result i))).toNat)]).compress
  return 0

end Hex.SignDetBench.SharedRoots
