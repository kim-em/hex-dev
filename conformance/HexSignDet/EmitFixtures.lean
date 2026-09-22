/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import HexSignDet
import HexSignDet.Compare
import Hex.Conformance.Emit
import HexRealAlgebraic.Roots
import HexPolyZ.IntegerPolynomial
import Lean.Data.Json

/-! Rational BKR fixtures with independent real-algebraic root evaluation.
This consumer-only import of `HexRealAlgebraic` creates no library dependency
from sign determination back to the rational real-algebraic implementation. -/
namespace Hex.SignDet.Emit

open Lean

private def rat (q : Rat) : Json := toJson #[q.num, (q.den : Int)]

private def poly (p : DensePoly Rat) : Json := Json.arr (p.toArray.map rat)

private def endpoint : Endpoint Rat → Json
  | .negInf => toJson "-inf"
  | .posInf => toJson "+inf"
  | .finite q => rat q

private def row (signs : List Int) (count : Nat) : Json :=
  Json.mkObj [("signs", toJson signs), ("count", toJson count)]

private def table {r : Nat} (s : System r) : Json :=
  toJson (s.positive.map fun i => row s.columns[i] s.counts[i].toNat)

private def result (t : Json) (replay : Bool) : Json :=
  Json.mkObj [("status", toJson "ok"), ("table", t), ("replay", toJson replay)]

private def failure (error : BuildError) : Json :=
  Json.mkObj [("status", toJson "error"), ("error", toJson (reprStr error))]

private def produced (domain : Sturm.PreparedDomain Rat) (qs : List (DensePoly Rat))
    (reduced : Bool) : Json :=
  match buildPrepared (10377 : Nat) domain qs reduced with
  | .error error => failure error
  | .ok t => result (table t.val.node.system)
    (t.val.check Sturm.orderSign 10377 domain.head domain.lower domain.upper qs)

private def reference (domain : Sturm.PreparedDomain Rat) (qs : List (DensePoly Rat)) : Json :=
  match referencePrepared (10377 : Nat) domain qs with
  | .error error => failure error
  | .ok n => result (table n.system)
    (n.check Sturm.orderSign 10377 domain.head domain.lower domain.upper qs)

private def inside (lower upper : Endpoint Rat) (root : RealAlgebraicNumber) : Bool :=
  (match lower with
   | .negInf => true
   | .posInf => false
   | .finite q => decide (RealAlgebraicNumber.ofRat q < root)) &&
  (match upper with
   | .posInf => true
   | .negInf => false
   | .finite q => decide (root < RealAlgebraicNumber.ofRat q))

/-- Independent existing real-algebraic root enumeration and Horner evaluation;
no BKR rows, moments, counts or proposed support enter this computation. -/
private def algebraicTable (p : DensePoly Rat) (qs : List (DensePoly Rat))
    (lower upper : Endpoint Rat) : Json :=
  let roots := (ZPoly.clearDenominators p).2.realAlgebraicRoots
  let words := (roots.filter (inside lower upper)).toList.map fun root =>
    qs.map fun q =>
      let value := q.toArray.toList.reverse.foldl
        (fun acc c => acc * root + RealAlgebraicNumber.ofRat c) 0
      value.sign
  let support := words.eraseDups.mergeSort (fun a b => compare a b != .gt)
  toJson (support.map fun signs => row signs (words.count signs))

private def emit (case : String) (p : DensePoly Rat) (qs : List (DensePoly Rat))
    (lower : Endpoint Rat := .negInf) (upper : Endpoint Rat := .posInf) : IO Unit := do
  let input := [("schema", toJson (1 : Nat)), ("seed", toJson (10377 : Nat)),
    ("head", poly p), ("queries", toJson (qs.map poly)),
    ("lower", endpoint lower), ("upper", endpoint upper)]
  let fields := match Sturm.prepare Sturm.orderSign p lower upper with
    | none =>
      let invalid := Json.mkObj [("status", toJson "invalid-domain")]
      [("reduced", invalid), ("direct", invalid), ("reference", invalid), ("algebraic", Json.null)]
    | some domain =>
      [("reduced", produced domain qs true), ("direct", produced domain qs false),
        ("algebraic", algebraicTable p qs lower upper)] ++
        (if qs.length ≤ 4 then [("reference", reference domain qs)] else [])
  Hex.Conformance.Emit.emitResult "HexSignDet" case "table" (Json.mkObj (input ++ fields)).compress

private def descriptorResult (raw : RawDescriptor Rat Nat) (qs : List (DensePoly Rat)) : Json :=
  match Descriptor.build Sturm.orderSign 10377 raw with
  | .error err => failure err
  | .ok (.error reason) => Json.mkObj [("status", toJson "invalid-descriptor"),
      ("reason", toJson (match reason with
        | .context => "context" | .malformed => "malformed" | .domain => "domain"
        | .absent => "absent" | .ambiguous => "ambiguous"))]
  | .ok (.ok d) =>
    let completion := match d.buildCompletion with
      | .error err => failure err
      | .ok c => Json.mkObj [("status", toJson "ok"), ("indices", toJson c.descriptor.raw.indices),
          ("signs", toJson c.descriptor.raw.signs),
          ("replay", toJson (c.descriptor.raw.check Sturm.orderSign 10377 c.descriptor.evidence)),
          ("bindings", toJson (d.raw.completes c.descriptor.raw))]
    let selected := match d.buildSigns qs with
      | .error err => failure err
      | .ok s => Json.mkObj [("status", toJson "ok"), ("signs", toJson s.values.toList),
          ("replay", toJson (d.checkSigns qs s.values s.evidence))]
    Json.mkObj [("status", toJson "ok"), ("replay", toJson (raw.check Sturm.orderSign 10377 d.evidence)),
      ("completion", completion), ("selected", selected)]

private def rootsResult (raw : RawDescriptor Rat Nat) : Json :=
  match Descriptor.buildRoots Sturm.orderSign 10377 raw.head raw.lower raw.upper with
  | .error err => failure err
  | .ok none => Json.mkObj [("status", toJson "invalid-domain")]
  | .ok (some roots) => Json.mkObj [("status", toJson "ok"), ("roots", toJson (roots.map fun d =>
      Json.mkObj [("indices", toJson d.raw.indices), ("signs", toJson d.raw.signs),
        ("replay", toJson (d.raw.check Sturm.orderSign 10377 d.evidence))]))]

private def emitDescriptor (name : String) (raw : RawDescriptor Rat Nat)
    (qs : List (DensePoly Rat)) : IO Unit :=
  Hex.Conformance.Emit.emitResult "HexSignDet" ("descriptor/" ++ name) "descriptor"
    (Json.mkObj [("schema", toJson (1 : Nat)), ("head", poly raw.head),
      ("lower", endpoint raw.lower), ("upper", endpoint raw.upper),
      ("context", toJson raw.context), ("indices", toJson raw.indices), ("signs", toJson raw.signs),
      ("queries", toJson (qs.map poly)), ("validation", descriptorResult raw qs),
      ("roots", rootsResult raw)]).compress

private def rawJson (raw : RawDescriptor Rat Nat) : Json :=
  Json.mkObj [("head", poly raw.head), ("lower", endpoint raw.lower), ("upper", endpoint raw.upper),
    ("context", toJson raw.context), ("indices", toJson raw.indices), ("signs", toJson raw.signs)]

private def emitComparison (name : String) (left right : RawDescriptor Rat Nat) : IO Unit := do
  let output := match Descriptor.build Sturm.orderSign 10377 left,
      Descriptor.build Sturm.orderSign 10377 right with
    | .ok (.ok l), .ok (.ok r) => match l.buildComparison r with
      | .error err => failure err
      | .ok c => Json.mkObj [("status", toJson "ok"), ("commonHead", poly c.common.head),
          ("order", toJson (match c.order with | .lt => "lt" | .eq => "eq" | .gt => "gt")),
          ("leftSigns", toJson c.leftEncoding.target.raw.signs),
          ("rightSigns", toJson c.rightEncoding.target.raw.signs),
          ("commonReplay", toJson (c.common.check 10377 left.head right.head)),
          ("leftReplay", toJson (l.checkReencoding c.leftEncoding.target c.common.head
            .negInf .posInf c.leftEncoding.evidence)),
          ("rightReplay", toJson (r.checkReencoding c.rightEncoding.target c.common.head
            .negInf .posInf c.rightEncoding.evidence))]
    | _, _ => Json.mkObj [("status", toJson "invalid-input")]
  Hex.Conformance.Emit.emitResult "HexSignDet" ("compare/" ++ name) "compare"
    (Json.mkObj [("schema", toJson (1 : Nat)), ("left", rawJson left),
      ("right", rawJson right), ("result", output)]).compress

private def emitReencoding (name : String) (raw : RawDescriptor Rat Nat)
    (head : DensePoly Rat) (a b : Endpoint Rat) : IO Unit := do
  let output := match Descriptor.build Sturm.orderSign 10377 raw with
    | .ok (.ok d) => match d.buildReencoding head a b with
      | .error err => failure err
      | .ok none => Json.mkObj [("status", toJson "none")]
      | .ok (some r) => Json.mkObj [("status", toJson "ok"),
          ("signs", toJson r.target.raw.signs), ("indices", toJson r.target.raw.indices),
          ("replay", toJson (d.checkReencoding r.target head a b r.evidence))]
    | _ => Json.mkObj [("status", toJson "invalid-input")]
  Hex.Conformance.Emit.emitResult "HexSignDet" ("reencode/" ++ name) "reencode"
    (Json.mkObj [("schema", toJson (1 : Nat)), ("source", rawJson raw),
      ("head", poly head), ("lower", endpoint a), ("upper", endpoint b),
      ("result", output)]).compress

private def x : DensePoly Rat := DensePoly.ofCoeffs #[0, 1]

def run : IO Unit := do
  let p := x * x - 1
  emit "two-roots" p [x, x - 1]
  emit "negative-head" (-p) [x, x - 1]
  emit "empty-queries" p []
  emit "zero-root" x [x, 0]
  emit "duplicate-zero-constant" p [0, 1, x, x]
  emit "irrational-common-factor" (x * x - 2) [x, x * x - 2, x * x - 3, x - 1]
  emit "cubic-derivatives" (x.natPow 3 - x) [3 * x * x - 1, 6 * x, 6]
  emit "negative-cubic-derivatives" (x - x.natPow 3) [1 - 3 * x * x, -6 * x, -6]
  emit "high-degree-queries" p [x.natPow 7 + 1, x.natPow 6 - 1]
  emit "rational-scaling" (DensePoly.scale (1 / 6) p) [DensePoly.scale (-1 / 10) x]
  emit "finite-interval" (x.natPow 3 - x) [x] (.finite (-1 / 2)) (.finite (1 / 2))
  emit "left-half-line" p [x] .negInf (.finite 0)
  emit "right-half-line" p [x] (.finite 0) .posInf
  emit "many-queries" (x.natPow 3 - x) (List.replicate 12 x)
  for (name, head) in [("constant", (3 : DensePoly Rat)), ("negative-constant", -2),
      ("root-free", x * x + 1)] do
    emit (name ++ "/empty") head []
    emit (name ++ "/queries") head [x, 0]
  for (name, head) in [("zero-head", (0 : DensePoly Rat)), ("repeated-head", p * p),
      ("cancelled-head", p - p)] do
    emit (name ++ "/empty") head []
    emit (name ++ "/queries") head [x]
  for (i, (lower, upper)) in ([(.negInf, .negInf), (.posInf, .posInf), (.posInf, .negInf),
      (.finite 0, .negInf), (.posInf, .finite 0), (.finite 0, .finite 0),
      (.finite 2, .finite (-2)), (.finite (-1), .posInf), (.negInf, .finite 1)] :
      List (Endpoint Rat × Endpoint Rat)).zipIdx.map (fun (pair, i) => (i, pair)) do
    emit s!"invalid-interval/{i}" p [] lower upper
  -- Fixed seed and generator; all generated inputs are emitted in full.
  let mut state := 10377
  for i in List.range 24 do
    state := (1664525 * state + 1013904223) % 4294967296
    let a : Rat := (state % 17 : Nat) - 8
    state := (1664525 * state + 1013904223) % 4294967296
    let b : Rat := (state % 19 : Nat) - 9
    let head := (x * x - 2) * (x - DensePoly.C ((i + 2 : Nat) : Rat))
    emit s!"seed-10377/{i}" head [x + DensePoly.C a, x * x + DensePoly.C b, head]

  let raw : RawDescriptor Rat Nat := ⟨10377, p, .negInf, .posInf, [1], [-1]⟩
  let queries := [x, p, x + 1, x - 1, 0, 7]
  emitDescriptor "negative-root" raw queries
  emitDescriptor "positive-root" {raw with signs := [1]} queries
  emitDescriptor "empty-queries" raw []
  emitDescriptor "permuted-slots" {raw with indices := [2, 1], signs := [1, -1]} queries
  emitDescriptor "singleton-empty" {raw with indices := [], signs := [], lower := .finite 0} queries
  emitDescriptor "negative-head" {raw with head := -p, signs := [1]} queries
  emitDescriptor "irrational" {raw with head := x * x - 2, signs := [1]}
    [x * x - 2, x * x - 3, x, x - 1]
  emitDescriptor "cubic-left" {raw with head := x.natPow 3 - x, indices := [2]} queries
  emitDescriptor "cubic-center" {raw with head := x.natPow 3 - x} queries
  emitDescriptor "cubic-right" {raw with head := x.natPow 3 - x, indices := [2], signs := [1]} queries
  emitDescriptor "negative-cubic" {raw with head := x - x.natPow 3, indices := [2], signs := [1]} queries
  for (name, d) in [
      ("absent", {raw with signs := [0]}),
      ("ambiguous", {raw with indices := [2], signs := [1]}),
      ("empty-ambiguous", {raw with indices := [], signs := []}),
      ("unrealized-full", {raw with indices := [1, 2], signs := [-1, -1]}),
      ("duplicate-slot", {raw with indices := [1, 1], signs := [-1, -1]}),
      ("zero-slot", {raw with indices := [0], signs := [0]}),
      ("large-slot", {raw with indices := [3], signs := [1]}),
      ("short-signs", {raw with indices := [1, 2]}),
      ("bad-sign", {raw with signs := [2]}),
      ("stale-context", {raw with context := 10378}),
      ("constant", {raw with head := 1, indices := [], signs := []}),
      ("root-free", {raw with head := x * x + 1}),
      ("zero-head", {raw with head := 0}),
      ("repeated-head", {raw with head := p * p}),
      ("root-endpoint", {raw with lower := .finite (-1)}),
      ("reversed-interval", {raw with lower := .finite 2, upper := .finite (-2)})] do
    emitDescriptor name d queries

  let left : RawDescriptor Rat Nat := ⟨10377, p, .negInf, .posInf, [1], [1]⟩
  let irrational := {left with head := x * x - 2}
  let shared := {left with head := (x * x - 2) * (x - 3), signs := [-1]}
  emitComparison "equal-linear-vectors" {left with head := x - 1} {left with head := x - 2}
  emitComparison "reverse-linear" {left with head := x - 2} {left with head := x - 1}
  emitComparison "permuted-slots" left {left with indices := [2, 1], signs := [1, 1]}
  emitComparison "shared-irrational" irrational shared
  emitComparison "distinct-irrational" {irrational with signs := [-1]} shared
  emitComparison "negative-head" left {left with head := -p, signs := [-1]}
  emitComparison "scaled-head" left {left with head := DensePoly.scale (2 / 3) p}
  emitComparison "foreign-endpoint" {left with head := x - 1, lower := .finite 0, upper := .finite 2}
    {left with head := x - 2, lower := .finite 1, upper := .finite 3}
  emitComparison "disjoint-intervals" {left with
      indices := []
      signs := []
      lower := .finite (-2)
      upper := .finite 0}
    {left with indices := [], signs := [], lower := .finite 0, upper := .finite 2}
  emitComparison "overlapping-equal" {left with lower := .finite 0, upper := .finite 2}
    {left with head := x - 1, lower := .finite (-2), upper := .finite 2}
  emitReencoding "shared-irrational" irrational shared.head .negInf .posInf
  emitReencoding "outside-target" {left with signs := [-1]} p (.finite 0) .posInf
  emitReencoding "missing-root" left (x - 3) .negInf .posInf
  emitReencoding "invalid-target" left p (.finite 1) .posInf
  emitReencoding "foreign-endpoints" {left with
      head := x - 1
      indices := []
      signs := []
      lower := .finite 0
      upper := .finite 2}
    (x * (x - 1) * (x - 2)) .negInf .posInf

end Hex.SignDet.Emit

def main : IO Unit := Hex.SignDet.Emit.run
