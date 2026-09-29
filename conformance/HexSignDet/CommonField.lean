/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexSignDet
public import HexNumberField
public import HexRealAlgebraic
public import Lean.Data.Json

public section

namespace Hex.SignDet.CommonField

open Lean

/-- Interpret a coordinate using its selected canonical algebraic value.
The companion proves reality and equality with `Coefficients.ofField` for
real generators. Nonreal generators are rejected before fixture execution. -/
@[expose] def value {generator : AlgebraicNumber} (a : QAdjoin generator) : RealAlgebraicNumber :=
  match RealAlgebraicNumber.ofAlgebraic? a.toAlgebraicNumber with
  | some r => r
  | none => Hex.panicWith 0 "CommonField: nonreal coordinate"

@[expose] def sign {generator : AlgebraicNumber} (a : QAdjoin generator) : Int := (value a).sign

private def rat (q : Rat) : Json := toJson #[q.num, (q.den : Int)]

private def algebraic (a : AlgebraicNumber) : Json :=
  let square := a.rep.1.square
  Json.mkObj [("polynomial", toJson a.p.toArray),
    ("lower", rat (square.re - square.radiusHi).toRat),
    ("upper", rat (square.re + square.radiusHi).toRat)]

private def coordinates {generator : AlgebraicNumber} (a : QAdjoin generator) : Json :=
  toJson (a.coeffs.toArray.map rat)

private def poly {generator : AlgebraicNumber} (p : DensePoly (QAdjoin generator)) : Json :=
  toJson (p.toArray.map coordinates)

private def ordering : Ordering → Json
  | .lt => toJson "lt" | .eq => toJson "eq" | .gt => toJson "gt"

private def error (message : String) : Json :=
  Json.mkObj [("status", toJson "error"), ("error", toJson message)]

/-- Emit actual algorithm outputs and exact common-field coordinates. The
independent oracle reconstructs the selected generator and both input values;
no expected signs, counts, derivative words or orders are used here. -/
def fixture (inputs : Array AlgebraicNumber) : Json := Id.run do
  let common := QAdjoin.common inputs
  if !common.generator.isReal then return error "nonreal generator"
  let some a := common.entries[0]? | return error "missing first coordinate"
  let some b := common.entries[1]? | return error "missing second coordinate"
  let x : DensePoly (QAdjoin common.generator) := DensePoly.ofList [0, 1]
  let qa := x - DensePoly.C a
  let qb := x - DensePoly.C b
  let head := qa * qb
  let qs := [qa, qb, DensePoly.C (a - b)]
  let some table := determine sign 7 head .negInf .posInf qs | return error "table"
  let .ok (some roots) := Descriptor.buildRoots sign 7 head .negInf .posInf |
    return error "roots"
  let rawA : RawDescriptor (QAdjoin common.generator) Nat :=
    ⟨7, head, .negInf, .posInf, [1], [-1]⟩
  let rawB : RawDescriptor (QAdjoin common.generator) Nat :=
    ⟨7, qb, .negInf, .posInf, [1], [1]⟩
  let some left := Descriptor.validate sign 7 rawA | return error "left descriptor"
  let some right := Descriptor.validate sign 7 rawB | return error "right descriptor"
  let .ok comparison := left.buildComparison right | return error "comparison"
  let .ok (some same) := left.buildReencoding qa .negInf .posInf | return error "reencoding"
  let result := Json.mkObj [
    ("status", toJson "ok"),
    ("table", toJson (table.rows.toList.map fun (word, count) =>
      Json.mkObj [("signs", toJson word), ("count", toJson count)])),
    ("absentCount", toJson (table.count [0, 0, -1])),
    ("roots", toJson (roots.map fun d => Json.mkObj [
      ("indices", toJson d.raw.indices), ("signs", toJson d.raw.signs),
      ("selected", toJson (qs.map d.signAt)),
      ("replay", toJson (d.raw.check sign 7 d.evidence))])),
    ("order", ordering comparison.order),
    ("totalOrder", ordering (left.compare right)),
    ("reverseOrder", ordering (right.compare left)),
    ("commonHead", poly comparison.common.head),
    ("commonReplay", toJson (comparison.common.check 7 head qb)),
    ("leftReplay", toJson (left.checkReencoding comparison.leftEncoding.target
      comparison.common.head .negInf .posInf comparison.leftEncoding.evidence)),
    ("rightReplay", toJson (right.checkReencoding comparison.rightEncoding.target
      comparison.common.head .negInf .posInf comparison.rightEncoding.evidence)),
    ("reencodedSigns", toJson same.target.raw.signs),
    ("reencodedSelected", toJson (qs.map same.target.signAt)),
    ("equalOrder", ordering (left.compare same.target)),
    ("reencodingReplay", toJson (left.checkReencoding same.target qa .negInf .posInf
      same.evidence)),
    ("copiedReplay", toJson (same.target.raw.check sign 7 left.evidence)),
    ("staleReplay", toJson (same.target.raw.check sign 8 same.target.evidence)),
    ("repeatedAccepted", toJson (determine sign 7 (head * head) .negInf .posInf qs).isSome)]
  return Json.mkObj [("schema", toJson (1 : Nat)),
    ("generator", algebraic common.generator),
    ("inputs", toJson (inputs.map algebraic)),
    ("coordinates", toJson (common.entries.map coordinates)),
    ("head", poly head), ("queries", toJson (qs.map poly)), ("result", result)]

end Hex.SignDet.CommonField
