/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import HexSignDet.Infinitesimal
import HexSignDet.Compare
import Hex.Conformance.Emit
import Lean.Data.Json

/-! Exact rational-function coefficient fixtures for the pinned Z3 RCF oracle.
The order of infinitesimal introduction is part of every input record. -/
namespace Hex.SignDet.EmitInfinitesimal
open Lean Infinitesimal

variable {E : Type} [Lean.Grind.Field E] [DecidableEq E] [NatCast E]

private def rat (q : Rat) : Json := toJson #[q.num, (q.den : Int)]
private def poly (coeff : E → Json) (p : DensePoly E) : Json := Json.arr (p.toArray.map coeff)
private def fraction (coeff : E → Json) (q : RationalFn E) : Json :=
  Json.mkObj [("num", poly coeff q.num), ("den", poly coeff q.den)]
private def first : First → Json := fraction rat
private def second : Second → Json := fraction first

private def endpoint (coeff : E → Json) : Endpoint E → Json
  | .negInf => toJson "-inf"
  | .posInf => toJson "+inf"
  | .finite q => coeff q

private def emit (depth : Nat) (name op : String) (data : Json) : IO Unit :=
  let context := Json.mkObj [("id", toJson (10377 : Nat)),
    ("levels", toJson ((List.range depth).map fun i => s!"epsilon{i + 1}")),
    ("order", toJson "each-new-level-smaller-than-positive-base-elements")]
  Hex.Conformance.Emit.emitResult "HexSignDet" ("infinitesimal/" ++ name) op
    (Json.mkObj [("coefficientContext", context), ("data", data)]).compress

/-- Refine the context in a descendant while retaining all parent certificates. -/
private def staleChild : Replay E Nat → Replay E Nat
  | .leaf n => .leaf { n with context := 10378 }
  | .split n l r => .split n (staleChild l) r

private def row (signs : List Int) (count : Nat) : Json :=
  Json.mkObj [("signs", toJson signs), ("count", toJson count)]

private def table {r : Nat} (s : System r) : Json :=
  toJson (s.positive.map fun i => row s.columns[i] s.counts[i].toNat)

private def result (t : Json) (replay : Bool) : Json :=
  Json.mkObj [("status", toJson "ok"), ("table", t), ("replay", toJson replay)]

private def failure (error : BuildError) : Json :=
  Json.mkObj [("status", toJson "error"), ("error", toJson (reprStr error))]

private def produced (sign : E → Int) (domain : Sturm.PreparedDomain E) (qs : List (DensePoly E))
    (reduced : Bool) : Json :=
  match buildPrepared (10377 : Nat) domain qs reduced with
  | .error error => failure error
  | .ok t => Json.mkObj [("status", toJson "ok"), ("table", table t.val.node.system),
      ("replay", toJson (t.val.check sign 10377 domain.head domain.lower domain.upper qs)),
      ("staleChildReplay", toJson ((staleChild t.val).check sign 10377
        domain.head domain.lower domain.upper qs)),
      ("missingSupportReplay", if qs.length > 1 then toJson
        ((Replay.leaf t.val.node).check sign 10377 domain.head domain.lower domain.upper qs)
        else Json.null)]

private def reference (sign : E → Int) (domain : Sturm.PreparedDomain E) (qs : List (DensePoly E)) : Json :=
  match referencePrepared (10377 : Nat) domain qs with
  | .error error => failure error
  | .ok n => result (table n.system)
    (n.check sign 10377 domain.head domain.lower domain.upper qs)

private def descriptorResult (sign : E → Int) (raw : RawDescriptor E Nat) (qs : List (DensePoly E)) : Json :=
  match Descriptor.build sign 10377 raw with
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
          ("replay", toJson (c.descriptor.raw.check sign 10377 c.descriptor.evidence)),
          ("bindings", toJson (d.raw.completes c.descriptor.raw)),
          ("copiedQueriesReplay", toJson (c.descriptor.evidence.check sign 10377
            raw.head raw.lower raw.upper (c.descriptor.raw.queries.map fun _ => 0)))]
    let selected := match d.buildSigns qs with
      | .error err => failure err
      | .ok s => Json.mkObj [("status", toJson "ok"), ("signs", toJson s.values.toList),
          ("replay", toJson (d.checkSigns qs s.values s.evidence))]
    Json.mkObj [("status", toJson "ok"), ("replay", toJson (raw.check sign 10377 d.evidence)),
      ("completion", completion), ("selected", selected),
      ("staleContextReplay", toJson (raw.check sign 10378 d.evidence)),
      ("changedHeadReplay", toJson ({raw with head := -raw.head}.check sign 10377 d.evidence))]

private def rootsResult (sign : E → Int) (raw : RawDescriptor E Nat) : Json :=
  match Descriptor.buildRoots sign 10377 raw.head raw.lower raw.upper with
  | .error err => failure err
  | .ok none => Json.mkObj [("status", toJson "invalid-domain")]
  | .ok (some roots) => Json.mkObj [("status", toJson "ok"), ("roots", toJson (roots.map fun d =>
      Json.mkObj [("indices", toJson d.raw.indices), ("signs", toJson d.raw.signs),
        ("replay", toJson (d.raw.check sign 10377 d.evidence))]))]

private def emitDescriptor (coeff : E → Json) (sign : E → Int) (depth : Nat) (name : String) (raw : RawDescriptor E Nat)
    (qs : List (DensePoly E)) : IO Unit :=
  emit depth ("descriptor/" ++ name) "descriptor"
    (Json.mkObj [("schema", toJson (1 : Nat)), ("head", poly coeff raw.head),
      ("lower", endpoint coeff raw.lower), ("upper", endpoint coeff raw.upper),
      ("context", toJson raw.context), ("indices", toJson raw.indices), ("signs", toJson raw.signs),
      ("queries", toJson (qs.map (poly coeff))), ("validation", descriptorResult sign raw qs),
      ("roots", rootsResult sign raw)])

private def rawJson (coeff : E → Json) (raw : RawDescriptor E Nat) : Json :=
  Json.mkObj [("head", poly coeff raw.head), ("lower", endpoint coeff raw.lower), ("upper", endpoint coeff raw.upper),
    ("context", toJson raw.context), ("indices", toJson raw.indices), ("signs", toJson raw.signs)]

private def emitComparison (coeff : E → Json) (sign : E → Int) (depth : Nat) (name : String) (left right : RawDescriptor E Nat) : IO Unit := do
  let output := match Descriptor.build sign 10377 left,
      Descriptor.build sign 10377 right with
    | .ok (.ok l), .ok (.ok r) => match l.buildComparison r with
      | .error err => failure err
      | .ok c => Json.mkObj [("status", toJson "ok"), ("commonHead", poly coeff c.common.head),
          ("order", toJson (match c.order with | .lt => "lt" | .eq => "eq" | .gt => "gt")),
          ("leftSigns", toJson c.leftEncoding.target.raw.signs),
          ("rightSigns", toJson c.rightEncoding.target.raw.signs),
          ("commonReplay", toJson (c.common.check 10377 left.head right.head)),
          ("leftReplay", toJson (l.checkReencoding c.leftEncoding.target c.common.head
            .negInf .posInf c.leftEncoding.evidence)),
          ("rightReplay", toJson (r.checkReencoding c.rightEncoding.target c.common.head
            .negInf .posInf c.rightEncoding.evidence))]
    | _, _ => Json.mkObj [("status", toJson "invalid-input")]
  emit depth ("compare/" ++ name) "compare"
    (Json.mkObj [("schema", toJson (1 : Nat)), ("left", rawJson coeff left),
      ("right", rawJson coeff right), ("result", output)])

private def emitReencoding (coeff : E → Json) (sign : E → Int) (depth : Nat) (name : String) (raw : RawDescriptor E Nat)
    (head : DensePoly E) (a b : Endpoint E) : IO Unit := do
  let output := match Descriptor.build sign 10377 raw with
    | .ok (.ok d) => match d.buildReencoding head a b with
      | .error err => failure err
      | .ok none => Json.mkObj [("status", toJson "none")]
      | .ok (some r) => Json.mkObj [("status", toJson "ok"),
          ("signs", toJson r.target.raw.signs), ("indices", toJson r.target.raw.indices),
          ("replay", toJson (d.checkReencoding r.target head a b r.evidence))]
    | _ => Json.mkObj [("status", toJson "invalid-input")]
  emit depth ("reencode/" ++ name) "reencode"
    (Json.mkObj [("schema", toJson (1 : Nat)), ("source", rawJson coeff raw),
      ("head", poly coeff head), ("lower", endpoint coeff a), ("upper", endpoint coeff b),
      ("result", output)])

private def emitTable (coeff : E → Json) (sign : E → Int) (depth : Nat)
    (name : String) (p : DensePoly E) (qs : List (DensePoly E))
    (lower : Endpoint E := .negInf) (upper : Endpoint E := .posInf) : IO Unit := do
  let input := [("schema", toJson (1 : Nat)), ("head", poly coeff p),
    ("queries", toJson (qs.map (poly coeff))),
    ("lower", endpoint coeff lower), ("upper", endpoint coeff upper)]
  let fields := match Sturm.prepare sign p lower upper with
    | none =>
      let invalid := Json.mkObj [("status", toJson "invalid-domain")]
      [("reduced", invalid), ("direct", invalid), ("reference", invalid)]
    | some domain =>
      [("reduced", produced sign domain qs true), ("direct", produced sign domain qs false)] ++
      (if qs.length ≤ 4 then [("reference", reference sign domain qs)] else [])
  emit depth name "table" (Json.mkObj (input ++ fields))

def run : IO Unit := do
  let p := passmore
  let third := p.derivative.derivative.derivative
  emitTable first firstSign 1 "passmore/whole" p [third]
  emitTable first firstSign 1 "passmore/positive" p [third] (.finite 0) .posInf
  emitTable first firstSign 1 "passmore/empty" p [] (.finite 0) .posInf
  let raw : RawDescriptor First Nat := ⟨10377, p, .finite 0, .posInf, [3], [-1]⟩
  emitDescriptor first firstSign 1 "passmore/cubic" raw [third, x, p]
  emitDescriptor first firstSign 1 "passmore/square" {raw with signs := [1]} [third, x, p]
  emitDescriptor first firstSign 1 "passmore/ambiguous" {raw with indices := [], signs := []} []
  emitComparison first firstSign 1 "passmore/order" raw {raw with signs := [1]}
  emitReencoding first firstSign 1 "passmore/reencode" raw
    (DensePoly.C epsilon * x.natPow 3 - 1) .negInf .posInf
  let q : DensePoly First := x.natPow 2 - DensePoly.C epsilon
  emitTable first firstSign 1 "square/zero-repeat" q [0, x, x, q]
  emitTable first firstSign 1 "square/negative-scale" (-q) [x]
  let qr : RawDescriptor First Nat := ⟨10377, q, .negInf, .posInf, [1], [1]⟩
  emitDescriptor first firstSign 1 "square/negative-head"
    {qr with head := -q, signs := [-1]} [x, q]
  emitComparison first firstSign 1 "square/scaled-equal" qr
    {qr with head := DensePoly.C (-epsilon) * q, signs := [-1]}
  emitComparison first firstSign 1 "passmore/shared-cubic" raw
    {raw with head := DensePoly.C epsilon * x.natPow 3 - 1, indices := [1], signs := [1]}
  emitTable first firstSign 1 "square/zero-root" x [x, 0]
  emitTable first firstSign 1 "square/constant" (DensePoly.C epsilon) []
  emitTable first firstSign 1 "square/root-free" (x.natPow 2 + DensePoly.C epsilon) []
  emitTable first firstSign 1 "square/repeated" (q * q) []
  emitTable first firstSign 1 "square/root-endpoint" (x - DensePoly.C epsilon) []
    (.finite epsilon) .posInf
  emitTable first firstSign 1 "square/cancelled" (q - q) []
  let n := nested
  emitTable second secondSign 2 "nested/whole" n
    [x - DensePoly.C delta, x - DensePoly.C (lift epsilon), 0]
  emitTable second secondSign 2 "nested/singleton" n [] (.finite 0) (.finite (2 * delta))
  emitTable second secondSign 2 "nested/reversed" n []
    (.finite (lift epsilon)) (.finite (2 * delta))
  emitTable second secondSign 2 "nested/root-endpoint" n [] (.finite delta) .posInf
  let nr : RawDescriptor Second Nat := ⟨10377, n, .finite 0, .finite (2 * delta), [], []⟩
  emitDescriptor second secondSign 2 "nested/singleton" nr
    [x - DensePoly.C delta, x - DensePoly.C (lift epsilon)]
  emitDescriptor second secondSign 2 "nested/stale-context" {nr with context := 10378} []
  emitReencoding second secondSign 2 "nested/reencode" nr
    (x - DensePoly.C delta) .negInf .posInf

end Hex.SignDet.EmitInfinitesimal

def main : IO Unit := Hex.SignDet.EmitInfinitesimal.run
