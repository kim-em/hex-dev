/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRealClosure.RootFrame
public import HexSignDet.Codec

public section

namespace Hex.RealClosure.ReplaySize
open SignDet Tower
open SignDet.Codec (Json)

private def object (fields : List (String × Json)) : Json :=
  .object (fields.foldr (fun entry rest => .cons entry.1 entry.2 rest) .nil)

private def occurrences {E C : Type} [Zero E] [DecidableEq E] : Replay E C → Nat
  | .leaf _ => 1
  | .split _ left right => 1 + occurrences left + occurrences right

private def registry : BaseContext.Registry := fun _ => none

private def emitCase {ctx : Context registry}
    (descriptor : Descriptor ctx.Value Signature ctx.sign ctx.signature)
    (depth count : Nat) (repeated : Bool) : IO Unit :=
  letI : Hashable ctx.Value := ⟨fun a => hash (ctx.codec.encode a)⟩
  letI : Hashable Signature := ⟨fun _ => 0⟩
  do
    let x : DensePoly ctx.Value := DensePoly.ofCoeffs #[0, 1]
    let queries := (List.range count).map fun i =>
      x - DensePoly.C (if repeated then 1 else (Nat.cast i : ctx.Value))
    let .ok signs := descriptor.buildSigns queries
      | throw (IO.userError "selected-sign production failed")
    let expected := (List.range count).map fun i =>
      if repeated || i < 2 then (1 : Int) else -1
    unless signs.values.toList == expected do
      throw (IO.userError "selected signs differ from the roots in (1,2)")
    let graph := Dag.encode signs.evidence
    let bytes := graph.encodeBytes ctx.codec (contextCodec ctx.signature)
    let .ok restored := Dag.decodeSigns ctx.codec (contextCodec ctx.signature)
        descriptor queries signs.values bytes
      | throw (IO.userError "selected-sign graph replay failed")
    unless restored.values == signs.values do
      throw (IO.userError "replay changed selected signs")
    let edges := graph.entries.foldl (fun n entry => n + if entry.children.isSome then 2 else 0) 0
    let payload := object [
      ("depth", Json.of depth), ("queries_count", Json.of count),
      ("repeated", .bool repeated), ("head", Codec.poly ctx.codec descriptor.raw.head),
      ("queries", .arr (queries.toArray.map (Codec.poly ctx.codec))),
      ("signs", Json.of signs.values.toList),
      ("tree_occurrences", Json.of (occurrences signs.evidence)),
      ("dag_nodes", Json.of graph.entries.size), ("dag_edges", Json.of edges),
      ("replayed", .bool true),
      ("graph", Codec.graph ctx.codec (contextCodec ctx.signature) graph)]
    let some text := String.fromUTF8? payload.writeBytes
      | throw (IO.userError "invalid UTF-8 output")
    IO.println text.trimAsciiEnd.toString

/-- Exact graph and operand sizes for repeated/distinct linear queries at two
actual selected algebraic levels. This driver records no elapsed time. -/
def emit : IO Unit := do
  let base := Context.base (BaseContext.rational registry)
  let x : DensePoly base.Value := DensePoly.ofCoeffs #[0, 1]
  let some descriptor := Descriptor.validate base.sign base.signature
      { context := base.signature, head := x * x - DensePoly.C (1 + 1),
        lower := .finite 1, upper := .finite (1 + 1), indices := [], signs := [] }
    | throw (IO.userError "first selected descriptor failed")
  let first := base.adjoin descriptor
  let y : DensePoly first.context.Value := DensePoly.ofCoeffs #[0, 1]
  let some next := Descriptor.validate first.context.sign first.context.signature
      { context := first.context.signature, head := y * y - DensePoly.C first.generator,
        lower := .finite 1, upper := .finite (1 + 1), indices := [], signs := [] }
    | throw (IO.userError "second selected descriptor failed")
  for count in [1, 2, 4, 8, 16, 32] do
    for repeated in [true, false] do
      emitCase descriptor 1 count repeated
      emitCase next 2 count repeated

end Hex.RealClosure.ReplaySize

def main : IO Unit := Hex.RealClosure.ReplaySize.emit
