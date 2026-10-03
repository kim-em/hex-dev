/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRealClosure.RootFrame
public import HexSignDet.Codec

public section

namespace Hex.RealClosure.NestedReplay
open SignDet Tower
open SignDet.Codec (Json)

private def object (fields : List (String × Json)) : Json :=
  .object (fields.foldr (fun entry rest => .cons entry.1 entry.2 rest) .nil)

private def registry : BaseContext.Registry := fun _ => none

private def selected {ctx : Context registry}
    (d : Descriptor ctx.Value Signature ctx.sign ctx.signature)
    (qs : List (DensePoly ctx.Value)) : IO (List Int × Json) :=
  letI : Hashable ctx.Value := ⟨fun a => hash (ctx.codec.encode a)⟩
  letI : Hashable Signature := ⟨fun _ => 0⟩
  do
    let .ok signs := d.buildSigns qs
      | throw (IO.userError "nested selected-sign producer failed")
    let graph := Dag.encode signs.evidence
    let bytes := graph.encodeBytes ctx.codec (contextCodec ctx.signature)
    let .ok replayed := Dag.decodeSigns ctx.codec (contextCodec ctx.signature) d qs signs.values bytes
      | throw (IO.userError "nested selected-sign byte replay failed")
    unless replayed.values == signs.values do
      throw (IO.userError "nested selected-sign replay changed values")
    unless (Dag.decodeSigns ctx.codec (contextCodec ctx.signature) d qs
        (signs.values.map (fun s => if s = 0 then 1 else -s)) bytes).toOption.isNone do
      throw (IO.userError "nested replay accepted false consumer signs")
    let stale := { graph with entries := graph.entries.modify 0 fun entry =>
      { entry with node := { entry.node with context :=
        { ctx.signature with base :=
          { ctx.signature.base with infinitesimals := ctx.signature.base.infinitesimals + 1 } } } } }
    let cyclic := { graph with entries := graph.entries.modify graph.root fun entry =>
      { entry with children := some (graph.root, graph.root) } }
    let falseDenominator := { graph with entries := graph.entries.modify graph.root fun entry =>
      { entry with node := { entry.node with system :=
        { entry.node.system with denominator := 0 } } } }
    let wrongDenominator := { graph with entries := graph.entries.modify graph.root fun entry =>
      { entry with node := { entry.node with system :=
        { entry.node.system with denominator :=
          if entry.node.system.denominator = -1 then 2 else entry.node.system.denominator + 1 } } } }
    for bad in #[stale, cyclic, falseDenominator, wrongDenominator] do
      let raw := bad.encodeBytes ctx.codec (contextCodec ctx.signature)
      unless (Dag.decodeSigns ctx.codec (contextCodec ctx.signature) d qs signs.values raw).toOption.isNone do
        throw (IO.userError "nested replay accepted stale, cyclic or false integer evidence")
    return (signs.values.toList, object [
      ("queries", .arr (qs.toArray.map (Codec.poly ctx.codec))),
      ("values", Json.of signs.values.toList),
      ("graph", Codec.graph ctx.codec (contextCodec ctx.signature) graph)])

private def selectedFamily {ctx : Context registry}
    (d : Descriptor ctx.Value Signature ctx.sign ctx.signature)
    (qs : List (DensePoly ctx.Value)) : IO Json := do
  let certificates ← qs.toArray.mapM fun q => selected d [q]
  let values ← certificates.mapM fun (signs, _) => do
    unless signs.length == 1 do throw (IO.userError "nested certificate does not have one query")
    return Json.of signs[0]!
  return object [
    ("queries", .arr (qs.toArray.map (Codec.poly ctx.codec))),
    ("values", .arr values), ("certificates", .arr (certificates.map Prod.snd))]

/-- Produce two native selected-root levels over two successive infinitesimals,
export their actual descriptor and signs at each common selected root, and replay
bytes and reconstruct the entire context without installed algebraic prefixes. -/
def emit : IO Unit := do
  let rational := BaseContext.rational registry
  let firstBase := rational.infinitesimal
  let finalBase := firstBase.infinitesimal
  let base := Context.base finalBase
  let epsilon : base.Value := (BaseContext.Element.infinitesimal rational).embed
  let delta : base.Value := BaseContext.Element.infinitesimal firstBase
  let x : DensePoly base.Value := DensePoly.ofCoeffs #[0, 1]
  let head := x * x - DensePoly.C (1 + 1 + epsilon)
  let some descriptor := Descriptor.validate base.sign base.signature
      { context := base.signature, head := head,
        lower := .finite 1, upper := .finite (1 + 1), indices := [], signs := [] }
    | throw (IO.userError "nested first descriptor failed")
  let first := base.adjoin descriptor
  let alpha := first.generator
  let firstQueries := [x - DensePoly.C 1]
  let firstSigns ← selectedFamily descriptor firstQueries
  let y : DensePoly first.context.Value := DensePoly.ofCoeffs #[0, 1]
  let secondHead := y * y - DensePoly.C (alpha + first.embed delta)
  let some secondDescriptor := Descriptor.validate first.context.sign first.context.signature
      { context := first.context.signature, head := secondHead,
        lower := .finite 1, upper := .finite (1 + 1), indices := [], signs := [] }
    | throw (IO.userError "nested second descriptor failed")
  let second := first.context.adjoin secondDescriptor
  let beta := second.generator
  let secondQueries : List (DensePoly first.context.Value) :=
    [y - DensePoly.C (1 : first.context.Value),
      y - DensePoly.C ((1 : first.context.Value) + 1)]
  let scalar := Algebraic.Context.adjoin secondDescriptor first.context.isClean
  for q in secondQueries do
    unless scalar.signPoly q == scalar.signQuery (scalar.queryPoly q) do
      throw (IO.userError "nested scalar sign differs from checked producer")
  let crossing := y - DensePoly.C ((1 : first.context.Value) + 1 / (1 + 1 + 1 + 1 + 1))
  unless (scalar.intervalSign? crossing).isNone && scalar.singleSign? crossing == some (-1) &&
      scalar.signPoly crossing == -1 do
    throw (IO.userError "nested count-one crossing sign failed")
  let secondSigns ← selectedFamily secondDescriptor secondQueries
  let values := #[beta, second.embed alpha, second.embed (first.embed epsilon),
    second.embed (first.embed delta), (beta - 1)⁻¹,
    second.embed ((alpha - 1)⁻¹),
    beta * beta - second.embed (alpha + first.embed delta),
    beta - (1 + 1 / (1 + 1 + 1 + 1 + 1))]
  unless second.context.sign ((beta - 1) * (beta - 1)⁻¹ - 1) == 0 &&
      second.context.sign (second.embed ((alpha - 1) * (alpha - 1)⁻¹ - 1)) == 0 &&
      second.context.sign (beta * beta - second.embed (alpha + first.embed delta)) == 0 do
    throw (IO.userError "nested inverse or defining-equation identity failed")
  let .ok restored := (Catalog.empty registry).reconstruct second.context.signature
    | throw (IO.userError "nested context reconstruction failed")
  for a in values do
    let packet := second.context.write a
    let .ok b := restored.val.read packet
      | throw (IO.userError "nested value reconstruction failed")
    unless restored.val.sign b == second.context.sign a do
      throw (IO.userError "nested restored sign changed")
    unless (restored.val.write b).value == packet.value do
      throw (IO.userError "nested restored payload changed")
  unless (first.context.read (second.context.write beta)).toOption.isNone do
    throw (IO.userError "nested stale reader accepted a later value")
  let payload := object [
    ("case", .string "nested infinitesimal algebraic replay"), ("mode", .string "nested-replay"),
    ("context", second.context.signature.literal.toJson),
    ("selected", .arr #[firstSigns, secondSigns]),
    ("values", .arr (values.map second.context.codec.encode)),
    ("signs", .arr (values.map (fun a => Json.of (second.context.sign a))))]
  let some text := String.fromUTF8? payload.writeBytes
    | throw (IO.userError "nested JSON printer emitted invalid UTF-8")
  IO.println text.trimAsciiEnd.toString

end Hex.RealClosure.NestedReplay
