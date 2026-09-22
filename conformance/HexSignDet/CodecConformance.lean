/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexSignDet.Codec
public import HexSignDet.DagConformance
public meta import HexSignDet.DagConformance
public meta import HexSignDet.Codec

public section

/-! Computational conformance owner: `HexSignDet`. Byte parsing is tested by
compiled execution. Ordinary-kernel graph replay and axiom probes remain in
DagConformance; successful byte decoding retains that finite checker evidence. -/
namespace Hex.SignDet.CodecConformance
open Lean
open Hex.SignDet.Conformance
open Hex.SignDet.DagConformance

private def encoded (d : Dag Rat Nat) : ByteArray := d.encodeBytes ValueCodec.rat ValueCodec.nat
private def decoded (bytes : ByteArray) : Except String (Dag Rat Nat) :=
  Codec.decodeGraph ValueCodec.rat ValueCodec.nat 7 singletonRaw.head
    singletonRaw.lower singletonRaw.upper bytes
private def checked (qs : List (DensePoly Rat)) (bytes : ByteArray) : Bool :=
  (Dag.decodeBytes ValueCodec.rat ValueCodec.nat Sturm.orderSign 7 singletonRaw.head
    singletonRaw.lower singletonRaw.upper qs bytes).isOk

private def roundtrip (d : Dag Rat Nat) : Bool :=
  match decoded (encoded d) with
  | .error _ => false
  | .ok actual => actual.root == d.root && actual.entries == d.entries

#guard roundtrip full && checked fullNode.queries (encoded full)
#guard roundtrip shared && checked sharedParent.queries (encoded shared)
#guard !checked [0, 0] (encoded full)

-- Every decoder field is compared literally on a produced reduced graph,
-- including query preprocessing, per-moment reductions and rank witnesses.
#guard match Sturm.prepare Sturm.orderSign singletonRaw.head singletonRaw.lower singletonRaw.upper with
  | none => false
  | some domain =>
    let qs := [DensePoly.ofCoeffs #[0, 1], 0, DensePoly.ofCoeffs #[0, 1], 0]
    match buildPrepared (7 : Nat) domain qs with
    | .error _ => false
    | .ok tree =>
      let graph := Dag.encode tree.val
      roundtrip graph && checked qs (encoded graph)

-- Parsing a structurally valid false certificate must not grant acceptance.
#guard let bad : Dag Rat Nat := ⟨#[⟨badDenominator, none⟩], 0⟩
  (decoded (encoded bad)).isOk && !checked badDenominator.queries (encoded bad)

#guard (decoded (encoded ⟨#[], 0⟩)).toOption.isNone
#guard (decoded (encoded {full with root := 3})).toOption.isNone
#guard (decoded (encoded ⟨#[⟨fullNode, some (0, 0)⟩], 0⟩)).toOption.isNone
#guard (decoded (encoded ⟨#[⟨fullNode, some (1, 2)⟩,
  ⟨firstNode, none⟩, ⟨derivativeNode, none⟩], 0⟩)).toOption.isNone
#guard (decoded (encoded {full with entries := full.entries.push ⟨fullNode, some (3, 3)⟩})).toOption.isNone
#guard (decoded (encoded ⟨#[⟨firstNode, none⟩,
  ⟨{derivativeNode with context := 8}, none⟩, ⟨fullNode, some (0, 1)⟩], 2⟩)).toOption.isNone
#guard let stale := {derivativeNode with moments := derivativeNode.moments.map fun c =>
    {c with context := 8}}
  (decoded (encoded ⟨#[⟨firstNode, none⟩, ⟨stale, none⟩, ⟨fullNode, some (0, 1)⟩], 2⟩)).toOption.isNone
#guard (decoded (encoded ⟨#[⟨{firstNode with lower := .finite (-2)}, none⟩], 0⟩)).toOption.isNone

private def replace (i : Nat) (value : Json) (j : Json) : Json :=
  match j with
  | .arr a => .arr (a.set! i value)
  | _ => .null

private def nodeWire : Json := Codec.node ValueCodec.rat ValueCodec.nat derivativeNode
private def readNode (j : Json) : Bool :=
  (Codec.readNode ValueCodec.rat ValueCodec.nat j).isOk

#guard readNode nodeWire
#guard !readNode (replace 5 (toJson (4 : Nat)) nodeWire)
#guard !readNode (replace 5 (toJson (10^50 : Nat)) nodeWire)
#guard !readNode (replace 7 (.arr #[]) nodeWire)
#guard !readNode (replace 8 (.arr #[]) nodeWire)
#guard !readNode (replace 10 (.arr #[toJson (4 : Nat), .arr #[], .arr #[],
  toJson (1 : Int), .arr #[]]) nodeWire)
#guard !readNode (replace 10 (.arr #[toJson (1 : Nat), toJson (#[3] : Array Nat),
  toJson (#[0] : Array Nat), toJson (1 : Int), toJson (#[#[1]] : Array (Array Int))]) nodeWire)

#guard (ValueCodec.rat.decode (.arr #[toJson (2 : Int), toJson (2 : Nat)])).toOption.isNone
#guard (ValueCodec.rat.decode (.arr #[toJson (1 : Int), toJson (0 : Nat)])).toOption.isNone
#guard (Codec.readPoly ValueCodec.rat
  (.arr #[ValueCodec.rat.encode 1, ValueCodec.rat.encode 0])).toOption.isNone
#guard (Codec.readEndpoint ValueCodec.rat (.arr #[toJson (1 : Nat)])).toOption.isNone
#guard (decoded "[2,0,[]]".toUTF8).toOption.isNone
#guard (decoded "[1,0,[],0]".toUTF8).toOption.isNone
#guard (decoded "[1,0,[]] trailing".toUTF8).toOption.isNone
#guard (decoded (ByteArray.mk #[255])).toOption.isNone
#guard (Codec.parse {} "[1e1000000000,0,[]]".toUTF8).toOption.isNone
#guard (Codec.parse {} "[1.0,0,[]]".toUTF8).toOption.isNone
#guard (Codec.checkBytes {bytes := 1} "[]".toUTF8).toOption.isNone
#guard (Codec.checkBytes {depth := 1} "[[]]".toUTF8).toOption.isNone
#guard (Codec.checkBytes {digits := 2} "[-123]".toUTF8).toOption.isNone
#guard (Codec.checkBytes {depth := 0, digits := 0} "\"[{}]e+1\"".toUTF8).isOk
#guard (Codec.checkBytes {depth := 0} "\"\\\"[\"".toUTF8).isOk
#guard (Codec.checkBytes {} "\"unterminated".toUTF8).toOption.isNone

-- Composite contexts preserve all components, including a changed refinement
-- slot. A codec for a single identifier is not substituted for the full value.
#guard match Sturm.prepare Sturm.orderSign singletonRaw.head singletonRaw.lower singletonRaw.upper with
  | none => false
  | some domain =>
    match buildPrepared ([7, 1] : List Nat) domain [DensePoly.ofCoeffs #[0, 1]] with
    | .error _ => false
    | .ok tree =>
      let ctx : ValueCodec (List Nat) := ⟨toJson, fromJson?⟩
      let bytes := (Dag.encode tree.val).encodeBytes ValueCodec.rat ctx
      (Dag.decodeBytes ValueCodec.rat ctx Sturm.orderSign [7, 1] singletonRaw.head
        singletonRaw.lower singletonRaw.upper tree.val.node.queries bytes).isOk &&
      (Dag.decodeBytes ValueCodec.rat ctx Sturm.orderSign [7, 2] singletonRaw.head
        singletonRaw.lower singletonRaw.upper tree.val.node.queries bytes).toOption.isNone

/-- info: 'Hex.SignDet.Dag.decode_replays' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Dag.decode_replays

end Hex.SignDet.CodecConformance
