/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexSignDet.Codec
public import HexSignDet.Codec.EvidenceLaws
public import HexPoly.InterpretTests
public meta import HexPoly.InterpretTests
public import HexSignDet.CrossCheck
public meta import HexSignDet.CrossCheck
public meta import HexSignDet.Codec

public section

/-! Computational conformance owner: `HexSignDet`. Byte parsing is tested by
compiled execution. Ordinary-kernel graph replay and axiom probes remain in
CrossCheck; successful byte decoding retains that finite checker evidence. -/
namespace Hex.SignDet.FastCheck
open Lean
open Hex.SignDet.Conformance
open Hex.SignDet.CrossCheck

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

-- An invertible local system with the correct total count still cannot omit
-- a realized column. Parsing succeeds; recursive support replay rejects it.
#guard let graph : Dag Rat Nat := ⟨#[⟨forgedNode, none⟩], 0⟩
  let bytes := encoded graph
  (Codec.decodeGraph ValueCodec.rat ValueCodec.nat 7 Sturm.Fixtures.p
    (.finite (-2)) (.finite 2) bytes).isOk &&
  (Dag.decodeBytes ValueCodec.rat ValueCodec.nat Sturm.orderSign 7 Sturm.Fixtures.p
    (.finite (-2)) (.finite 2) forgedNode.queries bytes).toOption.isNone

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

#guard match Dag.decodeDescriptor ValueCodec.rat ValueCodec.nat Sturm.orderSign 7
    (singletonRaw.full [1, 1]) (encoded full) with
  | .error _ => false
  | .ok d => d.raw.context == 7 && d.raw.head == singletonRaw.head &&
      d.raw.indices == [1, 2] && d.raw.signs == [1, 1]
#guard (Dag.decodeDescriptor ValueCodec.rat ValueCodec.nat Sturm.orderSign 7
  (singletonRaw.full [-1, 1]) (encoded full)).toOption.isNone
#guard (Dag.decodeDescriptor ValueCodec.rat ValueCodec.nat Sturm.orderSign 7
  {singletonRaw.full [1, 1] with indices := [2, 2]} (encoded full)).toOption.isNone
#guard (Dag.decodeDescriptor ValueCodec.rat ValueCodec.nat Sturm.orderSign 8
  (singletonRaw.full [1, 1]) (encoded full)).toOption.isNone
#guard (Dag.decodeDescriptor ValueCodec.rat ValueCodec.nat Sturm.orderSign 7
  derivativeRaw (encoded full)).toOption.isNone

/-- info: 'Hex.SignDet.Dag.decodeDescriptor_raw' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Dag.decodeDescriptor_raw

-- Empty query lists and zero-root parents retain their actual empty vectors
-- and rank-zero matrices, rather than being confused with malformed graphs.
#guard match Sturm.prepare Sturm.orderSign singletonRaw.head singletonRaw.lower singletonRaw.upper with
  | none => false
  | some domain =>
    match buildPrepared (7 : Nat) domain [] with
    | .error _ => false
    | .ok t => roundtrip (Dag.encode t.val) && checked [] (encoded (Dag.encode t.val))

#guard let p : DensePoly Rat := DensePoly.C 5
  match Sturm.prepare Sturm.orderSign p .negInf .posInf with
  | none => false
  | some domain =>
    match buildPrepared (7 : Nat) domain [0, 1] with
    | .error _ => false
    | .ok t =>
      let graph := Dag.encode t.val
      t.val.node.size == 0 && graph.entries.size == 3 &&
      (Dag.decodeBytes ValueCodec.rat ValueCodec.nat Sturm.orderSign 7 p
        .negInf .posInf [0, 1] (encoded graph)).isOk

namespace Noncanonical
open HexPoly.InterpretTests

local instance : Hashable Rep := ⟨fun r => hash (raw r)⟩

/-- Preserve both rational coordinates of every nonzero representative. -/
private def codec : ValueCodec Rep where
  encode r := Codec.option (fun a => Json.arr #[ValueCodec.rat.encode a.val.1,
    ValueCodec.rat.encode a.val.2]) r
  decode j := Codec.readOption (fun j => do
    let a ← Codec.tuple 2 j
    let left ← ValueCodec.rat.decode a[0]
    let right ← ValueCodec.rat.decode a[1]
    if h : testZero (left, right) = false then return ⟨(left, right), h⟩
    else throw "noncanonical zero representative") j

private def sign (r : Rep) : Int := (value r).num.sign

#guard codec.encode (pack 0 1) != codec.encode (1 : Rep)
#guard let p : DensePoly Rep := DensePoly.ofCoeffs #[pack (-1) 0, 0, pack 0 1]
  let canonical : DensePoly Rep := DensePoly.ofCoeffs #[pack (-1) 0, 0, 1]
  let qs := [DensePoly.C (pack 0 1)]
  match Sturm.prepare sign p .negInf .posInf with
  | none => false
  | some domain =>
    match buildPrepared (7 : Nat) domain qs with
    | .error _ => false
    | .ok t =>
      let graph := Dag.encode t.val
      let bytes := graph.encodeBytes codec ValueCodec.nat
      match Codec.decodeGraph codec ValueCodec.nat 7 p .negInf .posInf bytes with
      | .error _ => false
      | .ok actual => actual.entries == graph.entries && actual.root == graph.root &&
          (Dag.decodeBytes codec ValueCodec.nat sign 7 p .negInf .posInf qs bytes).isOk &&
          (Dag.decodeBytes codec ValueCodec.nat sign 7 canonical .negInf .posInf qs bytes).toOption.isNone

end Noncanonical

/-- info: 'Hex.SignDet.Dag.decode_replays' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Dag.decode_replays

/-- False arithmetic evidence remains literal after structured encoding. The
separate graph checker must still reject it. This uses ordinary kernel proofs. -/
theorem false_evidence_roundtrip :
    Codec.readTarski ValueCodec.rat ValueCodec.nat
      (Codec.tarski ValueCodec.rat ValueCodec.nat (corruptCert singletonQuery)) =
      .ok (corruptCert singletonQuery) :=
  Codec.read_tarski _ _ ValueCodec.rat_lawful ValueCodec.nat_lawful _

/-- info: 'Hex.SignDet.ValueCodec.nat_lawful' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ValueCodec.nat_lawful
/-- info: 'Hex.SignDet.ValueCodec.rat_lawful' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ValueCodec.rat_lawful
/-- info: 'Hex.SignDet.Codec.read_vector' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Codec.read_vector
/-- info: 'Hex.SignDet.Codec.read_matrix' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Codec.read_matrix
/-- info: 'Hex.SignDet.Codec.read_tarski' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Codec.read_tarski
/-- info: 'Hex.SignDet.Codec.read_reduction' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Codec.read_reduction
/-- info: 'Hex.SignDet.FastCheck.false_evidence_roundtrip' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms false_evidence_roundtrip

end Hex.SignDet.FastCheck
