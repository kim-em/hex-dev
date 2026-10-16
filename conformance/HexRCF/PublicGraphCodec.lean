/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRCF.RealCoefficients

public section
open Hex Hex.SignDet

namespace Hex.RCF.PublicGraphCodec

/-- The optional umbrella exposes the graph reader for kernel reduction. -/
theorem graph_empty : (Codec.readGraph ValueCodec.rat ValueCodec.nat (0 : Nat)
    (DensePoly.ofList ([1] : List Rat)) .negInf .posInf (.arr #[])).toOption.isNone = true := by
  decide +kernel

/-- info: 'Hex.RCF.PublicGraphCodec.graph_empty' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms graph_empty

/-- Empty literal field. -/
def empty : Codec.Json := .arr #[]
/-- Natural-number literal field. -/
def natural (n : Nat) : Codec.Json := Codec.Json.of n
/-- A size-zero raw node; parsing asserts no mathematical certificate. -/
def node : Codec.Json := .arr #[natural 0,
  .arr #[.arr #[Codec.Json.of (1 : Int), natural 1]],
  .arr #[natural 0], .arr #[natural 2], empty, natural 0,
  .arr #[empty, empty, empty, empty, empty, Codec.Json.of (1 : Int)],
  empty, empty, empty,
  .arr #[natural 0, empty, empty, Codec.Json.of (1 : Int), empty]]
/-- One raw node without children. -/
def graph : Codec.Json := .arr #[natural 1, natural 0,
  .arr #[.arr #[node, empty]]]

/-- Reduction reaches a complete node, rather than only an early shape error. -/
theorem graph_node : (Codec.readGraph ValueCodec.rat ValueCodec.nat (0 : Nat)
    (DensePoly.ofList ([1] : List Rat)) .negInf .posInf graph).toOption.isSome = true := by
  decide +kernel

/-- info: 'Hex.RCF.PublicGraphCodec.graph_node' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms graph_node

/-- Literal reconstruction can read the parent token through ordinary imports. -/
theorem parent_decode (context : RealClosure.Tower.Signature) :
    (RealClosure.Tower.contextCodec context).decode (.arr #[.number 0]) = .ok context :=
  RealClosure.Tower.contextCodec_self context

/-- Parent encoding is characterized through the public interface. -/
theorem parent_encode (context : RealClosure.Tower.Signature) :
    (RealClosure.Tower.contextCodec context).encode context = .arr #[.number 0] :=
  RealClosure.Tower.contextCodec_encode_self context

/-- info: 'Hex.RCF.PublicGraphCodec.parent_decode' depends on axioms: [propext] -/
#guard_msgs in
#print axioms parent_decode
/-- info: 'Hex.RCF.PublicGraphCodec.parent_encode' depends on axioms: [propext] -/
#guard_msgs in
#print axioms parent_encode

/-- Parsed constructor-form JSON uses the same public parent rule. -/
theorem parent_parsed (context : RealClosure.Tower.Signature) :
    (RealClosure.Tower.contextCodec context).decode
      (.array (.cons (.number 0) .nil)) = .ok context := by
  simp

/-- Natural-number syntax for the parsed zero also simplifies. -/
theorem parent_natural (context : RealClosure.Tower.Signature) :
    (RealClosure.Tower.contextCodec context).decode
      (.array (.cons (.number (Int.ofNat 0)) .nil)) = .ok context := by
  simp

/-- The two literal equations compose without unfolding the codec. -/
theorem parent_roundtrip (context : RealClosure.Tower.Signature) :
    (RealClosure.Tower.contextCodec context).decode
      ((RealClosure.Tower.contextCodec context).encode context) = .ok context := by
  simp only [RealClosure.Tower.contextCodec_encode_self, RealClosure.Tower.contextCodec_self]

/-- The public simp rules also normalize the composed operation. -/
theorem parent_simp (context : RealClosure.Tower.Signature) :
    (RealClosure.Tower.contextCodec context).decode
      ((RealClosure.Tower.contextCodec context).encode context) = .ok context := by
  simp

/-- info: 'Hex.RCF.PublicGraphCodec.parent_parsed' depends on axioms: [propext] -/
#guard_msgs in
#print axioms parent_parsed
/-- info: 'Hex.RCF.PublicGraphCodec.parent_natural' depends on axioms: [propext] -/
#guard_msgs in
#print axioms parent_natural
/-- info: 'Hex.RCF.PublicGraphCodec.parent_roundtrip' depends on axioms: [propext] -/
#guard_msgs in
#print axioms parent_roundtrip
/-- info: 'Hex.RCF.PublicGraphCodec.parent_simp' depends on axioms: [propext] -/
#guard_msgs in
#print axioms parent_simp

/-- Parsed parent references simplify inside an actual decoder bind. -/
theorem parent_bind (context : RealClosure.Tower.Signature) :
    ((RealClosure.Tower.contextCodec context).decode
      (.array (.cons (.number 0) .nil)) >>= fun signature => pure signature.roots) =
      .ok context.roots := by
  simp

/-- info: 'Hex.RCF.PublicGraphCodec.parent_bind' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms parent_bind

/-- The public characterization covers every parsed JSON value. -/
theorem parent_unique (context : RealClosure.Tower.Signature) (value : Codec.Json) :
    (RealClosure.Tower.contextCodec context).decode value = .ok context ↔
      value = .array (.cons (.number 0) .nil) :=
  RealClosure.Tower.contextCodec_self_iff context value

/-- info: 'Hex.RCF.PublicGraphCodec.parent_unique' depends on axioms: [propext] -/
#guard_msgs in
#print axioms parent_unique

end Hex.RCF.PublicGraphCodec
