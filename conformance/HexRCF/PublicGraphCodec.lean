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

/-- Parent encoding is characterized without exposing the decoder implementation. -/
theorem parent_encode (context : RealClosure.Tower.Signature) :
    (RealClosure.Tower.contextCodec context).encode context = .arr #[.number 0] :=
  RealClosure.Tower.contextCodec_encode_self context

/-- info: 'Hex.RCF.PublicGraphCodec.parent_decode' depends on axioms: [propext] -/
#guard_msgs in
#print axioms parent_decode
/-- info: 'Hex.RCF.PublicGraphCodec.parent_encode' depends on axioms: [propext] -/
#guard_msgs in
#print axioms parent_encode

end Hex.RCF.PublicGraphCodec
