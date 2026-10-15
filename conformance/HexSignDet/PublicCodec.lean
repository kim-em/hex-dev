/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexSignDet

public section
open Hex Hex.SignDet

namespace Hex.SignDet.PublicCodec

/-- A public graph reader reduces during an ordinary kernel proof. -/
theorem graph_empty : (Codec.readGraph ValueCodec.rat ValueCodec.nat (0 : Nat)
    (DensePoly.ofList ([1] : List Rat)) .negInf .posInf (.arr #[])).toOption.isNone = true := by
  decide +kernel

/-- Empty literal field. -/
@[expose] def empty : Codec.Json := .arr #[]
/-- Natural-number literal field. -/
@[expose] def natural (n : Nat) : Codec.Json := Codec.Json.of n
/-- A size-zero raw node; parsing asserts no mathematical certificate. -/
@[expose] def node : Codec.Json := .arr #[natural 0,
  .arr #[.arr #[Codec.Json.of (1 : Int), natural 1]],
  .arr #[natural 0], .arr #[natural 2], empty, natural 0,
  .arr #[empty, empty, empty, empty, empty, Codec.Json.of (1 : Int)],
  empty, empty, empty,
  .arr #[natural 0, empty, empty, Codec.Json.of (1 : Int), empty]]
/-- One raw node without children. -/
@[expose] def graph : Codec.Json := .arr #[natural 1, natural 0,
  .arr #[.arr #[node, empty]]]

/-- Reduction reaches a complete node, rather than only an early shape error. -/
theorem graph_node : (Codec.readGraph ValueCodec.rat ValueCodec.nat (0 : Nat)
    (DensePoly.ofList ([1] : List Rat)) .negInf .posInf graph).toOption.isSome = true := by
  decide +kernel


/-- Raw rational zero used in evidence fields. -/
@[expose] def zero : Codec.Json := .arr #[Codec.Json.of (0 : Int), natural 1]
/-- Raw unit polynomial. -/
@[expose] def one : Codec.Json := .arr #[.arr #[Codec.Json.of (1 : Int), natural 1]]
/-- A raw remainder record, with no assertion of its arithmetic identity. -/
@[expose] def remainder : Codec.Json := .arr #[zero, empty, zero]
/-- A raw chain with an optional terminal record. -/
@[expose] def chain : Codec.Json := .arr #[.arr #[one], .arr #[natural 0],
  remainder, .arr #[remainder], .arr #[.arr #[zero, empty]]]
/-- Literal Tarski fields bound to the caller's context and domain. -/
@[expose] def moment : Codec.Json := .arr #[natural 0, one, empty,
  .arr #[natural 0], .arr #[natural 2], chain, chain,
  .arr #[Codec.Json.of (0 : Int)], .arr #[Codec.Json.of (0 : Int)],
  natural 0, natural 0, Codec.Json.of (0 : Int)]
/-- One original-query reduction step with an in-range index. -/
@[expose] def steps : Codec.Json := .arr #[.arr #[natural 0, empty, remainder]]
/-- A node exercising nested witnesses, optional reductions and preparation. -/
@[expose] def nestedNode : Codec.Json := .arr #[natural 0, one,
  .arr #[natural 0], .arr #[natural 2], .arr #[empty], natural 1,
  .arr #[.arr #[.arr #[natural 0]], .arr #[.arr #[Codec.Json.of (0 : Int)]],
    .arr #[Codec.Json.of (0 : Int)], .arr #[Codec.Json.of (0 : Int)],
    .arr #[.arr #[Codec.Json.of (0 : Int)]], Codec.Json.of (0 : Int)],
  .arr #[moment], .arr #[.arr #[.arr #[steps, empty]]], .arr #[steps],
  .arr #[natural 0, empty, empty, Codec.Json.of (0 : Int), empty]]
/-- Wrap one literal raw node, without replaying its arithmetic. -/
@[expose] def wrap (entry : Codec.Json) : Codec.Json :=
  .arr #[natural 1, natural 0, .arr #[.arr #[entry, empty]]]

/-- Kernel reduction traverses every nested evidence reader on public imports. -/
theorem graph_nested : (Codec.readGraph ValueCodec.rat ValueCodec.nat (0 : Nat)
    (DensePoly.ofList ([1] : List Rat)) .negInf .posInf (wrap nestedNode)).toOption.isSome = true := by
  decide +kernel

/-- A structurally decoded graph remains bound to its literal context. -/
theorem graph_wrong_context : (Codec.readGraph ValueCodec.rat ValueCodec.nat (1 : Nat)
    (DensePoly.ofList ([1] : List Rat)) .negInf .posInf (wrap nestedNode)).toOption.isNone = true := by
  decide +kernel

/-- Child indices cannot refer to the entry currently being read. -/
theorem graph_forward_child : (Codec.readGraph ValueCodec.rat ValueCodec.nat (0 : Nat)
    (DensePoly.ofList ([1] : List Rat)) .negInf .posInf
    (.arr #[natural 1, natural 0,
      .arr #[.arr #[nestedNode, .arr #[.arr #[natural 0, natural 0]]]]])).toOption.isNone = true := by
  decide +kernel

/-- Version refusal also reduces through the ordinary public reader. -/
theorem graph_version : (Codec.readGraph ValueCodec.rat ValueCodec.nat (0 : Nat)
    (DensePoly.ofList ([1] : List Rat)) .negInf .posInf
    (.arr #[natural 2, natural 0, .arr #[.arr #[nestedNode, empty]]])).toOption.isNone = true := by
  decide +kernel

/-- Both child indices of a later entry reduce on a complete prefix. -/
theorem graph_children : (Codec.readGraph ValueCodec.rat ValueCodec.nat (0 : Nat)
    (DensePoly.ofList ([1] : List Rat)) .negInf .posInf
    (.arr #[natural 1, natural 1, .arr #[.arr #[node, empty],
      .arr #[nestedNode, .arr #[.arr #[natural 0, natural 0]]]]])).toOption.isSome = true := by
  decide +kernel

/-- An in-range left child cannot hide an invalid right child. -/
theorem graph_right_child : (Codec.readGraph ValueCodec.rat ValueCodec.nat (0 : Nat)
    (DensePoly.ofList ([1] : List Rat)) .negInf .posInf
    (.arr #[natural 1, natural 1, .arr #[.arr #[node, empty],
      .arr #[nestedNode, .arr #[.arr #[natural 0, natural 1]]]]])).toOption.isNone = true := by
  decide +kernel

/-- info: 'Hex.SignDet.PublicCodec.graph_empty' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms graph_empty
/-- info: 'Hex.SignDet.PublicCodec.graph_node' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms graph_node
/-- info: 'Hex.SignDet.PublicCodec.graph_nested' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms graph_nested
/-- info: 'Hex.SignDet.PublicCodec.graph_wrong_context' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms graph_wrong_context
/-- info: 'Hex.SignDet.PublicCodec.graph_forward_child' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms graph_forward_child
/-- info: 'Hex.SignDet.PublicCodec.graph_version' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms graph_version

/-- info: 'Hex.SignDet.PublicCodec.graph_children' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms graph_children

/-- info: 'Hex.SignDet.PublicCodec.graph_right_child' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms graph_right_child

end Hex.SignDet.PublicCodec
