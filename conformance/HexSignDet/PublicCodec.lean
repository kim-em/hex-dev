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

section Encoding

variable {E Ctx : Type} [Zero E] [DecidableEq E]

/-- The complete graph header is available through an ordinary public import. -/
theorem graph_encode (value : ValueCodec E) (context : ValueCodec Ctx) (data : Dag E Ctx) :
    Codec.graph value context data = Codec.Json.arr
      #[Codec.Json.of (1 : Nat), Codec.Json.of data.root,
        Codec.array (Codec.entry value context) data.entries] :=
  Codec.graph_eq value context data

/-- Entry encoding retains the actual node and both optional child indices. -/
theorem entry_encode (value : ValueCodec E) (context : ValueCodec Ctx)
    (data : Dag.Entry E Ctx) :
    Codec.entry value context data = Codec.Json.arr #[Codec.node value context data.node,
      Codec.option (fun (i, j) => Codec.Json.arr #[Codec.Json.of i, Codec.Json.of j])
        data.children] :=
  Codec.entry_eq value context data

/-- Present child indices are preserved even when they are invalid references. -/
theorem entry_children (value : ValueCodec E) (context : ValueCodec Ctx)
    (data : Node E Ctx) (left right : Nat) :
    Codec.entry value context ⟨data, some (left, right)⟩ =
      Codec.Json.arr #[Codec.node value context data,
        Codec.Json.arr #[Codec.Json.arr #[Codec.Json.of left, Codec.Json.of right]]] := by
  simp only [Codec.entry_fn, Codec.option_some]

/-- The node equation exposes all eleven stored fields without a private import. -/
theorem node_fields (value : ValueCodec E) (context : ValueCodec Ctx) (data : Node E Ctx) :
    (Codec.node value context data).getArr?.map Array.size = .ok 11 := by
  rw [Codec.node_eq]
  rfl

/-- info: 'Hex.SignDet.Codec.graph_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Codec.graph_eq
/-- info: 'Hex.SignDet.Codec.entry_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Codec.entry_eq
/-- info: 'Hex.SignDet.Codec.entry_fn' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Codec.entry_fn
/-- info: 'Hex.SignDet.Codec.node_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Codec.node_eq
/-- info: 'Hex.SignDet.PublicCodec.graph_encode' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms graph_encode
/-- info: 'Hex.SignDet.PublicCodec.entry_encode' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms entry_encode
/-- info: 'Hex.SignDet.PublicCodec.entry_children' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms entry_children
/-- info: 'Hex.SignDet.PublicCodec.node_fields' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms node_fields

end Encoding

/-- A public graph reader reduces during an ordinary kernel proof. -/
theorem graph_empty : (Codec.readGraph ValueCodec.rat ValueCodec.nat (0 : Nat)
    (DensePoly.ofList ([1] : List Rat)) .negInf .posInf (.arr #[])).toOption.isNone = true := by
  decide +kernel

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

/-- Raw zero-size records, with no assertion of arithmetic acceptance. -/
@[expose] def rawNode : Node Rat Nat where
  context := 0
  head := DensePoly.C 1
  lower := .negInf
  upper := .posInf
  queries := []
  size := 0
  system := {
    rows := #v[]
    columns := #v[]
    counts := #v[]
    values := #v[]
    inverse := Matrix.ofRows #v[]
    denominator := 1 }
  moments := #v[]
  reductions := #v[]
  preparation := none
  basis := { rank := 0, rows := #v[], cols := #v[], denom := 1, adj := Matrix.ofRows #v[] }

/-- Public equations compose from a source record to a complete numerical packet. -/
theorem graph_literal : Codec.graph ValueCodec.rat ValueCodec.nat
    (⟨#[⟨rawNode, none⟩], 0⟩ : Dag Rat Nat) = graph := by
  rw [Codec.graph_eq, Codec.entry_fn]
  simp only [Codec.array, Array.map_singleton, Codec.option_none]
  rw [Codec.node_eq, Codec.system_eq, Codec.basis_eq]
  simp only [rawNode, Codec.encodeMatrix_eq, Matrix.rows_ofRows, Codec.option_none,
    Codec.Json.of_array, Codec.array, Codec.list, Array.map_empty]
  simp only [graph, node, empty, natural, Codec.poly, Codec.endpoint,
    ValueCodec.rat, ValueCodec.nat, DensePoly.toArray,
    DensePoly.coeffs_C_of_ne_zero (show (1 : Rat) ≠ 0 by decide),
    Codec.array, Array.map_singleton] <;> rfl

/-- info: 'Hex.SignDet.Codec.encodeMatrix_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Codec.encodeMatrix_eq
/-- info: 'Hex.SignDet.Codec.option_none' does not depend on any axioms -/
#guard_msgs in
#print axioms Codec.option_none
/-- info: 'Hex.SignDet.Codec.option_some' does not depend on any axioms -/
#guard_msgs in
#print axioms Codec.option_some
/-- info: 'Hex.SignDet.Codec.system_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Codec.system_eq
/-- info: 'Hex.SignDet.Codec.basis_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Codec.basis_eq
/-- info: 'Hex.SignDet.PublicCodec.graph_literal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms graph_literal

/-- Reduction reaches a complete node, rather than only an early shape error. -/
theorem graph_node : (Codec.readGraph ValueCodec.rat ValueCodec.nat (0 : Nat)
    (DensePoly.ofList ([1] : List Rat)) .negInf .posInf graph).toOption.isSome = true := by
  decide +kernel


/-- Raw rational zero used in evidence fields. -/
def zero : Codec.Json := .arr #[Codec.Json.of (0 : Int), natural 1]
/-- Raw unit polynomial. -/
def one : Codec.Json := .arr #[.arr #[Codec.Json.of (1 : Int), natural 1]]
/-- A raw remainder record, with no assertion of its arithmetic identity. -/
def remainder : Codec.Json := .arr #[zero, empty, zero]
/-- A raw chain with an optional terminal record. -/
def chain : Codec.Json := .arr #[.arr #[one], .arr #[natural 0],
  remainder, .arr #[remainder], .arr #[.arr #[zero, empty]]]
/-- Literal Tarski fields bound to the caller's context and domain. -/
def moment : Codec.Json := .arr #[natural 0, one, empty,
  .arr #[natural 0], .arr #[natural 2], chain, chain,
  .arr #[Codec.Json.of (0 : Int)], .arr #[Codec.Json.of (0 : Int)],
  natural 0, natural 0, Codec.Json.of (0 : Int)]
/-- One original-query reduction step with an in-range index. -/
def steps : Codec.Json := .arr #[.arr #[natural 0, empty, remainder]]
/-- A node exercising nested witnesses, optional reductions and preparation. -/
def nestedNode : Codec.Json := .arr #[natural 0, one,
  .arr #[natural 0], .arr #[natural 2], .arr #[empty], natural 1,
  .arr #[.arr #[.arr #[natural 0]], .arr #[.arr #[Codec.Json.of (0 : Int)]],
    .arr #[Codec.Json.of (0 : Int)], .arr #[Codec.Json.of (0 : Int)],
    .arr #[.arr #[Codec.Json.of (0 : Int)]], Codec.Json.of (0 : Int)],
  .arr #[moment], .arr #[.arr #[.arr #[steps, empty]]], .arr #[steps],
  .arr #[natural 0, empty, empty, Codec.Json.of (0 : Int), empty]]
/-- Wrap one literal raw node, without replaying its arithmetic. -/
def wrap (entry : Codec.Json) : Codec.Json :=
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

/-- Changing the caller's polynomial rejects an otherwise decodable graph. -/
theorem graph_wrong_head : (Codec.readGraph ValueCodec.rat ValueCodec.nat (0 : Nat)
    (DensePoly.ofList ([2] : List Rat)) .negInf .posInf (wrap nestedNode)).toOption.isNone = true := by
  decide +kernel

/-- Both caller endpoints retain their literal identities. -/
theorem graph_wrong_endpoints :
    (Codec.readGraph ValueCodec.rat ValueCodec.nat (0 : Nat)
      (DensePoly.ofList ([1] : List Rat)) (.finite 0) .posInf (wrap nestedNode)).toOption.isNone = true ∧
    (Codec.readGraph ValueCodec.rat ValueCodec.nat (0 : Nat)
      (DensePoly.ofList ([1] : List Rat)) .negInf (.finite 0) (wrap nestedNode)).toOption.isNone = true := by
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

/-- info: 'Hex.SignDet.PublicCodec.graph_wrong_head' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms graph_wrong_head

/-- info: 'Hex.SignDet.PublicCodec.graph_wrong_endpoints' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms graph_wrong_endpoints

end Hex.SignDet.PublicCodec
