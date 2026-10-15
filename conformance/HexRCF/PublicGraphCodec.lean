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

end Hex.RCF.PublicGraphCodec
