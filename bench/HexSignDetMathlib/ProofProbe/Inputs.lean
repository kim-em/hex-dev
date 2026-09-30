/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexSignDet.Conformance
public import HexSignDetMathlib
public meta import HexSignDet.Dag
public meta import HexSignDet.Conformance

public section

namespace Hex.SignDetMathlib.ProofProbe.Inputs
open Hex.SignDet Hex.SignDet.Conformance

/-- A schematic literal parent: the constant queries have their unique
positive sign on the root in (0,2). No certificate producer is invoked. -/
@[expose] def parent (arity : Nat) : Node Rat Nat :=
  {singletonNode with
    queries := List.replicate arity (DensePoly.C 2)
    system := {literalSystem with
      rows := #v[List.replicate arity 0]
      columns := #v[List.replicate arity 1]
      counts := #v[1], values := #v[1]}}

@[expose] def entries : Nat → Array (Dag.Entry Rat Nat)
  | 0 => #[⟨derivativeNode, none⟩]
  | depth + 1 => (entries depth).push ⟨parent (2 ^ (depth + 1)), some (depth, depth)⟩

/-- Both child references share the preceding accepted entry. This is a
same-level proof graph, not a graph of nested coefficient-sign certificates. -/
@[expose] def graph (depth : Nat) : Dag Rat Nat := ⟨entries depth, depth⟩

@[expose] def stale : Nat → Dag Rat Nat
  | 0 => ⟨#[⟨{derivativeNode with context := 8}, none⟩], 0⟩
  | depth + 1 => ⟨(entries depth).push
      ⟨{parent (2 ^ (depth + 1)) with context := 8}, some (depth, depth)⟩, depth + 1⟩

@[expose] def check (depth : Nat) (evidence : Dag Rat Nat) : Bool :=
  evidence.check Sturm.orderSign 7 singletonRaw.head singletonRaw.lower singletonRaw.upper
    (List.replicate (2 ^ depth) (DensePoly.C 2))

end Hex.SignDetMathlib.ProofProbe.Inputs
