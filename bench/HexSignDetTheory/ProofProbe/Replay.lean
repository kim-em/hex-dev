/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexSignDetTheory.Diagnostics.D3.Semantic
public import HexSignDetTheory.Diagnostics.D3.Reject

/-! Shared BKR graph replay and mathematical root counts. Imported examples use the ordinary
Lean kernel and guard their theorem axiom inventories. -/

public section

namespace Hex.SignDetTheory.ProofProbe
open Hex Hex.SignDet Hex.SignDet.Conformance Hex.SignDetTheory.Diagnostics

/-- Re-export the checked graph and its mathematical counts from the warm
diagnostic dependency. -/
theorem replay_counts : ∃ t,
    Dag.replay? Sturm.orderSign 7 singletonRaw.head singletonRaw.lower singletonRaw.upper
      (List.replicate (2 ^ 3) (DensePoly.C (2 : Rat))) D3.Accept.evidence = some t ∧
    ∀ condition, t.val.node.system.count condition =
      (Semantics.roots.filter (fun x => Semantics.signCondition 3 x = condition)).card :=
  D3.Semantic.counts_roots

/-- A stale literal context is rejected by the independent checker. -/
theorem replay_stale : Inputs.check 3 D3.Reject.evidence = false := D3.Reject.checked

/-- info: 'Hex.SignDetTheory.ProofProbe.replay_counts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms replay_counts

/-- info: 'Hex.SignDetTheory.ProofProbe.replay_stale' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms replay_stale

end Hex.SignDetTheory.ProofProbe
