/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import HexIntervalMathlib.Experiment.ExpSign

/-!
# Proof-producing contradiction conformance

An engine contradiction flag is not evidence. This canary closes an arbitrary
target only from an ordinary proof of the exact bottom fact and a package-owned
semantic refutation of that fact.
-/

namespace Hex.IntervalMathlib.RefuteConformance

open Hex.Interval.Experiment
open SemanticReplay ProofEmitter ExpSign

private def bottom : NodeFact Bound :=
  { node := node 0, fact := .empty }

private def childBase : List (NodeFact Bound) :=
  bottom :: baseFacts

private def bottomSound : Evidence
    (semantics.Entails program childBase bottom) :=
  assumeSplit program baseFacts bottom

private def refuted? : Option
    (Evidence (semantics.Entails program childBase checkerInput.target)) :=
  replayRefute emptyRefute program childBase bottom checkerInput.target
    bottomSound

/-- Transparent refutation replay constructs the expected ordinary kernel
theorem; the proposition itself is ex falso because `childBase` contains the
bottom fact. The reduction and guarded dependency report below are the
conformance obligations, and no evaluator or runtime flag occurs in the
declaration. -/
theorem closesTarget :
    semantics.Entails program childBase checkerInput.target :=
  (refuted?.get (by rfl)).proof

/--
info: 'Hex.IntervalMathlib.RefuteConformance.closesTarget' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms closesTarget

private def top : NodeFact Bound :=
  { node := node 0, fact := .all }

private def topSound : Evidence
    (semantics.Entails program baseFacts top) :=
  assumed (by simp [baseFacts, top, node])

/-- Pin the schema's reduction gate: the real adapter rejects a non-bottom
fact instead of constructing refutation evidence. -/
example :
    replayRefute emptyRefute program baseFacts top checkerInput.target
      topSound = none := by
  rfl

end Hex.IntervalMathlib.RefuteConformance
