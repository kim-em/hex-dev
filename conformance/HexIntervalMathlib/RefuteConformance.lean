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

/-- A contradiction leaf produces an ordinary kernel theorem for the branch
target; no evaluator or runtime flag occurs in this declaration. -/
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

/-- A non-bottom fact is rejected by reduction, so the schema check is
load-bearing rather than decorative. -/
example :
    replayRefute emptyRefute program baseFacts top checkerInput.target
      topSound = none := by
  rfl

end Hex.IntervalMathlib.RefuteConformance
