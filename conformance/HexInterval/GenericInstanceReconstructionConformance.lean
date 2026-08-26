/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import HexInterval.Experiment.GenericInstanceReconstruction

/-!
This conformance isolates generic program reconstruction from package replay.
One event appends the exact final-program suffix; a second version-only event
has an empty node suffix and therefore reconstructs the same program.  The
semantics-wide stability law is uniform in both programs and sees no event,
operation key, or package registry.
-/

namespace Hex.Interval.GenericInstanceReconstructionConformance

open Hex.Interval
open Experiment Propagator SemanticReplay ChronologicalReplay
open GenericInstanceReconstruction

def valueDomain : DomainId := { index := 0 }

def sourceKey : OpKey := { name := "generic-reconstruction.source" }
def identityKey : OpKey := { name := "generic-reconstruction.identity" }

def operations : Array Operation :=
  #[{ key := sourceKey, inputs := [], output := valueDomain },
    { key := identityKey, inputs := [valueDomain], output := valueDomain }]

def node (index : Nat) : NodeId := { index }

def source : Node :=
  { domain := valueDomain, op := { index := 0 }, args := [] }

def identity : Node :=
  { domain := valueDomain, op := { index := 1 }, args := [node 0] }

/-- The only retained full snapshot. -/
def finalProgram : Program :=
  { operations, nodes := #[source, identity] }

/-- The caller program is the exact one-node prefix of the retained snapshot. -/
def baseProgram : Program :=
  programPrefix finalProgram 1

theorem baseSnapshot : GenericInstanceReconstruction.Snapshot finalProgram baseProgram :=
  { finalChecked := by rfl
    currentChecked := by rfl
    finalPrefix :=
      { operationSize := by simp [baseProgram, programPrefix]
        nodeSize := by simp [baseProgram, programPrefix, finalProgram]
        operationAt := by
          intro index _
          simp [baseProgram, programPrefix]
        nodeAt := by
          intro index within
          have indexZero : index = 0 := by
            simpa [baseProgram, programPrefix, finalProgram] using within
          subst index
          rfl }
    sameOperations := rfl }

def semantics : Semantics Unit :=
  { Value := Unit
    models := fun _ _ => True
    holds := fun _ _ _ => True }

/-- One law covers every checked fixed-operation prefix; it contains no case
for the source or identity operations used by this fixture. -/
def stableLaw : StableLaw semantics :=
  { stable := by
      intro before after _ _ prefixWitness _
      exact
        { programPrefix := prefixWitness
          modelsBefore := by
            intro _ _
            trivial
          holdsOld := by
            intro _ _ _ _ _ _ _
            rfl } }

def action (programVersion : Nat) : Action :=
  { serial := programVersion
    programVersion
    application := { index := 0 }
    rule := { index := 0 }
    key := { name := "generic-reconstruction.instance" }
    node := node 0
    kind := .instantiate
    effort := 0
    inputs := [] }

def instanceEvent (programVersion : Nat) (newNodes : List NodeId) : InstanceEvent :=
  { programVersion
    origin := action (programVersion - 1)
    family := 0
    substitution := []
    products := newNodes
    newNodes
    generation := programVersion
    equalities := []
    payload := { index := 0 } }

def appendEvent : InstanceEvent :=
  instanceEvent 1 [node 1]

def appendStep :=
  reconstruct? stableLaw finalProgram baseProgram baseSnapshot appendEvent

/-- Literal reconstruction reduces in the kernel; compiled search is not
needed to establish that the structural step was accepted. -/
theorem appendAccepted : appendStep.isSome := by rfl

theorem appendIsFinal : (appendStep.get appendAccepted).after = finalProgram := by
  rfl

/-- A pure equality/scope-style event advances the outer trace version without
adding a node.  Structural reconstruction correctly keeps the program fixed. -/
def versionOnlyStep :=
  let first := appendStep.get appendAccepted
  reconstruct? stableLaw finalProgram first.after first.next
    (instanceEvent 2 [])

theorem versionOnlyAccepted : versionOnlyStep.isSome := by rfl

theorem versionOnlyKeepsProgram :
    (versionOnlyStep.get versionOnlyAccepted).after = finalProgram := by
  rfl

def appendThenVersionOnly : Bool :=
  match appendStep with
  | none => false
  | some first =>
      match reconstruct? stableLaw finalProgram first.after first.next
          (instanceEvent 2 []) with
      | none => false
      | some second =>
          second.after == finalProgram && second.after.nodes.size == 2

#guard appendThenVersionOnly

-- The event cannot substitute another identifier for the exact fresh suffix,
-- nor claim more nodes than remain in the retained final program.
#guard
  (reconstruct? stableLaw finalProgram baseProgram baseSnapshot
      (instanceEvent 1 [node 2])).isNone &&
    (reconstruct? stableLaw finalProgram baseProgram baseSnapshot
      (instanceEvent 1 [node 1, node 2])).isNone

end Hex.Interval.GenericInstanceReconstructionConformance
