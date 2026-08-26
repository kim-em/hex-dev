/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexInterval.Experiment.ChronologicalReplay

@[expose] public section

/-!
# Generic reconstruction of instantiation program prefixes

An instantiation event records the identifiers of its fresh node suffix, while
the retained trace records the final program.  This module reconstructs the
intermediate program without asking a function package to choose it: the next
program is the exact prefix of the final node array whose length is the current
length plus `event.newNodes.length`.

Function packages remain responsible for replaying their conservative-
extension theorem.  Stability of old models and facts is instead supplied once
for the complete semantics by `StableLaw`; it cannot inspect the event or a
package registry.
-/

namespace Hex.Interval.Experiment.GenericInstanceReconstruction

open Propagator SemanticReplay ChronologicalReplay

/-- The exact node prefix of a retained final program.  Instantiation never
changes the operation table, so every prefix reuses the final table verbatim. -/
def programPrefix (final : Program) (nodeCount : Nat) : Program :=
  { operations := final.operations
    nodes := final.nodes.extract 0 nodeCount }

/-- Structural invariants carried between reconstructed instance events. -/
structure Snapshot (final current : Program) : Prop where
  finalChecked : final.check = true
  currentChecked : current.check = true
  finalPrefix : ProgramPrefix current final
  sameOperations : current.operations = final.operations

/-- Stability is a property of the assembled semantics, not of an individual
instantiation recipe.  A standard node-local semantics should prove this law
once for every checked fixed-operation prefix. -/
structure StableLaw (semantics : Semantics Fact) : Type where
  stable :
    ∀ {before after : Program},
      before.check = true ->
      after.check = true ->
      ProgramPrefix before after ->
      before.operations = after.operations ->
      StableStep semantics before after

/-- One structurally reconstructed instance step and the invariants needed for
the following step. -/
structure Step (semantics : Semantics Fact) (final before : Program)
    (event : InstanceEvent) where
  after : Program
  stepPrefix : ProgramPrefix before after
  stable : StableStep semantics before after
  sameOperations : before.operations = after.operations
  exactNewNodes :
    Propagator.newNodeIds before.nodes.size after.nodes.size =
      event.newNodes
  next : Snapshot final after

/-- Build the exact next program prefix selected by an instance event.

The final snapshot, current-to-final prefix, fixed operation table, program
checks, and exact fresh identifiers are all revalidated.  The only semantic
input is the universal `StableLaw`; no function key or package value is
available to this routine. -/
def reconstruct? {Fact : Type} {semantics : Semantics Fact}
    (law : StableLaw semantics) (final before : Program)
    (snapshot : Snapshot final before) (event : InstanceEvent) :
    Option (Step semantics final before event) := do
  let nextSize := before.nodes.size + event.newNodes.length
  if within : nextSize ≤ final.nodes.size then
    let after := programPrefix final nextSize
    if afterChecked : after.check = true then
      let stepPrefix : ProgramPrefix before after :=
        { operationSize := by
            simp [after, programPrefix, snapshot.sameOperations]
          nodeSize := by
            simp only [after, programPrefix, Array.size_extract]
            omega
          operationAt := by
            intro index _
            simp [after, programPrefix, snapshot.sameOperations]
          nodeAt := by
            intro index beforeIndex
            have nextIndex : index < nextSize := by omega
            have finalIndex : index < final.nodes.size := by omega
            have extractIndex :
                index < min nextSize final.nodes.size - 0 := by omega
            simp only [after, programPrefix]
            rw [Array.getElem?_extract]
            simp only [extractIndex, ↓reduceIte, Nat.zero_add]
            exact snapshot.finalPrefix.nodeAt index beforeIndex }
      let sameOperations : before.operations = after.operations := by
        simpa [after, programPrefix] using snapshot.sameOperations
      if exactNewNodes :
          Propagator.newNodeIds before.nodes.size after.nodes.size =
            event.newNodes then
        let afterPrefix : ProgramPrefix after final :=
          { operationSize := by simp [after, programPrefix]
            nodeSize := by
              simp only [after, programPrefix, Array.size_extract]
              omega
            operationAt := by
              intro index _
              simp [after, programPrefix]
            nodeAt := by
              intro index afterIndex
              have nextIndex : index < nextSize := by
                simpa [after, programPrefix, within] using afterIndex
              have finalIndex : index < final.nodes.size :=
                Nat.lt_of_lt_of_le nextIndex within
              have extractIndex :
                  index < min nextSize final.nodes.size - 0 := by omega
              simp only [after, programPrefix]
              rw [Array.getElem?_extract]
              simp only [extractIndex, ↓reduceIte, Nat.zero_add] }
        some
          { after
            stepPrefix
            stable := law.stable snapshot.currentChecked afterChecked
              stepPrefix sameOperations
            sameOperations
            exactNewNodes
            next :=
              { finalChecked := snapshot.finalChecked
                currentChecked := afterChecked
                finalPrefix := afterPrefix
                sameOperations := by simp [after, programPrefix] } }
      else
        none
    else
      none
  else
    none

end Hex.Interval.Experiment.GenericInstanceReconstruction
