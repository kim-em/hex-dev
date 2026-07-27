/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import HexInterval.Experiment.RationalTable

/-!
Compiled conformance for endpoint erasure and canonical raw rational tables.
The ordinary-kernel examples also confirm that both public checker boundaries
remain transparent from a downstream module.
-/

namespace Hex.Interval.RationalTableConformance

open Experiment.Center Experiment.Scale Experiment.RationalTable

/-! ## Endpoint-erased skeleton -/

#guard checksErasure
#guard fixtureSkeleton == expectedSkeleton
#guard eraseCertificate endpointChanged baseProgram.length endpointChangedSources
  endpointChangedTarget fixtureStructureLimit == expectedSkeleton
#guard eraseCertificate { fixtureCert with result := 8 } baseProgram.length fixtureSources
  fixtureTarget fixtureStructureLimit != expectedSkeleton

-- The projection retains every interval shape required by the public model,
-- including strictness and independently unbounded cuts.
#guard eraseRange .empty == Shape.Range.empty
#guard eraseRange (.bounds (.finite (-2) true) (.finite 3 true)) ==
  Shape.Range.bounds (.finite true) (.finite true)
#guard eraseRange (.bounds .unbounded (.finite 3 false)) ==
  Shape.Range.bounds .unbounded (.finite false)
#guard eraseRange (.bounds (.finite (-2) false) .unbounded) ==
  Shape.Range.bounds (.finite false) .unbounded
#guard eraseRange (.bounds .unbounded .unbounded) ==
  Shape.Range.bounds .unbounded .unbounded

private def openFinite (range : Hex.Interval.Raw) : Hex.Interval.Raw :=
  match range with
  | .bounds (.finite lower _) (.finite upper _) =>
      .bounds (.finite lower true) (.finite upper true)
  | other => other

private def strictnessChangedCert : Certificate :=
  { fixtureCert with
    facts := fixtureFacts.map fun fact =>
      { fact with row := { fact.row with range := openFinite fact.row.range } } }

private def strictnessChangedSources : List Row :=
  fixtureSources.map fun row => { row with range := openFinite row.range }

private def strictnessChangedTarget : Row :=
  { fixtureTarget with range := openFinite fixtureTarget.range }

-- Endpoint values erase, but strictness at a fact, source, or target boundary
-- is structural and therefore changes the projected skeleton.
#guard eraseCertificate strictnessChangedCert baseProgram.length fixtureSources
  fixtureTarget fixtureStructureLimit != expectedSkeleton
#guard eraseCertificate fixtureCert baseProgram.length strictnessChangedSources
  fixtureTarget fixtureStructureLimit != expectedSkeleton
#guard eraseCertificate fixtureCert baseProgram.length fixtureSources
  strictnessChangedTarget fixtureStructureLimit != expectedSkeleton

private def hasShape (nodes facts result lookupSteps : Nat)
    (workload : Option Workload) : Bool :=
  match workload with
  | none => false
  | some accepted =>
      let shape := eraseWorkload accepted
      shape.program.length == nodes && shape.facts.length == facts &&
        shape.result == result && shape.limit.maxLookupSteps == lookupSteps

#guard hasShape 500 10 9 74 (deadNodes? 500)
#guard hasShape 9 50 49 (adjacentLookupSteps 41) (adjacent? 41)
#guard hasShape 9 50 49 (farLookupSteps 41) (far? 41)
#guard hasShape 9 50 9 (sourcePadLookupSteps 40) (some (sourcePad 40))

example : checksErasure = true := by
  decide +kernel

/-! ## Canonical raw rational table -/

#guard checksTable
#guard Table.check fixtureTableLimit fixtureTable == .ready
#guard Table.check fixtureTableLimit [⟨0, 1⟩, ⟨-1, 3⟩, ⟨127, 255⟩] == .ready

-- Logical malformed inputs are rejected rather than normalized.
#guard Table.check fixtureTableLimit [⟨0, 0⟩] ==
  .malformed 0 .zeroDenominator
#guard Table.check fixtureTableLimit [⟨0, 7⟩] ==
  .malformed 0 .notReduced
#guard Table.check fixtureTableLimit [⟨2, 6⟩] ==
  .malformed 0 .notReduced
#guard Table.check fixtureTableLimit [⟨100, 200⟩] ==
  .malformed 0 .notReduced

-- Complete-table validation observes a malformed entry after valid retained
-- values, even though no arithmetic fact refers to that final entry.
#guard Table.check fixtureTableLimit (fixtureTable ++ [⟨0, 7⟩]) ==
  .malformed 4 .notReduced

-- Collection and endpoint caps are caller-owned. Size failure precedes both
-- traversal and logical canonicality failure.
#guard Table.check { fixtureTableLimit with maxEntries := 4 } fixtureTable == .ready
#guard Table.check { fixtureTableLimit with maxEntries := 3 } fixtureTable ==
  .resourceLimit none .entries
#guard Table.check { fixtureTableLimit with maxEntries := 3 }
  (fixtureTable ++ [⟨0, 0⟩]) == .resourceLimit none .entries
#guard Table.check { fixtureTableLimit with maxNumeratorBits := 8 } [⟨255, 1⟩] ==
  .ready
#guard Table.check { fixtureTableLimit with maxNumeratorBits := 8 } [⟨256, 1⟩] ==
  .resourceLimit (some 0) .numeratorBits
#guard Table.check { fixtureTableLimit with maxNumeratorBits := 7 } [⟨128, 1⟩] ==
  .resourceLimit (some 0) .numeratorBits
#guard Table.check { fixtureTableLimit with maxDenominatorBits := 8 } [⟨1, 255⟩] ==
  .ready
#guard Table.check { fixtureTableLimit with maxDenominatorBits := 8 } [⟨1, 256⟩] ==
  .resourceLimit (some 0) .denominatorBits
#guard Table.check { fixtureTableLimit with maxDenominatorBits := 8 }
  (fixtureTable ++ [⟨1, 256⟩]) == .resourceLimit (some 4) .denominatorBits

-- Successful validation reconstructs exactly the checked Core numerator and
-- denominator; it does not silently replace the raw encoding.
example : (RawRat.value ⟨-1, 3⟩).num = -1 ∧ (RawRat.value ⟨-1, 3⟩).den = 3 := by
  exact RawRat.value_fields (limit := fixtureTableLimit) (by decide +kernel)

example : checksTable = true := by
  decide +kernel

end Hex.Interval.RationalTableConformance
