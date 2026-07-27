/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import HexInterval.Experiment.RationalCertificate

/-!
Compiled conformance for the table-indexed rational certificate boundary.
These checks exercise structural cross-backend identity, complete table
validation, typed endpoint references, and downstream kernel transparency.
-/

namespace Hex.Interval.RationalCertificateConformance

open Experiment.RationalCertificate

/-! ## Cross-backend structural identity -/

#guard checkFixture
#guard checksProjection
#guard fixtureProjection.skeleton == Experiment.RationalTable.fixtureSkeleton
#guard fixtureProjection.skeleton == Experiment.RationalTable.expectedSkeleton
#guard fixtureProjection.tableLimit == fixtureTableLimit
#guard fixtureProjection.referenceLimit == fixtureReferenceLimit
#guard fixtureProjection.skeleton.program ==
  Experiment.RationalTable.expectedSkeleton.program
#guard fixtureProjection.skeleton.center == Experiment.Center.centerWitness
#guard fixtureProjection.skeleton.edges == [Experiment.Center.centerEdge]
#guard fixtureProjection.skeleton.facts ==
  Experiment.RationalTable.expectedSkeleton.facts
#guard fixtureProjection.skeleton.result == 9
#guard fixtureProjection.skeleton.baseSize == baseProgram.length
#guard fixtureProjection.skeleton.sources ==
  Experiment.RationalTable.expectedSkeleton.sources
#guard fixtureProjection.skeleton.target ==
  Experiment.RationalTable.expectedSkeleton.target
#guard fixtureProjection.skeleton.limit == fixtureStructureLimit
#guard fixtureProjection.sourceValues == [unitValueRange]
#guard fixtureProjection.targetValue == quarterValueRange

-- Erasure preserves every interval shape while discarding only table indices.
#guard eraseRange .empty == Experiment.RationalTable.Shape.Range.empty
#guard eraseRange (.bounds (.finite (endpoint 0) true) (.finite (endpoint 1) true)) ==
  Experiment.RationalTable.Shape.Range.bounds (.finite true) (.finite true)
#guard eraseRange (.bounds (.finite (endpoint 0) true) (.finite (endpoint 1) false)) ==
  Experiment.RationalTable.Shape.Range.bounds (.finite true) (.finite false)
#guard eraseRange (.bounds (.finite (endpoint 0) false) (.finite (endpoint 1) true)) ==
  Experiment.RationalTable.Shape.Range.bounds (.finite false) (.finite true)
#guard eraseRange (.bounds .unbounded (.finite (endpoint 1) false)) ==
  Experiment.RationalTable.Shape.Range.bounds .unbounded (.finite false)
#guard eraseRange (.bounds (.finite (endpoint 0) false) .unbounded) ==
  Experiment.RationalTable.Shape.Range.bounds (.finite false) .unbounded
#guard eraseRange (.bounds .unbounded .unbounded) ==
  Experiment.RationalTable.Shape.Range.bounds .unbounded .unbounded

-- Backend-specific table/reference limits remain part of the rational
-- projection rather than being conflated with the shared structural skeleton.
private def smallerTableLimit : Experiment.RationalTable.RawRat.Limit :=
  { fixtureTableLimit with maxEntries := fixtureTableLimit.maxEntries - 1 }

private def smallerProjection : Projection :=
  projectCertificate fixtureCert smallerTableLimit fixtureReferenceLimit
    baseProgram.length fixtureSources fixtureTarget fixtureStructureLimit

#guard smallerProjection.skeleton == fixtureProjection.skeleton
#guard smallerProjection.tableLimit == smallerTableLimit
#guard smallerProjection.referenceLimit == fixtureReferenceLimit
#guard smallerProjection != fixtureProjection

/-! ## Complete table and index validation -/

#guard rejectsBadBoundary
#guard checksReferenceBudget
#guard fixtureCert.endpointLookupCost? fixtureSources fixtureTarget == some 73
#guard !fixtureCert.check fixtureTableLimit
  { fixtureReferenceLimit with maxEndpointLookupSteps := 72 }
  fixtureStructureLimit baseProgram.length fixtureSources fixtureTarget

private def roomyTableLimit : Experiment.RationalTable.RawRat.Limit :=
  { fixtureTableLimit with maxEntries := fixtureTableLimit.maxEntries + 1 }

-- An invalid final entry is rejected even though no literal or cut refers to
-- it.  Logical and resource failures both cross the complete table boundary.
#guard !({ fixtureCert with table :=
    fixtureTable ++ [Experiment.RationalTable.RawRat.mk 0 7] }).check
  roomyTableLimit fixtureReferenceLimit fixtureStructureLimit baseProgram.length
  fixtureSources fixtureTarget
#guard !({ fixtureCert with table :=
    fixtureTable ++ [Experiment.RationalTable.RawRat.mk 0 0] }).check
  roomyTableLimit fixtureReferenceLimit fixtureStructureLimit baseProgram.length
  fixtureSources fixtureTarget
#guard !({ fixtureCert with table :=
    fixtureTable ++ [Experiment.RationalTable.RawRat.mk 256 1] }).check
  roomyTableLimit fixtureReferenceLimit fixtureStructureLimit baseProgram.length
  fixtureSources fixtureTarget

private def missing : EndpointId := endpoint fixtureTable.length

private def missingLiteralProgram : Program :=
  [Prim.var 0, Prim.lit missing] ++ fixtureCert.program.drop 2

private def missingFact : Fact :=
  ⟨⟨Experiment.Center.node 0, Range.closed zero missing⟩, .source 0⟩

private def missingSource : ExpectedRow :=
  ⟨⟨Experiment.Center.node 0, Range.closed missing one⟩, unitValueRange⟩

private def missingTarget : ExpectedRow :=
  ⟨⟨Experiment.Center.node 3, Range.closed zero missing⟩, quarterValueRange⟩

#guard !(endpoint 5).valid fixtureTable
#guard !({ fixtureCert with program := missingLiteralProgram }).check fixtureTableLimit
  fixtureReferenceLimit fixtureStructureLimit baseProgram.length fixtureSources
  fixtureTarget
#guard !({ fixtureCert with facts := missingFact :: fixtureFacts.drop 1 }).check
  fixtureTableLimit fixtureReferenceLimit fixtureStructureLimit baseProgram.length
  fixtureSources fixtureTarget
#guard !fixtureCert.check fixtureTableLimit fixtureReferenceLimit
  fixtureStructureLimit baseProgram.length [missingSource] fixtureTarget
#guard !fixtureCert.check fixtureTableLimit fixtureReferenceLimit
  fixtureStructureLimit baseProgram.length fixtureSources missingTarget

-- Existing structural references remain checked at this boundary even though
-- arithmetic replay is deferred.
private def badSourceFact : Fact :=
  ⟨⟨Experiment.Center.node 0, unitRange⟩, .source 1⟩

#guard !({ fixtureCert with facts := badSourceFact :: fixtureFacts.drop 1 }).check
  fixtureTableLimit fixtureReferenceLimit fixtureStructureLimit baseProgram.length
  fixtureSources fixtureTarget
#guard !({ fixtureCert with result := 10 }).check fixtureTableLimit
  fixtureReferenceLimit fixtureStructureLimit baseProgram.length fixtureSources
  fixtureTarget

private def wrongLiteralShape : Program :=
  [Prim.var 0, Prim.var 0] ++ fixtureCert.program.drop 2

private def wrongEdge : Experiment.Center.EqEdge :=
  { Experiment.Center.centerEdge with left := Experiment.Center.node 8 }

-- Every locally reimplemented structural rejection path has a rational-side
-- canary, including the exact 74-step structural budget.
#guard !({ fixtureCert with program := wrongLiteralShape }).check fixtureTableLimit
  fixtureReferenceLimit fixtureStructureLimit baseProgram.length fixtureSources fixtureTarget
#guard !({ fixtureCert with edges := [wrongEdge] }).check fixtureTableLimit
  fixtureReferenceLimit fixtureStructureLimit baseProgram.length fixtureSources fixtureTarget
#guard !({ fixtureCert with center :=
    { Experiment.Center.centerWitness with generation := 0 } }).check
  fixtureTableLimit fixtureReferenceLimit fixtureStructureLimit baseProgram.length
  fixtureSources fixtureTarget
#guard !({ fixtureCert with center :=
    { Experiment.Center.centerWitness with generation := 2 } }).check
  fixtureTableLimit fixtureReferenceLimit fixtureStructureLimit baseProgram.length
  fixtureSources fixtureTarget
#guard fixtureCert.check fixtureTableLimit fixtureReferenceLimit
  { fixtureStructureLimit with maxLookupSteps := 74 } baseProgram.length
  fixtureSources fixtureTarget
#guard !fixtureCert.check fixtureTableLimit fixtureReferenceLimit
  { fixtureStructureLimit with maxLookupSteps := 73 } baseProgram.length
  fixtureSources fixtureTarget

-- Changing canonical table values preserves the internal structural layer,
-- but cannot change the caller-owned meaning of the invocation boundary.
private def shapeOnlyTable : List Experiment.RationalTable.RawRat :=
  [⟨2, 1⟩, ⟨3, 1⟩, ⟨4, 1⟩, ⟨-5, 1⟩, ⟨6, 1⟩]

private def shapeOnlyCert : Certificate :=
  { fixtureCert with table := shapeOnlyTable }

private def shapeOnlySources : List ExpectedRow :=
  [⟨⟨Experiment.Center.node 0, unitRange⟩, ValueRange.closed ⟨2, 1⟩ ⟨3, 1⟩⟩]

private def shapeOnlyTarget : ExpectedRow :=
  ⟨⟨Experiment.Center.node 3, quarterRange⟩, ValueRange.closed ⟨2, 1⟩ ⟨6, 1⟩⟩

-- A certificate-chosen table cannot reinterpret the original caller boundary.
#guard !shapeOnlyCert.check fixtureTableLimit fixtureReferenceLimit
  fixtureStructureLimit baseProgram.length fixtureSources fixtureTarget
#guard shapeOnlyCert.check fixtureTableLimit fixtureReferenceLimit
  fixtureStructureLimit baseProgram.length shapeOnlySources shapeOnlyTarget
#guard (eraseCertificate shapeOnlyCert baseProgram.length shapeOnlySources shapeOnlyTarget
  fixtureStructureLimit) == fixtureProjection.skeleton

-- Literal sharing is retained by endpoint erasure, not merely literal
-- positions.  Reusing `one` for all three slots changes the skeleton.
private def repeatedLiteralProgram : Program :=
  [ .var 0, .lit one, .sub (Experiment.Center.node 1) (Experiment.Center.node 0),
    .mul (Experiment.Center.node 0) (Experiment.Center.node 2), .lit one,
    .sub (Experiment.Center.node 0) (Experiment.Center.node 4),
    .sq (Experiment.Center.node 5), .lit one,
    .sub (Experiment.Center.node 7) (Experiment.Center.node 6) ]

#guard eraseProgram repeatedLiteralProgram != fixtureProjection.skeleton.program

/-! ## Downstream kernel transparency -/

example : checkFixture = true := by
  decide +kernel

example : Experiment.RationalTable.Table.check fixtureTableLimit fixtureCert.table =
    .ready := by
  exact Certificate.table_ready_of_check checkFixture_eq_true

example : ∀ q ∈ fixtureCert.table, q.Canonical := by
  exact Certificate.table_canonical checkFixture_eq_true

example : fixtureSources.all (fun source => source.agrees fixtureCert.table) = true ∧
    fixtureTarget.agrees fixtureCert.table = true := by
  exact Certificate.boundary_agrees_of_check checkFixture_eq_true

example : checksProjection = true := by
  decide +kernel

end Hex.Interval.RationalCertificateConformance
