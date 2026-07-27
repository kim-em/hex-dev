/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexInterval.Experiment.RationalTable

@[expose] public section

/-!
# Table-indexed rational certificate boundary

This module adds the next proof-facing layer of the rational endpoint vertical.
Finite program literals and interval cuts refer to a complete, canonical
`RawRat` table by typed indices.  The transparent boundary checker validates
the whole table, every endpoint index, SSA and derivation indices, equality
references, caller-owned sources and target, and structural budgets.

No interval arithmetic or equality arithmetic is replayed here.  The module
also does not choose a wire format or a production storage representation;
`List` is the deliberately transparent proof-facing experiment boundary.
-/

namespace Hex.Interval.Experiment.RationalCertificate

open Center

/-! ## Table-indexed syntax -/

/-- Typed reference to one entry of the certificate's rational table. -/
structure EndpointId where
  index : Nat
  deriving DecidableEq, Repr

namespace EndpointId

/-- A reference is in range exactly when optional table lookup succeeds. -/
def valid (table : List RationalTable.RawRat) (endpoint : EndpointId) : Bool :=
  table[endpoint.index]?.isSome

/-- Exact forward-list lookup work for one endpoint reference.  This validates
the index without traversing the table. -/
def lookupCost? (tableCount : Nat) (endpoint : EndpointId) : Option Nat :=
  Center.Fact.forwardDistance? tableCount endpoint.index

end EndpointId

/-- Lower cut whose finite endpoint is a table reference. -/
inductive Lower where
  | unbounded
  | finite (endpoint : EndpointId) (strict : Bool)
  deriving DecidableEq, Repr

/-- Upper cut whose finite endpoint is a table reference. -/
inductive Upper where
  | finite (endpoint : EndpointId) (strict : Bool)
  | unbounded
  deriving DecidableEq, Repr

/-- Empty or bounded table-indexed interval data. -/
inductive Range where
  | empty
  | bounds (lower : Lower) (upper : Upper)
  deriving DecidableEq, Repr

namespace Lower

/-- Validate a lower cut's optional endpoint reference. -/
def refsOk (table : List RationalTable.RawRat) : Lower → Bool
  | .unbounded => true
  | .finite endpoint _ => endpoint.valid table

/-- Exact table lookup work requested by a lower cut. -/
def lookupCost? (tableCount : Nat) : Lower → Option Nat
  | .unbounded => some 0
  | .finite endpoint _ => endpoint.lookupCost? tableCount

end Lower

namespace Upper

/-- Validate an upper cut's optional endpoint reference. -/
def refsOk (table : List RationalTable.RawRat) : Upper → Bool
  | .finite endpoint _ => endpoint.valid table
  | .unbounded => true

/-- Exact table lookup work requested by an upper cut. -/
def lookupCost? (tableCount : Nat) : Upper → Option Nat
  | .finite endpoint _ => endpoint.lookupCost? tableCount
  | .unbounded => some 0

end Upper

namespace Range

/-- Closed finite range over two table entries. -/
def closed (lower upper : EndpointId) : Range :=
  .bounds (.finite lower false) (.finite upper false)

/-- Validate every finite endpoint reference in a range. -/
def refsOk (table : List RationalTable.RawRat) : Range → Bool
  | .empty => true
  | .bounds lower upper => lower.refsOk table && upper.refsOk table

/-- Exact table lookup work requested by every finite cut in a range. -/
def lookupCost? (tableCount : Nat) : Range → Option Nat
  | .empty => some 0
  | .bounds lower upper => do
      let lowerCost ← lower.lookupCost? tableCount
      let upperCost ← upper.lookupCost? tableCount
      pure (lowerCost + upperCost)

end Range

/-- Operations needed by the centered-product shape. -/
inductive Prim where
  | var (source : Nat)
  | lit (endpoint : EndpointId)
  | sub (left right : NodeId .real)
  | mul (left right : NodeId .real)
  | sq (input : NodeId .real)
  deriving DecidableEq, Repr

/-- Transparent proof-facing rational SSA program. -/
abbrev Program := List Prim

namespace Prim

/-- Check that every operand precedes the instruction defining its result. -/
def checkAt (index : Nat) : Prim → Bool
  | .var _ | .lit _ => true
  | .sub left right | .mul left right =>
      left.index < index && right.index < index
  | .sq input => input.index < index

/-- Validate a literal's table reference. -/
def refsOk (table : List RationalTable.RawRat) : Prim → Bool
  | .lit endpoint => endpoint.valid table
  | _ => true

/-- Exact table lookup work requested by an instruction. -/
def lookupCost? (tableCount : Nat) : Prim → Option Nat
  | .lit endpoint => endpoint.lookupCost? tableCount
  | _ => some 0

end Prim

namespace Program

/-- Exact optional program lookup. -/
def node? (program : Program) (node : NodeId .real) : Option Prim :=
  program[node.index]?

/-- Tail-recursive topology check from an explicit output position. -/
def checkFrom : Nat → Program → Bool
  | _, [] => true
  | index, instruction :: tail =>
      instruction.checkAt index && checkFrom (index + 1) tail

/-- Check complete SSA topology. -/
def check (program : Program) : Bool :=
  checkFrom 0 program

/-- Validate every literal reference in a complete program. -/
def refsOk (table : List RationalTable.RawRat) : Program → Bool
  | [] => true
  | instruction :: tail =>
      instruction.refsOk table && refsOk table tail

/-- Exact endpoint-table lookup work for every literal in a program. -/
def lookupCost? (tableCount : Nat) : Program → Option Nat
  | [] => some 0
  | instruction :: tail => do
      let headCost ← instruction.lookupCost? tableCount
      let tailCost ← lookupCost? tableCount tail
      pure (headCost + tailCost)

end Program

/-- One node and its table-indexed interval range. -/
structure Row where
  node : NodeId .real
  range : Range
  deriving DecidableEq, Repr

namespace Row

/-- Validate every endpoint reference in a row. -/
def refsOk (table : List RationalTable.RawRat) (row : Row) : Bool :=
  row.range.refsOk table

/-- Exact endpoint-table lookup work for one row. -/
def lookupCost? (tableCount : Nat) (row : Row) : Option Nat :=
  row.range.lookupCost? tableCount

/-- Singleton range for a rational literal reference. -/
def lit (node : NodeId .real) (endpoint : EndpointId) : Row :=
  ⟨node, Range.closed endpoint endpoint⟩

end Row

/-! ## Structural recipes and references -/

namespace CenterShape

/-- Check the centered recipe's complete expression shape while deliberately
leaving the three literal values to a later arithmetic layer. -/
def check (program : Program) (center : Center.Center) : Bool :=
  program.node? center.x == some (.var 0) &&
    (match program.node? center.one with | some (.lit _) => true | _ => false) &&
    program.node? center.gap == some (.sub center.one center.x) &&
    program.node? center.prod == some (.mul center.x center.gap) &&
    (match program.node? center.half with | some (.lit _) => true | _ => false) &&
    program.node? center.shift == some (.sub center.x center.half) &&
    program.node? center.square == some (.sq center.shift) &&
    (match program.node? center.quarter with | some (.lit _) => true | _ => false) &&
    program.node? center.form == some (.sub center.quarter center.square) &&
    center.boundary && center.generation == center.inferredGeneration

end CenterShape

namespace EqEdge

/-- Check one equality edge's selected structural recipe and endpoints. -/
def check (program : Program) (expectedBaseSize maxGeneration : Nat)
    (edge : Center.EqEdge) : Bool :=
  match edge.recipe with
  | .centerV1 center =>
      center.baseSize == expectedBaseSize && center.generation ≤ maxGeneration &&
        CenterShape.check program center && edge.left == center.prod &&
        edge.right == center.form

end EqEdge

/-- A table-indexed row paired with the existing derivation reference language. -/
structure Fact where
  row : Row
  derivation : Center.Derivation
  deriving DecidableEq

namespace Fact

/-- Lookup preserving original fact numbering in a newest-first accumulator. -/
def prior? (priorCount : Nat) (priorRev : List Row) (index : Nat) : Option Row :=
  if index < priorCount then priorRev[priorCount - (index + 1)]? else none

/-- Lookup work charged for one structural derivation check. -/
def lookupCost? (programCount sourceCount edgeCount priorCount : Nat)
    (fact : Fact) : Option Nat :=
  match fact.derivation with
  | .source source => Center.Fact.forwardDistance? sourceCount source
  | .lit => Center.Fact.forwardDistance? programCount fact.row.node.index
  | .sub left right | .mul left right => do
      let programCost ← Center.Fact.forwardDistance? programCount fact.row.node.index
      let leftCost ← Center.Fact.reverseDistance? priorCount left
      let rightCost ← Center.Fact.reverseDistance? priorCount right
      pure (programCost + leftCost + rightCost)
  | .sq input => do
      let programCost ← Center.Fact.forwardDistance? programCount fact.row.node.index
      let inputCost ← Center.Fact.reverseDistance? priorCount input
      pure (programCost + inputCost)
  | .transport edge input => do
      let edgeCost ← Center.Fact.forwardDistance? edgeCount edge
      let inputCost ← Center.Fact.reverseDistance? priorCount input
      pure (edgeCost + inputCost)

/-- Validate endpoint, node, source, edge, and prior-fact references without
replaying interval arithmetic.  Literal rows must use the program literal's
exact table entry as a closed singleton. -/
def check (table : List RationalTable.RawRat) (program : Program)
    (sources : List Row) (edges : List Center.EqEdge) (priorCount : Nat)
    (priorRev : List Row) (fact : Fact) : Bool :=
  fact.row.refsOk table &&
    match fact.derivation with
    | .source source => sources[source]? == some fact.row
    | .lit =>
        match program.node? fact.row.node with
        | some (.lit endpoint) => fact.row == Row.lit fact.row.node endpoint
        | _ => false
    | .sub left right =>
        match program.node? fact.row.node, prior? priorCount priorRev left,
            prior? priorCount priorRev right with
        | some (.sub leftNode rightNode), some leftRow, some rightRow =>
            leftRow.node == leftNode && rightRow.node == rightNode
        | _, _, _ => false
    | .mul left right =>
        match program.node? fact.row.node, prior? priorCount priorRev left,
            prior? priorCount priorRev right with
        | some (.mul leftNode rightNode), some leftRow, some rightRow =>
            leftRow.node == leftNode && rightRow.node == rightNode
        | _, _, _ => false
    | .sq input =>
        match program.node? fact.row.node, prior? priorCount priorRev input with
        | some (.sq inputNode), some inputRow => inputRow.node == inputNode
        | _, _ => false
    | .transport edge input =>
        match edges[edge]?, prior? priorCount priorRev input with
        | some equality, some inputRow =>
            inputRow.range == fact.row.range &&
              ((inputRow.node == equality.left && fact.row.node == equality.right) ||
                (inputRow.node == equality.right && fact.row.node == equality.left))
        | _, _ => false

end Fact

/-- Validate a complete fact list while charging every indexed lookup. -/
def checkFacts (table : List RationalTable.RawRat) (program : Program)
    (sources : List Row) (edges : List Center.EqEdge)
    (programCount sourceCount edgeCount : Nat) :
    Nat → Nat → List Fact → List Row → Bool
  | _, _, [], _ => true
  | priorCount, remainingSteps, fact :: tail, priorRev =>
      match Fact.lookupCost? programCount sourceCount edgeCount priorCount fact with
      | none => false
      | some cost =>
          if cost ≤ remainingSteps then
            fact.check table program sources edges priorCount priorRev &&
              checkFacts table program sources edges programCount sourceCount edgeCount
                (priorCount + 1) (remainingSteps - cost) tail (fact.row :: priorRev)
          else
            false

/-! ## Complete certificate boundary -/

/-- Exact endpoint-table lookup work for a row collection. -/
def rowsLookupCost? (tableCount : Nat) : List Row → Option Nat
  | [] => some 0
  | row :: tail => do
      let headCost ← row.lookupCost? tableCount
      let tailCost ← rowsLookupCost? tableCount tail
      pure (headCost + tailCost)

/-- Exact endpoint-table lookup work for every fact row. -/
def factsLookupCost? (tableCount : Nat) : List Fact → Option Nat
  | [] => some 0
  | fact :: tail => do
      let headCost ← fact.row.lookupCost? tableCount
      let tailCost ← factsLookupCost? tableCount tail
      pure (headCost + tailCost)

/-- Caller-owned budget for forward traversals of the rational endpoint table.
It is separate from structural derivation lookup work so backend-independent
structural limits remain comparable. -/
structure ReferenceLimit where
  maxEndpointLookupSteps : Nat
  deriving DecidableEq, Repr

/-- Complete rational endpoint certificate.  The table and all indexed syntax
are untrusted; invocation sources, target, base size, and limits remain caller
owned arguments to the checker. -/
structure Certificate where
  table : List RationalTable.RawRat
  program : Program
  center : Center.Center
  edges : List Center.EqEdge
  facts : List Fact
  result : Nat
  deriving DecidableEq

namespace Certificate

/-- Bounded structural preflight before table or indexed traversal. -/
def structureOk (certificate : Certificate) (limit : Center.StructureLimit)
    (expectedBaseSize : Nat) (expectedSources : List Row) : Bool :=
  certificate.center.generation ≤ limit.maxGeneration &&
    expectedBaseSize ≤ limit.maxNodes && certificate.result < limit.maxFacts &&
    Center.lengthWithin limit.maxNodes certificate.program &&
    Center.lengthWithin limit.maxSources expectedSources &&
    Center.lengthWithin limit.maxEdges certificate.edges &&
    Center.lengthWithin limit.maxFacts certificate.facts

/-- Exact forward-list work for every endpoint-table lookup the boundary will
perform.  Returning `none` rejects an out-of-range reference before any table
lookup is attempted. -/
def endpointLookupCost? (certificate : Certificate) (expectedSources : List Row)
    (expectedTarget : Row) : Option Nat := do
  let tableCount := certificate.table.length
  let programCost ← certificate.program.lookupCost? tableCount
  let sourceCost ← rowsLookupCost? tableCount expectedSources
  let targetCost ← expectedTarget.lookupCost? tableCount
  let factCost ← factsLookupCost? tableCount certificate.facts
  pure (programCost + sourceCost + targetCost + factCost)

/-- Check the complete table-indexed certificate boundary.  A successful
result establishes table canonicality and all structural references, but no
arithmetic equality or interval propagation claim. -/
def check (certificate : Certificate) (tableLimit : RationalTable.RawRat.Limit)
    (referenceLimit : ReferenceLimit) (structureLimit : Center.StructureLimit)
    (expectedBaseSize : Nat) (expectedSources : List Row)
    (expectedTarget : Row) : Bool :=
  certificate.structureOk structureLimit expectedBaseSize expectedSources &&
    match RationalTable.Table.check tableLimit certificate.table with
    | .ready =>
        match certificate.endpointLookupCost? expectedSources expectedTarget with
        | none => false
        | some endpointCost =>
            if endpointCost ≤ referenceLimit.maxEndpointLookupSteps then
              certificate.program.refsOk certificate.table &&
                certificate.program.check &&
                certificate.center.baseSize == expectedBaseSize &&
                CenterShape.check certificate.program certificate.center &&
                (expectedSources.all fun source =>
                  source.refsOk certificate.table &&
                    (certificate.program.node? source.node).isSome) &&
                expectedTarget.refsOk certificate.table &&
                (certificate.program.node? expectedTarget.node).isSome &&
                Center.EqEdge.containsCenter certificate.edges certificate.center &&
                certificate.edges.all
                  (EqEdge.check certificate.program expectedBaseSize
                    structureLimit.maxGeneration) &&
                match Center.Fact.forwardDistance? certificate.facts.length
                    certificate.result with
                | none => false
                | some resultCost =>
                    if resultCost ≤ structureLimit.maxLookupSteps then
                      checkFacts certificate.table certificate.program expectedSources
                          certificate.edges certificate.program.length
                          expectedSources.length certificate.edges.length 0
                          (structureLimit.maxLookupSteps - resultCost)
                          certificate.facts [] &&
                        certificate.facts[certificate.result]?.map
                            (fun fact => fact.row) == some expectedTarget
                    else
                      false
            else
              false
    | .malformed _ _ | .resourceLimit _ _ => false

/-- Success implies that the complete raw table passed validation. -/
theorem table_ready_of_check {certificate : Certificate}
    {tableLimit : RationalTable.RawRat.Limit}
    {referenceLimit : ReferenceLimit} {structureLimit : Center.StructureLimit}
    {expectedBaseSize : Nat} {expectedSources : List Row} {expectedTarget : Row}
    (h : certificate.check tableLimit referenceLimit structureLimit
      expectedBaseSize expectedSources expectedTarget = true) :
    RationalTable.Table.check tableLimit certificate.table = .ready := by
  unfold check at h
  cases htable : RationalTable.Table.check tableLimit certificate.table with
  | ready => rfl
  | malformed index reason => simp [htable] at h
  | resourceLimit index reason => simp [htable] at h

/-- Every entry of an accepted certificate table is canonical. -/
theorem table_canonical {certificate : Certificate}
    {tableLimit : RationalTable.RawRat.Limit}
    {referenceLimit : ReferenceLimit} {structureLimit : Center.StructureLimit}
    {expectedBaseSize : Nat} {expectedSources : List Row} {expectedTarget : Row}
    (h : certificate.check tableLimit referenceLimit structureLimit
      expectedBaseSize expectedSources expectedTarget = true) :
    ∀ q ∈ certificate.table, q.Canonical :=
  RationalTable.Table.canonical_of_check (table_ready_of_check h)

end Certificate

/-! ## Endpoint-erased projection -/

/-- Erase one rational program instruction.  A literal retains its program
position as the backend-independent literal slot. -/
def eraseOp (index : Nat) : Prim → RationalTable.Shape.Op
  | .var source => .var source
  | .lit _ => .lit index
  | .sub left right => .sub left right
  | .mul left right => .mul left right
  | .sq input => .sq input

/-- Erase a complete rational program from an explicit position. -/
def eraseProgramFrom : Nat → Program → List RationalTable.Shape.Op
  | _, [] => []
  | index, instruction :: tail =>
      eraseOp index instruction :: eraseProgramFrom (index + 1) tail

/-- Endpoint-erased rational program. -/
def eraseProgram (program : Program) : List RationalTable.Shape.Op :=
  eraseProgramFrom 0 program

/-- Erase a lower cut's table reference while retaining strictness. -/
def eraseLower : Lower → RationalTable.Shape.Lower
  | .unbounded => .unbounded
  | .finite _ strict => .finite strict

/-- Erase an upper cut's table reference while retaining strictness. -/
def eraseUpper : Upper → RationalTable.Shape.Upper
  | .finite _ strict => .finite strict
  | .unbounded => .unbounded

/-- Erase table references while retaining every interval shape. -/
def eraseRange : Range → RationalTable.Shape.Range
  | .empty => .empty
  | .bounds lower upper => .bounds (eraseLower lower) (eraseUpper upper)

/-- Erase one rational row. -/
def eraseRow (row : Row) : RationalTable.Shape.Row :=
  ⟨row.node, eraseRange row.range⟩

/-- Erase one rational fact without changing its derivation references. -/
def eraseFact (fact : Fact) : RationalTable.Shape.Fact :=
  ⟨eraseRow fact.row, fact.derivation⟩

/-- Backend-independent certificate skeleton. -/
def eraseCertificate (certificate : Certificate) (baseSize : Nat)
    (sources : List Row) (target : Row) (limit : Center.StructureLimit) :
    RationalTable.Shape.Skeleton :=
  { program := eraseProgram certificate.program
    center := certificate.center
    edges := certificate.edges
    facts := certificate.facts.map eraseFact
    result := certificate.result
    baseSize
    sources := sources.map eraseRow
    target := eraseRow target
    limit }

/-- Rational projection retains its caller-owned table and endpoint-reference
limits alongside the backend-independent skeleton. -/
structure Projection where
  skeleton : RationalTable.Shape.Skeleton
  tableLimit : RationalTable.RawRat.Limit
  referenceLimit : ReferenceLimit
  deriving DecidableEq

/-- Project a rational certificate and its complete caller-owned boundary. -/
def projectCertificate (certificate : Certificate)
    (tableLimit : RationalTable.RawRat.Limit) (referenceLimit : ReferenceLimit)
    (baseSize : Nat) (sources : List Row) (target : Row)
    (structureLimit : Center.StructureLimit) : Projection :=
  { skeleton := eraseCertificate certificate baseSize sources target structureLimit
    tableLimit
    referenceLimit }

/-! ## Fixed rational rendering of the centered fixture -/

def endpoint (index : Nat) : EndpointId := ⟨index⟩

def zero : EndpointId := endpoint 0
def one : EndpointId := endpoint 1
def half : EndpointId := endpoint 2
def negHalf : EndpointId := endpoint 3
def quarter : EndpointId := endpoint 4

/-- Canonical values used by the rational centered fixture. -/
def fixtureTable : List RationalTable.RawRat :=
  [⟨0, 1⟩, ⟨1, 1⟩, ⟨1, 2⟩, ⟨-1, 2⟩, ⟨1, 4⟩]

/-- Rational-table rendering of the four-node source program. -/
def baseProgram : Program :=
  [.var 0, .lit one, .sub (Center.node 1) (Center.node 0),
    .mul (Center.node 0) (Center.node 2)]

/-- Rational-table rendering of the complete nine-node program. -/
def extendedProgram : Program :=
  baseProgram ++
    [.lit half, .sub (Center.node 0) (Center.node 4), .sq (Center.node 5),
      .lit quarter, .sub (Center.node 7) (Center.node 6)]

def unitRange : Range := Range.closed zero one
def centeredRange : Range := Range.closed negHalf half
def quarterRange : Range := Range.closed zero quarter

/-- Rational-table rendering of all ten centered fixture facts. -/
def fixtureFacts : List Fact :=
  [ ⟨⟨Center.node 0, unitRange⟩, .source 0⟩
  , ⟨Row.lit (Center.node 1) one, .lit⟩
  , ⟨⟨Center.node 2, unitRange⟩, .sub 1 0⟩
  , ⟨⟨Center.node 3, unitRange⟩, .mul 0 2⟩
  , ⟨Row.lit (Center.node 4) half, .lit⟩
  , ⟨⟨Center.node 5, centeredRange⟩, .sub 0 4⟩
  , ⟨⟨Center.node 6, quarterRange⟩, .sq 5⟩
  , ⟨Row.lit (Center.node 7) quarter, .lit⟩
  , ⟨⟨Center.node 8, quarterRange⟩, .sub 7 6⟩
  , ⟨⟨Center.node 3, quarterRange⟩, .transport 0 8⟩ ]

/-- Complete table-indexed centered certificate. -/
def fixtureCert : Certificate :=
  { table := fixtureTable
    program := extendedProgram
    center := Center.centerWitness
    edges := [Center.centerEdge]
    facts := fixtureFacts
    result := 9 }

/-- Caller-owned rational source rows. -/
def fixtureSources : List Row :=
  [⟨Center.node 0, unitRange⟩]

/-- Caller-owned rational target row. -/
def fixtureTarget : Row :=
  ⟨Center.node 3, quarterRange⟩

/-- Caller-owned table limit for the fixed rational certificate. -/
def fixtureTableLimit : RationalTable.RawRat.Limit :=
  RationalTable.fixtureTableLimit

/-- Exact caller-owned budget for all endpoint-table traversals in the fixed
rational certificate boundary. -/
def fixtureReferenceLimit : ReferenceLimit :=
  { maxEndpointLookupSteps := 73 }

/-- Structural boundary shared exactly with the centered dyadic fixture. -/
def fixtureStructureLimit : Center.StructureLimit :=
  Center.fixtureStructureLimit

/-- Transparent checker canary for the complete rational boundary. -/
def checkFixture : Bool :=
  fixtureCert.check fixtureTableLimit fixtureReferenceLimit fixtureStructureLimit
    baseProgram.length fixtureSources fixtureTarget

theorem checkFixture_eq_true : checkFixture = true := by
  decide +kernel

/-- Complete rational projection of the fixed certificate. -/
def fixtureProjection : Projection :=
  projectCertificate fixtureCert fixtureTableLimit fixtureReferenceLimit
    baseProgram.length fixtureSources fixtureTarget fixtureStructureLimit

/-- The table-indexed rational and dyadic certificates have exactly the same
backend-independent structure. -/
def checksProjection : Bool :=
  fixtureProjection.skeleton == RationalTable.fixtureSkeleton &&
    fixtureProjection.skeleton == RationalTable.expectedSkeleton &&
    fixtureProjection.tableLimit == fixtureTableLimit &&
    fixtureProjection.referenceLimit == fixtureReferenceLimit

theorem checksProjection_eq_true : checksProjection = true := by
  decide +kernel

/-- The fixture's endpoint-reference budget is exact and one step short is
rejected before any endpoint-table traversal. -/
def checksReferenceBudget : Bool :=
  fixtureCert.endpointLookupCost? fixtureSources fixtureTarget == some 73 &&
    checkFixture &&
    !fixtureCert.check fixtureTableLimit
      { fixtureReferenceLimit with maxEndpointLookupSteps := 72 }
      fixtureStructureLimit baseProgram.length fixtureSources fixtureTarget

theorem checksReferenceBudget_eq_true : checksReferenceBudget = true := by
  decide +kernel

/-- Boundary canaries for invalid indices and an invalid unused table entry. -/
def rejectsBadBoundary : Bool :=
  let missing := endpoint fixtureTable.length
  let roomy : RationalTable.RawRat.Limit :=
    { fixtureTableLimit with maxEntries := fixtureTableLimit.maxEntries + 1 }
  !({ fixtureCert with program :=
        [Prim.var 0, Prim.lit missing] ++ fixtureCert.program.drop 2 }).check
      fixtureTableLimit fixtureReferenceLimit fixtureStructureLimit
      baseProgram.length fixtureSources fixtureTarget &&
    !({ fixtureCert with facts :=
        (⟨⟨Center.node 0, Range.closed zero missing⟩, .source 0⟩ : Fact) ::
          fixtureFacts.drop 1 }).check fixtureTableLimit fixtureReferenceLimit
      fixtureStructureLimit baseProgram.length fixtureSources fixtureTarget &&
    !({ fixtureCert with table :=
        fixtureTable ++ [RationalTable.RawRat.mk 0 7] }).check roomy
      fixtureReferenceLimit fixtureStructureLimit baseProgram.length fixtureSources
      fixtureTarget

theorem rejectsBadBoundary_eq_true : rejectsBadBoundary = true := by
  decide +kernel

end Hex.Interval.Experiment.RationalCertificate
