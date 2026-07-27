/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexInterval.Experiment.Center

@[expose] public section

/-!
# Centered-checker scaling fixtures

This module keeps the centered-product theorem, endpoints, source, target,
equality edge, and one-generation witness fixed while varying only the amount
and lookup shape of untrusted certificate data.  The builders are transparent
and Mathlib-free so later compiled and ordinary-kernel probes can consume the
same deterministic workloads.

The formulas below count exactly the indexed lookups charged by
`StructureLimit.maxLookupSteps`.  They do not count the separately bounded
whole-program and whole-table scans.
-/

namespace Hex.Interval.Experiment.Scale

open Hex.Interval.Experiment.Center

/-! ## Shared workload boundary -/

/-- A certificate together with the exact indexed-lookup budget expected by
the reference checker. -/
structure Workload where
  certificate : Certificate
  lookupSteps : Nat
  deriving DecidableEq

/-- Exact indexed list-constructor visits, separated by referenced table. -/
structure LookupCount where
  program : Nat := 0
  source : Nat := 0
  edge : Nat := 0
  prior : Nat := 0
  result : Nat := 0
  deriving DecidableEq, Repr

namespace LookupCount

/-- Componentwise sum of two lookup counts. -/
def add (left right : LookupCount) : LookupCount :=
  { program := left.program + right.program
    source := left.source + right.source
    edge := left.edge + right.edge
    prior := left.prior + right.prior
    result := left.result + right.result }

/-- Total charged constructors across every indexed table lookup. -/
def total (count : LookupCount) : Nat :=
  count.program + count.source + count.edge + count.prior + count.result

end LookupCount

/-- Separately charge the indexed lookups requested by one fact. -/
def factLookupCount? (programCount sourceCount edgeCount priorCount : Nat)
    (fact : Fact) : Option LookupCount :=
  match fact.derivation with
  | .source source => do
      let cost ← Fact.forwardDistance? sourceCount source
      pure { source := cost }
  | .lit => do
      let cost ← Fact.forwardDistance? programCount fact.row.node.index
      pure { program := cost }
  | .sub left right | .mul left right => do
      let programCost ← Fact.forwardDistance? programCount fact.row.node.index
      let leftCost ← Fact.reverseDistance? priorCount left
      let rightCost ← Fact.reverseDistance? priorCount right
      pure { program := programCost, prior := leftCost + rightCost }
  | .sq input => do
      let programCost ← Fact.forwardDistance? programCount fact.row.node.index
      let inputCost ← Fact.reverseDistance? priorCount input
      pure { program := programCost, prior := inputCost }
  | .transport edge input => do
      let edgeCost ← Fact.forwardDistance? edgeCount edge
      let inputCost ← Fact.reverseDistance? priorCount input
      pure { edge := edgeCost, prior := inputCost }

/-- Sum separated lookup counts over an original-order fact list. -/
def factLookupCounts? (programCount sourceCount edgeCount : Nat) :
    Nat → List Fact → Option LookupCount
  | _, [] => some {}
  | priorCount, fact :: tail => do
      let count ← factLookupCount? programCount sourceCount edgeCount priorCount fact
      let tailCount ← factLookupCounts? programCount sourceCount edgeCount
        (priorCount + 1) tail
      pure (count.add tailCount)

/-- Recompute the complete separated lookup count for a certificate. -/
def certificateLookupCounts? (certificate : Certificate) : Option LookupCount := do
  let resultCost ← Fact.forwardDistance? certificate.facts.length certificate.result
  let factCount ← factLookupCounts? certificate.program.length fixtureSources.length
    certificate.edges.length 0 certificate.facts
  pure { factCount with result := resultCost }

/-- Sum the indexed lookup costs of an original-order fact list. -/
def factLookupSteps? (programCount sourceCount edgeCount : Nat) :
    Nat → List Fact → Option Nat
  | _, [] => some 0
  | priorCount, fact :: tail => do
      let cost ← Fact.lookupCost? programCount sourceCount edgeCount priorCount fact
      let tailCost ← factLookupSteps? programCount sourceCount edgeCount
        (priorCount + 1) tail
      pure (cost + tailCost)

/-- Recompute the complete charged lookup budget, including selected-result
lookup, directly from a certificate. -/
def certificateLookupSteps? (certificate : Certificate) : Option Nat := do
  let resultCost ← Fact.forwardDistance? certificate.facts.length certificate.result
  let factCost ← factLookupSteps? certificate.program.length fixtureSources.length
    certificate.edges.length 0 certificate.facts
  pure (factCost + resultCost)

namespace Workload

/-- Exact structural limits for one generated workload, with only the lookup
budget supplied separately. -/
def limitAt (workload : Workload) (lookupSteps : Nat) : StructureLimit :=
  { maxNodes := workload.certificate.program.length
    maxSources := fixtureSources.length
    maxEdges := workload.certificate.edges.length
    maxFacts := workload.certificate.facts.length
    maxGeneration := 1
    maxLookupSteps := lookupSteps }

/-- Run the fixed caller-bound checker at a chosen lookup budget. -/
def checkAt (workload : Workload) (lookupSteps : Nat) : Bool :=
  workload.certificate.check fixtureLimit (workload.limitAt lookupSteps)
    baseProgram.length fixtureSources fixtureTarget

/-- The closed-form workload budget agrees with the checker cost model. -/
def costMatches (workload : Workload) : Bool :=
  certificateLookupSteps? workload.certificate == some workload.lookupSteps &&
    (certificateLookupCounts? workload.certificate).map LookupCount.total ==
      some workload.lookupSteps

/-- The workload is accepted at its exact claimed lookup budget. -/
def accepts (workload : Workload) : Bool :=
  workload.checkAt workload.lookupSteps

/-- A positive exact budget is rejected when reduced by one step. -/
def rejectsBelow (workload : Workload) : Bool :=
  match workload.lookupSteps with
  | 0 => false
  | lookupSteps + 1 => !(workload.checkAt lookupSteps)

/-- Combined Boolean canary used by the small representative fixtures. -/
def checksBoundary (workload : Workload) : Bool :=
  workload.costMatches && workload.accepts && workload.rejectsBelow

end Workload

/-- Recognize a successfully constructed workload and check its exact budget
boundary. -/
def checksSome : Option Workload → Bool
  | none => false
  | some workload => workload.checksBoundary

/-! ## Node-only scaling -/

/-- The original fixture's exact indexed-lookup budget. Appending dead program
nodes does not change it. -/
def deadLookupSteps : Nat := 74

/-- Append `count` unique square nodes.  The first new node is at index 9 and
squares node 8; every later node squares its immediate predecessor. -/
def squareTailFrom : Nat → Nat → List (Prim .real)
  | _, 0 => []
  | input, count + 1 => .sq (node input) :: squareTailFrom (input + 1) count

/-- Build a node-only workload with exactly `totalNodes` program nodes.
Requests below the nine-node centered fixture are rejected rather than
silently clamped. -/
def deadNodes? (totalNodes : Nat) : Option Workload :=
  if 9 ≤ totalNodes then
    some
      { certificate :=
          { fixtureCert with
            program := extendedProgram ++ squareTailFrom 8 (totalNodes - 9) }
        lookupSteps := deadLookupSteps }
  else
    none

/-! ## Fact-table scaling -/

/-- The first nine centered facts end at the generated form.  Scaling tails
replace the fixture's final transport while preserving that prefix exactly. -/
def centeredPrefix : List Fact := fixtureFacts.take 9

/-- An adjacent alternating transport chain with `count` new facts costs
`71 + 3 * count` indexed lookup steps: 62 for the common derivations, two per
transport, and `9 + count` for the selected final result. -/
def adjacentLookupSteps (count : Nat) : Nat := 71 + 3 * count

/-- Generate transports which alternate between the centered form and the
original product and always cite the immediately preceding fact. `input` is
the original-order index of that preceding fact. -/
def adjacentTailFrom : Nat → Bool → Nat → List Fact
  | _, _, 0 => []
  | input, atForm, count + 1 =>
      let output := if atForm then node 3 else node 8
      { row := ⟨output, quarterRange⟩
        derivation := .transport 0 input } ::
        adjacentTailFrom (input + 1) (!atForm) count

/-- Build an adjacent transport workload. A positive odd count is required so
the last alternating row is the caller-selected product target. -/
def adjacent? (count : Nat) : Option Workload :=
  if count % 2 == 1 then
    some
      { certificate :=
          { fixtureCert with
            facts := centeredPrefix ++ adjacentTailFrom 8 true count
            result := 8 + count }
        lookupSteps := adjacentLookupSteps count }
  else
    none

/-- A far-reference transport chain costs
`71 + count * (count + 5) / 2`: each new product fact cites the fixed form fact
at index 8, so reverse distance grows by one on every step. -/
def farLookupSteps (count : Nat) : Nat :=
  71 + count * (count + 5) / 2

/-- Generate repeated valid transports from the fixed centered-form fact at
index 8 to the product target. -/
def farTail : Nat → List Fact
  | 0 => []
  | count + 1 =>
      { row := ⟨node 3, quarterRange⟩
        derivation := .transport 0 8 } :: farTail count

/-- Build a far-reference workload. At least one new transport is required to
provide the selected product target after the nine-fact prefix. -/
def far? (count : Nat) : Option Workload :=
  if 0 < count then
    some
      { certificate :=
          { fixtureCert with
            facts := centeredPrefix ++ farTail count
            result := 8 + count }
        lookupSteps := farLookupSteps count }
  else
    none

/-- Appending `count` irrelevant source copies adds exactly one charged source
lookup per fact while leaving the selected result at fixture index 9. -/
def sourcePadLookupSteps (count : Nat) : Nat := 74 + count

/-- Generate valid but result-irrelevant copies of the caller-owned source
row. -/
def sourcePadTail : Nat → List Fact
  | 0 => []
  | count + 1 =>
      { row := ⟨node 0, unitRange⟩
        derivation := .source 0 } :: sourcePadTail count

/-- Build a workload whose irrelevant source rows occur after the selected
fixture result but are still validated by the checker. -/
def sourcePad (count : Nat) : Workload :=
  { certificate :=
      { fixtureCert with facts := fixtureFacts ++ sourcePadTail count }
    lookupSteps := sourcePadLookupSteps count }

end Hex.Interval.Experiment.Scale
