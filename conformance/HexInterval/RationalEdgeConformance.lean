/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import HexInterval.Experiment.RationalEdge

/-!
Compiled conformance for resource-preflighted rational arithmetic edges.
Ordinary-kernel examples exercise the transparent checker and every Core `Rat`
soundness theorem from a downstream module.
-/

namespace Hex.Interval.RationalEdgeConformance

open Experiment.RationalEdge

#guard checksEdges
#guard check fixtureTableLimit fixtureLimit fixtureTable fixtureEdges == .ready

-- Each caller-owned resource accepts its exact fixture boundary and rejects
-- one unit below it at the deterministic first edge that exhausts the budget.
#guard check fixtureTableLimit { fixtureLimit with maxEdges := 6 }
  fixtureTable fixtureEdges == .edgeResource none .edges
#guard check fixtureTableLimit { fixtureLimit with maxLookupSteps := 40 }
  fixtureTable fixtureEdges == .ready
#guard check fixtureTableLimit { fixtureLimit with maxLookupSteps := 39 }
  fixtureTable fixtureEdges == .edgeResource (some 6) .lookupSteps
#guard check fixtureTableLimit { fixtureLimit with maxTemporaryBits := 7 }
  fixtureTable fixtureEdges == .ready
#guard check fixtureTableLimit { fixtureLimit with maxTemporaryBits := 6 }
  fixtureTable fixtureEdges == .edgeResource (some 0) .temporaryBits
#guard check fixtureTableLimit { fixtureLimit with maxArithmeticWork := 130 }
  fixtureTable fixtureEdges == .ready
#guard check fixtureTableLimit { fixtureLimit with maxArithmeticWork := 129 }
  fixtureTable fixtureEdges == .edgeResource (some 6) .arithmeticWork

-- Zero-aware width formulas account for every declared intermediate.  In the
-- total inverse zero branch no cross-product or temporary is charged.
#guard (Resolved.add ⟨0, 1⟩ ⟨1, 2⟩ ⟨1, 2⟩).cost ==
  ({ temporaryBits := 4, arithmeticWork := 17 } : Cost)
#guard (Resolved.mul ⟨0, 1⟩ ⟨1, 2⟩ ⟨0, 1⟩).cost ==
  ({ temporaryBits := 3, arithmeticWork := 2 } : Cost)
#guard (Resolved.inv ⟨0, 1⟩ ⟨0, 1⟩).cost ==
  ({ temporaryBits := 0, arithmeticWork := 0 } : Cost)

private def zeroTable : List Experiment.RationalTable.RawRat := [⟨0, 1⟩]

private def zeroTableLimit : Experiment.RationalTable.RawRat.Limit :=
  { maxEntries := 1
    maxNumeratorBits := 0
    maxDenominatorBits := 1 }

private def zeroInvLimit : Limit :=
  { maxEdges := 1
    maxLookupSteps := 2
    maxTemporaryBits := 0
    maxArithmeticWork := 0 }

#guard check zeroTableLimit zeroInvLimit zeroTable [.inv 0 0] == .ready

-- No lookup defaults are accepted; inverse follows Core's total operation.
#guard check fixtureTableLimit fixtureLimit fixtureTable [.add 0 99 2] ==
  .malformedEdge 0 (.badIndex .right 99)
#guard check fixtureTableLimit fixtureLimit fixtureTable [.add 99 1 2] ==
  .malformedEdge 0 (.badIndex .left 99)
#guard check fixtureTableLimit fixtureLimit fixtureTable [.inv 99 4] ==
  .malformedEdge 0 (.badIndex .input 99)
#guard check fixtureTableLimit fixtureLimit fixtureTable [.add 0 1 99] ==
  .malformedEdge 0 (.badIndex .result 99)
#guard check fixtureTableLimit fixtureLimit (fixtureTable ++ [⟨0, 1⟩]) [.inv 5 5] ==
  .ready
#guard check fixtureTableLimit fixtureLimit (fixtureTable ++ [⟨0, 1⟩]) [.inv 5 4] ==
  .malformedEdge 0 .wrongIdentity
#guard check fixtureTableLimit fixtureLimit fixtureTable [.add 0 1 0] ==
  .malformedEdge 0 .wrongIdentity

-- Every operation tag rejects a false assertion.
#guard check fixtureTableLimit fixtureLimit fixtureTable [.sub 0 1 0] ==
  .malformedEdge 0 .wrongIdentity
#guard check fixtureTableLimit fixtureLimit fixtureTable [.mul 0 1 0] ==
  .malformedEdge 0 .wrongIdentity
#guard check fixtureTableLimit fixtureLimit fixtureTable [.inv 0 0] ==
  .malformedEdge 0 .wrongIdentity
#guard check fixtureTableLimit fixtureLimit fixtureTable [.eq 0 1] ==
  .malformedEdge 0 .wrongIdentity
#guard check fixtureTableLimit fixtureLimit fixtureTable [.le 0 1] ==
  .malformedEdge 0 .wrongIdentity
#guard check fixtureTableLimit fixtureLimit fixtureTable [.lt 0 1] ==
  .malformedEdge 0 .wrongIdentity

-- Zero arithmetic exercises zero-aware multiplication and sum widths.
#guard check fixtureTableLimit { fixtureLimit with maxLookupSteps := 41 }
  (fixtureTable ++ [⟨0, 1⟩])
  [.add 5 0 0, .sub 0 0 5, .mul 5 0 5, .inv 5 5] == .ready

-- Full-list preflight precedes replay: a bad later index is returned before an
-- earlier false cross-product is ever evaluated.
#guard check fixtureTableLimit fixtureLimit fixtureTable
  [.add 0 1 0, .mul 0 99 3] ==
    .malformedEdge 1 (.badIndex .right 99)

-- Successful table validation remains a prerequisite of all edge work.
#guard check fixtureTableLimit fixtureLimit
  ([⟨1, 2⟩, ⟨2, 6⟩] : List Experiment.RationalTable.RawRat)
  [] == .malformedTable 1 .notReduced
#guard check { fixtureTableLimit with maxEntries := 4 } fixtureLimit
  fixtureTable [] == .tableResource none .entries

private def signedTable : List Experiment.RationalTable.RawRat :=
  [⟨0, 1⟩, ⟨-2, 3⟩, ⟨-3, 2⟩, ⟨-1, 3⟩, ⟨-2, 3⟩]

private def signedTableLimit : Experiment.RationalTable.RawRat.Limit :=
  { maxEntries := 5
    maxNumeratorBits := 3
    maxDenominatorBits := 2 }

private def signedLimit : Limit :=
  { maxEdges := 5
    maxLookupSteps := 26
    maxTemporaryBits := 4
    maxArithmeticWork := 50 }

-- Negative inversion, equality, and both order relations use signed integer
-- cross-products with positive canonical denominators.
#guard check signedTableLimit signedLimit signedTable
  [.inv 1 2, .eq 1 4, .le 1 3, .lt 1 3, .inv 0 0] == .ready

private def half : Experiment.RationalTable.RawRat := ⟨1, 2⟩
private def third : Experiment.RationalTable.RawRat := ⟨1, 3⟩
private def fiveSixths : Experiment.RationalTable.RawRat := ⟨5, 6⟩
private def sixth : Experiment.RationalTable.RawRat := ⟨1, 6⟩
private def two : Experiment.RationalTable.RawRat := ⟨2, 1⟩
private def zero : Experiment.RationalTable.RawRat := ⟨0, 1⟩
private def negTwoThirds : Experiment.RationalTable.RawRat := ⟨-2, 3⟩
private def negThreeHalves : Experiment.RationalTable.RawRat := ⟨-3, 2⟩
private def negThird : Experiment.RationalTable.RawRat := ⟨-1, 3⟩

private theorem halfCanonical : half.Canonical :=
  Experiment.RationalTable.RawRat.canonical_of_check
    (limit := fixtureTableLimit) (by decide +kernel)

private theorem thirdCanonical : third.Canonical :=
  Experiment.RationalTable.RawRat.canonical_of_check
    (limit := fixtureTableLimit) (by decide +kernel)

private theorem fiveSixthsCanonical : fiveSixths.Canonical :=
  Experiment.RationalTable.RawRat.canonical_of_check
    (limit := fixtureTableLimit) (by decide +kernel)

private theorem sixthCanonical : sixth.Canonical :=
  Experiment.RationalTable.RawRat.canonical_of_check
    (limit := fixtureTableLimit) (by decide +kernel)

private theorem twoCanonical : two.Canonical :=
  Experiment.RationalTable.RawRat.canonical_of_check
    (limit := fixtureTableLimit) (by decide +kernel)

private theorem zeroCanonical : zero.Canonical :=
  Experiment.RationalTable.RawRat.canonical_of_check
    (limit := zeroTableLimit) (by decide +kernel)

private theorem negTwoThirdsCanonical : negTwoThirds.Canonical :=
  Experiment.RationalTable.RawRat.canonical_of_check
    (limit := signedTableLimit) (by decide +kernel)

private theorem negThreeHalvesCanonical : negThreeHalves.Canonical :=
  Experiment.RationalTable.RawRat.canonical_of_check
    (limit := signedTableLimit) (by decide +kernel)

private theorem negThirdCanonical : negThird.Canonical :=
  Experiment.RationalTable.RawRat.canonical_of_check
    (limit := signedTableLimit) (by decide +kernel)

-- These proofs invoke the public soundness API, rather than asking reduction
-- to normalize Core rational arithmetic as a test oracle.
example : fiveSixths.value = half.value + third.value := by
  exact Resolved.add_sound halfCanonical thirdCanonical
    fiveSixthsCanonical (by decide +kernel)

example : sixth.value = half.value - third.value := by
  exact Resolved.sub_sound halfCanonical thirdCanonical
    sixthCanonical (by decide +kernel)

example : sixth.value = half.value * third.value := by
  exact Resolved.mul_sound halfCanonical thirdCanonical
    sixthCanonical (by decide +kernel)

example : two.value = half.value⁻¹ := by
  exact Resolved.inv_sound halfCanonical twoCanonical
    (by decide +kernel)

example : zero.value = zero.value⁻¹ := by
  exact Resolved.inv_sound zeroCanonical zeroCanonical (by decide +kernel)

example : negThreeHalves.value = negTwoThirds.value⁻¹ := by
  exact Resolved.inv_sound negTwoThirdsCanonical negThreeHalvesCanonical
    (by decide +kernel)

example : sixth.value = sixth.value := by
  exact Resolved.eq_sound sixthCanonical sixthCanonical (by decide +kernel)

example : third.value ≤ half.value := by
  exact Resolved.le_sound thirdCanonical halfCanonical (by decide +kernel)

example : third.value < half.value := by
  exact Resolved.lt_sound thirdCanonical halfCanonical (by decide +kernel)

example : negTwoThirds.value = negTwoThirds.value := by
  exact Resolved.eq_sound negTwoThirdsCanonical negTwoThirdsCanonical
    (by decide +kernel)

example : negTwoThirds.value ≤ negThird.value := by
  exact Resolved.le_sound negTwoThirdsCanonical negThirdCanonical
    (by decide +kernel)

example : negTwoThirds.value < negThird.value := by
  exact Resolved.lt_sound negTwoThirdsCanonical negThirdCanonical
    (by decide +kernel)

-- A downstream consumer can turn public checker success directly into the
-- indexed edge's Core `Rat` proposition.
example : ArithEdge.Holds fixtureTable (.add 0 1 2) := by
  have hsound := sound_of_check
    (tableLimit := fixtureTableLimit) (edgeLimit := fixtureLimit)
    (table := fixtureTable) (edges := fixtureEdges) (by decide +kernel)
  exact hsound (.add 0 1 2) (by simp [fixtureEdges])

example : checksEdges = true := by
  decide +kernel

end Hex.Interval.RationalEdgeConformance
