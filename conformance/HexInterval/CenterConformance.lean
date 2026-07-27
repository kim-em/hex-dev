/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import HexInterval.Experiment.Center

/-!
Adversarial conformance checks for the provisional centered-product replay
certificate. Each malformed value is checked through the complete public
certificate boundary.
-/

namespace Hex.Interval.CenterConformance

open Experiment.Center

private def accepts (certificate : Certificate) : Bool :=
  certificate.check fixtureLimit fixtureStructureLimit baseProgram.length
    fixtureSources fixtureTarget

private def withProgram (program : Program) : Certificate :=
  { fixtureCert with program := program }

private def withCenter (center : Experiment.Center.Center) : Certificate :=
  { fixtureCert with center := center }

private def withFacts (facts : List Fact) : Certificate :=
  { fixtureCert with facts := facts }

private def acceptsSource (range : Raw) : Bool :=
  fixtureCert.check fixtureLimit fixtureStructureLimit baseProgram.length
    [⟨node 0, range⟩] fixtureTarget

private def acceptsWithin (limit : StructureLimit) : Bool :=
  fixtureCert.check fixtureLimit limit baseProgram.length fixtureSources fixtureTarget

-- The committed nine-node program, centered edge, propagation trace, and
-- transported result are accepted together.
#guard accepts fixtureCert

-- Sources and the expected target are trusted arguments rather than
-- certificate fields.  A certificate cannot manufacture a source node, name
-- a nonexistent target node, or select a different fact as its result.
private def nonexistentSource : List Row :=
  [⟨node 99, unitRange⟩]

private def nonexistentTarget : Row :=
  ⟨node 99, quarterRange⟩

private def wrongSelectedResult : Certificate :=
  { fixtureCert with result := 0 }

#guard !fixtureCert.check fixtureLimit fixtureStructureLimit baseProgram.length
  nonexistentSource fixtureTarget
#guard !fixtureCert.check fixtureLimit fixtureStructureLimit baseProgram.length
  fixtureSources nonexistentTarget
#guard !wrongSelectedResult.check fixtureLimit fixtureStructureLimit
  baseProgram.length fixtureSources fixtureTarget

-- Every trusted collection/depth cap is independently active.  The complete
-- replay consumes exactly 74 charged list constructors, so 73 rejects.
#guard !acceptsWithin { fixtureStructureLimit with maxNodes := 8 }
#guard !acceptsWithin { fixtureStructureLimit with maxSources := 0 }
#guard !acceptsWithin { fixtureStructureLimit with maxEdges := 0 }
#guard !acceptsWithin { fixtureStructureLimit with maxFacts := 9 }
#guard !acceptsWithin { fixtureStructureLimit with maxGeneration := 0 }
#guard !acceptsWithin { fixtureStructureLimit with maxLookupSteps := 73 }

-- SSA topology rejects both a reference to a later node and a reference
-- outside the program.
private def forwardProgram : Program :=
  extendedProgram.set 2 (.sub (node 1) (node 4))

private def danglingProgram : Program :=
  extendedProgram.set 8 (.sub (node 7) (node 99))

#guard !accepts (withProgram forwardProgram)
#guard !accepts (withProgram danglingProgram)

-- The base/generated boundary is checked independently of the claimed
-- generation, and the generation is recomputed rather than trusted.
#guard !accepts (withCenter { centerWitness with baseSize := 5 })
#guard !accepts (withCenter { centerWitness with generation := 0 })
#guard !accepts (withCenter { centerWitness with generation := 2 })

-- Appending a second complete centered-product pattern cannot move the
-- caller's generation-zero boundary.  The shifted witness is locally
-- coherent and claims generation one relative to its forged base size, but
-- the trusted base remains `baseProgram.length`.
private def shiftedPatternProgram : Program :=
  extendedProgram ++
    [ .var 0
    , .lit 1
    , .sub (node 10) (node 9)
    , .mul (node 9) (node 11)
    , .lit half
    , .sub (node 9) (node 13)
    , .sq (node 14)
    , .lit quarter
    , .sub (node 16) (node 15) ]

private def shiftedCenter : Experiment.Center.Center :=
  { x := node 9
    one := node 10
    gap := node 11
    prod := node 12
    half := node 13
    shift := node 14
    square := node 15
    quarter := node 16
    form := node 17
    baseSize := 13
    generation := 1 }

private def shiftedCertificate : Certificate :=
  { fixtureCert with
    program := shiftedPatternProgram
    center := shiftedCenter
    edges := [EqEdge.ofCenter shiftedCenter] }

private def shiftedNodeLimit : StructureLimit :=
  { fixtureStructureLimit with maxNodes := 18 }

#guard !shiftedCertificate.check fixtureLimit shiftedNodeLimit
  baseProgram.length fixtureSources fixtureTarget

-- The selected center must contribute its exact edge.  Here both the
-- selected alternate center and the original edge are independently valid
-- for the same trusted base, but they are unrelated to one another.
private def alternateCenterProgram : Program :=
  extendedProgram ++
    [ .lit half
    , .sub (node 0) (node 9)
    , .sq (node 10)
    , .lit quarter
    , .sub (node 12) (node 11) ]

private def alternateCenter : Experiment.Center.Center :=
  { x := node 0
    one := node 1
    gap := node 2
    prod := node 3
    half := node 9
    shift := node 10
    square := node 11
    quarter := node 12
    form := node 13
    baseSize := baseProgram.length
    generation := 1 }

private def unrelatedCenterCertificate : Certificate :=
  { fixtureCert with
    program := alternateCenterProgram
    center := alternateCenter }

private def alternateNodeLimit : StructureLimit :=
  { fixtureStructureLimit with maxNodes := 14 }

#guard !unrelatedCenterCertificate.check fixtureLimit alternateNodeLimit
  baseProgram.length fixtureSources fixtureTarget

-- Both exact centered constants and the square instruction shape are pinned
-- by `EqRecipe.centerV1`.
private def wrongHalf : Program :=
  extendedProgram.set 4 (.lit (Dyadic.ofIntWithPrec 3 2))

private def wrongSquare : Program :=
  extendedProgram.set 6 (.mul (node 5) (node 5))

#guard !accepts (withProgram wrongHalf)
#guard !accepts (withProgram wrongSquare)

-- Whole-program literal preflight covers dead nodes as well as nodes reached
-- by the selected recipe or derivation.
private def oversizedLiteral : Dyadic :=
  .ofOdd 1 1000000000 (by decide)

private def unusedOversizedLiteral : Certificate :=
  { fixtureCert with program := extendedProgram ++ [.lit oversizedLiteral] }

private def tenNodeLimit : StructureLimit :=
  { fixtureStructureLimit with maxNodes := 10 }

#guard !unusedOversizedLiteral.check fixtureLimit tenNodeLimit
  baseProgram.length fixtureSources fixtureTarget

-- An equality recipe cannot be attached to different endpoints.
private def wrongEdge : EqEdge :=
  { centerEdge with left := node 0 }

#guard !accepts { fixtureCert with edges := [wrongEdge] }

-- Transport must cross the checked edge and must preserve the exact range.
private def sameEndpointMove : Fact :=
  ⟨⟨node 3, unitRange⟩, .transport 0 3⟩

private def changedRangeMove : Fact :=
  ⟨⟨node 3, unitRange⟩, .transport 0 8⟩

#guard !accepts (withFacts (fixtureFacts.set 9 sameEndpointMove))
#guard !accepts (withFacts (fixtureFacts.set 9 changedRangeMove))

-- Fact references and claimed nodes are checked against both prior rows and
-- the operation stored at the program node.
private def danglingFact : Fact :=
  ⟨⟨node 2, unitRange⟩, .sub 99 0⟩

private def wrongFactNode : Fact :=
  ⟨⟨node 8, unitRange⟩, .sub 1 0⟩

private def wrongSubOutput : Fact :=
  ⟨⟨node 2, quarterRange⟩, .sub 1 0⟩

private def wrongMulOutput : Fact :=
  ⟨⟨node 3, quarterRange⟩, .mul 0 2⟩

private def wrongSqOutput : Fact :=
  ⟨⟨node 6, unitRange⟩, .sq 5⟩

#guard !accepts (withFacts (fixtureFacts.set 2 danglingFact))
#guard !accepts (withFacts (fixtureFacts.set 2 wrongFactNode))
#guard !accepts (withFacts (fixtureFacts.set 2 wrongSubOutput))
#guard !accepts (withFacts (fixtureFacts.set 3 wrongMulOutput))
#guard !accepts (withFacts (fixtureFacts.set 6 wrongSqOutput))

-- Every source range crosses finite-closed normalization and resource
-- preflight before it can become a fact.
private def openRange : Raw :=
  .bounds (.finite 0 true) (.finite 1 false)

private def unboundedRange : Raw :=
  .bounds .unbounded (.finite 1 false)

#guard !acceptsSource .empty
#guard !acceptsSource openRange
#guard !acceptsSource unboundedRange
#guard !acceptsSource (closed 1 0)

-- Compact huge exponents cannot bypass either endpoint-height or alignment
-- budgets. The second case permits the endpoint heights but rejects before
-- exact comparison can allocate a billion-bit alignment shift.
private def far : Dyadic := .ofOdd 1 1000000000 (by decide)

#guard !acceptsSource (closed far far)

private def shiftLimit : EndpointLimit :=
  { maxEndpointHeight := 1000000100
    maxAlignmentShift := 8 }

private def farRange : Raw := closed far 1

#guard !fixtureCert.check shiftLimit fixtureStructureLimit baseProgram.length
  [⟨node 0, farRange⟩] fixtureTarget

end Hex.Interval.CenterConformance
