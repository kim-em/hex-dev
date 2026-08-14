/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import HexInterval.Experiment.SinTenInterval
import HexInterval.Experiment.ProofFrontend
import HexInterval.Experiment.TargetRun

namespace Hex.Interval.SinTenIntervalConformance

open Hex.Interval.Experiment
open Propagator PolicySession ProofEmitter
open SinTenInterval

private def firstOffer : TargetRun.Controller Bound Unit :=
  { update := fun state _ => state
    choose := fun state view =>
      match view.offers[0]? with
      | some offer => .select offer state
      | none => .stop state }

private def reorderedView : ProgramView :=
  { programVersion := 0
    operations :=
      #[negationOperation, sourceOperation, sineOperation, piOperation,
        residualOperation]
    nodes :=
      #[{ sourceInstruction with op := { index := 1 } },
        { targetSineInstruction with op := { index := 2 } },
        { piInstruction with op := { index := 3 } },
        { residualInstruction with op := { index := 4 } },
        { localSineInstruction with op := { index := 2 } }]
    generations := #[0, 0, 0, 0, 0]
    depths := #[0, 1, 0, 1, 2] }

private def identityRequest (program : ProgramView) : RuleRequest Bound :=
  { action :=
      { serial := 0
        programVersion := program.programVersion
        application := { index := 0 }
        rule := { index := 0 }
        key := identityRuleKey
        node := node 3
        kind := .instantiate
        effort := 0
        inputs := [{ node := node 3, version := 1 }] }
    program
    inputs := [{ node := node 3, fact := residualFact, version := 1 }]
    writes := [] }

private def reorderedIdentityOp? : Option OpId :=
  match (identityPlan (identityRequest reorderedView)).outcome with
  | .success [] [.instantiate proposal] _ =>
      match proposal.nodes with
      | [proposed] => some proposed.op
      | _ => none
  | _ => none

#guard reorderedIdentityOp? == some { index := 0 }

private def missingNegationView : ProgramView :=
  { reorderedView with
    operations := #[sourceOperation, sineOperation, piOperation, residualOperation]
    nodes :=
      #[sourceInstruction, targetSineInstruction,
        { piInstruction with op := { index := 2 } },
        { residualInstruction with op := { index := 3 } }, localSineInstruction] }

#guard match (identityPlan (identityRequest missingNegationView)).outcome with
  | .noChange _ => true
  | _ => false

private def missingSineView : ProgramView :=
  { reorderedView with
    operations := #[negationOperation, sourceOperation, piOperation, residualOperation]
    nodes :=
      #[{ sourceInstruction with op := { index := 1 } },
        { targetSineInstruction with op := { index := 1 } },
        { piInstruction with op := { index := 2 } },
        { residualInstruction with op := { index := 3 } },
        { localSineInstruction with op := { index := 1 } }] }

#guard match (identityPlan (identityRequest missingSineView)).outcome with
  | .noChange _ => true
  | _ => false

private def malformedResidualView : ProgramView :=
  { reorderedView with
    nodes := reorderedView.nodes.set! 3
      { domain := real, op := { index := 4 }, args := [node 2, node 0] } }

#guard match (identityPlan (identityRequest malformedResidualView)).outcome with
  | .noChange _ => true
  | _ => false

private def malformedPiView : ProgramView :=
  { reorderedView with
    nodes := reorderedView.nodes.set! 2
      { domain := real, op := { index := 3 }, args := [node 0] }
    depths := reorderedView.depths.set! 2 1 }

#guard match (identityPlan (identityRequest malformedPiView)).outcome with
  | .noChange _ => true
  | _ => false

private def liveTrace? : Option (Frontend.Trace Bound) := do
  let .ok session := Session.start factDomain checkerInput.baseProgram
      packages checkerInput.initialFacts limits
    | none
  let result := TargetRun.drive factDomain checkerInput.target.node
    checkerInput.target.fact firstOffer limits.policy.maxDecisions session ()
  let .target _ := result.stop | none
  Frontend.trace? result.session.state.engine result.session.arena

private def exactInput (step : RuleStep Bound) (expected : List SeenVersion) : Bool :=
  match step.event.cause with
  | .rule action _ _ => action.inputs == expected
  | .transport _ _ => false

private def exactTransport (step : TransportStep Bound)
    (equality : EqualityId) (source : SeenVersion) : Bool :=
  match step.event.cause with
  | .transport actualEquality actualSource =>
      actualEquality == equality && actualSource == source
  | .rule _ _ _ => false

private def exactRule (step : RuleStep Bound) (expected : RuleKey) : Bool :=
  match step.event.cause with
  | .rule action _ _ => action.key == expected
  | .transport _ _ => false

#guard
  liveTrace?.any fun trace =>
    trace.program == extendedProgram &&
      match trace.events with
      | [.rule constant, .rule reduction, .rule localSine,
          .instantiation identity, .rule negation, .transport transport] =>
          identity.event.newNodes == [node 5] &&
            identity.event.newEqualities == [{ index := 0 }] &&
            identity.entry.body == [1] &&
            constant.event.node == node 2 && constant.event.fact == piFact &&
              constant.entry.body == [1] && exactRule constant constantRuleKey &&
              exactInput constant [] &&
            reduction.event.node == node 3 &&
              reduction.event.fact == residualFact && reduction.entry.body == [2] &&
              exactRule reduction reductionRuleKey &&
              exactInput reduction [{ node := node 0, version := 0 },
                { node := node 2, version := 1 }] &&
            localSine.event.node == node 4 &&
              localSine.event.fact == positiveFact && localSine.entry.body == [3] &&
              exactRule localSine localRuleKey &&
              exactInput localSine [{ node := node 3, version := 1 }] &&
            negation.event.node == node 5 &&
              negation.event.fact == negativeFact && negation.entry.body == [4] &&
              exactRule negation negationRuleKey &&
              exactInput negation [{ node := node 4, version := 1 }] &&
            transport.event.node == node 1 &&
              transport.event.fact == negativeFact && transport.entry.body == [1] &&
              exactTransport transport { index := 0 }
                { node := node 5, version := 1 }
      | _ => false

#guard Bound.code? (.interval
  { lower := rat 3 1, upper := rat 17 5,
    lowerOpen := true, upperOpen := true }) == none

#guard Bound.code? (.interval
  { lower := rat 3 1, upper := rat 16 5,
    lowerOpen := false, upperOpen := true }) == none

#guard !Bound.valid (.interval
  { lower := rat 3 0, upper := rat 16 5,
    lowerOpen := true, upperOpen := true })

#guard Bound.code? (.interval
  { lower := rat 3 0, upper := rat 16 5,
    lowerOpen := true, upperOpen := true }) == none

#guard match factDomain.narrow real positiveFact negativeFact with
  | .malformed 1 => true
  | _ => false

end Hex.Interval.SinTenIntervalConformance
