/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import HexIntervalMathlib.Experiment.Centered
import HexInterval.Experiment.PayloadSession
import HexInterval.Experiment.ProofEmitter

/-!
# Centered arbitrary-function replay conformance

The live session below contains only the centered package. Arithmetic
signatures are present because the package's structural matcher requires them,
but no arithmetic handler or proof schema participates in the forward rule.
-/

namespace Hex.IntervalMathlib.CenteredConformance

open Hex.Interval Hex.Interval.Experiment
open Propagator PayloadArena PayloadSession SemanticReplay ChronologicalReplay ProofEmitter
open DyadicInterval DyadicRules Centered

private def real : DomainId := { index := 0 }
private def sourceKey : OpKey := { name := "centered-conformance.source" }

private def operations : Array Operation :=
  ((arithmeticOperations real).push
    { key := sourceKey, inputs := [], output := real }).push
      { key := centeredOp, inputs := [real], output := real }

private def sourceInstruction : Node :=
  { domain := real, op := { index := 6 }, args := [] }

private def centeredInstruction : Node :=
  { domain := real, op := { index := 7 }, args := [{ index := 0 }] }

private def program : Program :=
  { operations, nodes := #[sourceInstruction, centeredInstruction] }

private def config : Config :=
  { endpointLimit := Centered.endpointLimit
    reciprocalBasePrecision := 2
    maxReciprocalEffort := 0 }

private def limits : Propagator.Limits :=
  { maxOperations := 16
    maxNodes := 8
    maxRules := 8
    maxRegistryEntries := 16
    maxReplayFormats := 8
    maxArity := 2
    maxApplications := 16
    maxQueueEntries := 32
    maxActions := 16
    maxAcceptedFacts := 8
    maxRetainedSuggestions := 8
    maxEffort := 0
    maxObservationValue := 32
    maxDiagnosticValue := 300
    maxOutcomeCandidates := 2
    maxOutcomeSuggestions := 2
    maxProposalItems := 4
    maxInstances := 0
    maxGeneration := 0
    maxNodeDepth := 4
    maxEqualities := 0
    splitEndpointLimit := Centered.endpointLimit }

private def arenaLimits : PayloadArena.Limits :=
  { maxEntries := PayloadSession.requiredUses limits
    maxBodyCells := 0
    maxDrafts := PayloadSession.requiredUses limits
    maxDraftCells := 0
    maxAtom := 0
    maxSchema := 0
    maxUses := PayloadSession.requiredUses limits }

private def session? : Option (PayloadSession.Session DyadicInterval.Fact) :=
  match PayloadSession.Session.start
      (DyadicInterval.factDomain Centered.endpointLimit) program
      #[centeredPackage config real] #[unitRange, .whole]
      limits arenaLimits with
  | .ok session => some session
  | .error _ => none

private def run? : Option (PayloadSession.Run DyadicInterval.Fact) := do
  let session ← session?
  pure (session.drive 8)

private def node (index : Nat) : NodeId := { index }
private def payload (index : Nat) : PayloadId := { index }

private def action : Action :=
  { serial := 0
    programVersion := 0
    application := { index := 0 }
    rule := { index := 0 }
    key := centeredForwardKey
    node := node 1
    kind := .forward
    effort := 0
    generation := 0
    inputs := [{ node := node 0, version := 0 }]
    writes := [node 1] }

private def event : FactEvent DyadicInterval.Fact :=
  { programVersion := 0
    node := node 1
    previous := { node := node 1, version := 0 }
    fact := quarterRange
    version := 1
    cause := .rule action quarterRange (payload 0) }

private def entry : Entry :=
  { origin := action
    role := .fact
    schema := 0
    body := [] }

private def step : RuleStep DyadicInterval.Fact :=
  { event
    payload := payload 0
    entry
    assumptions := [{ node := node 0, fact := unitRange }]
    previous := .whole }

private def sameEntry (left right : Entry) : Bool :=
  left.origin == right.origin && left.role == right.role &&
    left.schema == right.schema && left.body == right.body

private def sameEvent (left right : FactEvent DyadicInterval.Fact) : Bool :=
  left.programVersion == right.programVersion && left.node == right.node &&
    left.previous == right.previous && left.fact == right.fact &&
    left.version == right.version &&
      match left.cause, right.cause with
      | .rule leftAction leftFact leftPayload,
          .rule rightAction rightFact rightPayload =>
          leftAction == rightAction && leftFact == rightFact &&
            leftPayload == rightPayload
      | .transport leftEquality leftSource,
          .transport rightEquality rightSource =>
          leftEquality == rightEquality && leftSource == rightSource
      | _, _ => false

private def quotesMatchLive : Bool :=
  match run? with
  | some run =>
      run.stop == .saturated && run.session.complete &&
        run.session.engine.history.size == 1 &&
        run.session.arena.entries.size == 1 &&
        run.session.arena.bodyCells == 0 &&
        run.session.engine.factAt? { node := node 1, version := 1 } ==
          some quarterRange &&
        match run.session.engine.history[0]?,
            run.session.arena.entry? (payload 0) .fact with
        | some actualEvent, some actualEntry =>
            sameEvent actualEvent event && sameEntry actualEntry entry
        | _, _ => false
  | none => false

#guard quotesMatchLive

private def checkerInput : CheckerInput DyadicInterval.Fact :=
  { baseProgram := program
    initialFacts := #[unitRange, .whole]
    target := { node := node 1, fact := quarterRange } }

private def base : List (NodeFact DyadicInterval.Fact) :=
  [{ node := node 0, fact := unitRange }, { node := node 1, fact := .whole }]

private def inputSound : Evidence
    (Centered.semantics.Entails program base
      { node := node 0, fact := unitRange }) :=
  ProofEmitter.assumed (by simp [base])

private def previousSound : Evidence
    (Centered.semantics.Entails program base
      { node := node 1, fact := step.previous }) := by
  apply ProofEmitter.assumed
  simp [step, base]

private def assumptionsSound : Evidence
    (InputsSound Centered.semantics program base step.assumptions) := by
  simpa [step, event] using (EntailsList.singleton inputSound)

private def replayed :=
  ProofEmitter.replayRule Centered.centeredFactSchema Centered.domain
    checkerInput program (ProgramPrefix.refl program) base step
    previousSound assumptionsSound

#guard replayed.isSome

private def malformed : RuleStep DyadicInterval.Fact :=
  { step with assumptions := [{ node := node 0, fact := .whole }] }

private def malformedAssumptions : Evidence
    (InputsSound Centered.semantics program base malformed.assumptions) := by
  simpa [malformed, step, event] using
    (EntailsList.singleton
      (ProofEmitter.closeFact Centered.domain program base (node 0)
        unitRange .whole inputSound |>.get (by rfl)))

private def rejected :=
  ProofEmitter.replayRule Centered.centeredFactSchema Centered.domain
    checkerInput program (ProgramPrefix.refl program) base malformed
    (by simpa [malformed, step, event] using previousSound) malformedAssumptions

#guard rejected.isNone

/-- The centered function's package-owned schema, rather than a generic
function case, turns the live rule quote into an ordinary kernel theorem. -/
theorem emittedCentered :
    Centered.semantics.Entails program base checkerInput.target := by
  exact ProofEmitter.proofOfReplay replayed (by rfl)

private noncomputable def valuation (x : ℝ) : NodeId → ℝ
  | ⟨0⟩ => x
  | ⟨1⟩ => (1 / 4 : ℝ) - (x - (1 / 2 : ℝ)) ^ 2
  | _ => 0

private theorem models (x : ℝ) : Centered.Models program (valuation x) := by
  intro output instruction found operation operationFound key
  rcases output with ⟨index⟩
  cases index with
  | zero =>
      simp [Program.node?, program, sourceInstruction] at found
      subst instruction
      simp [Program.operation?, program, operations, arithmeticOperations,
        sourceKey, centeredOp] at operationFound
      subst operation
      simp [centeredOp] at key
  | succ index =>
      cases index with
      | zero =>
          simp [Program.node?, program, centeredInstruction] at found
          subst instruction
          refine ⟨node 0, rfl, ?_⟩
          simp [node, valuation]
      | succ index =>
          simp [Program.node?, program] at found

/-- End-to-end arbitrary-function example. The only function-specific step is
the centered package's semantic schema; generic replay handles its fact event. -/
theorem tacticCentered (x : ℝ) (nonnegative : 0 ≤ x) (atMostOne : x ≤ 1) :
    0 ≤ (1 / 4 : ℝ) - (x - (1 / 2 : ℝ)) ^ 2 ∧
      (1 / 4 : ℝ) - (x - (1 / 2 : ℝ)) ^ 2 ≤ 1 / 4 := by
  have result := emittedCentered (valuation x) (models x) (by
    intro assumption member
    simp only [base, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl
    · change unitRange.Contains (valuation x (node 0))
      simpa only [unitRange, DyadicInterval.Fact.Contains, rawContains,
        lowerContains, upperContains, DyadicInterval.toReal_zero,
        Centered.toReal_one, node, valuation, and_true] using
          And.intro nonnegative atMostOne
    · change DyadicInterval.Fact.whole.Contains (valuation x (node 1))
      simp [DyadicInterval.Fact.Contains, DyadicInterval.Fact.whole,
        rawContains, lowerContains, upperContains])
  change quarterRange.Contains (valuation x (node 1)) at result
  simpa only [quarterRange, DyadicInterval.Fact.Contains, rawContains,
    lowerContains, upperContains, DyadicInterval.toReal_zero,
    Centered.toReal_quarter, node, valuation, and_true] using result

/--
info: 'Hex.IntervalMathlib.CenteredConformance.tacticCentered' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms tacticCentered

end Hex.IntervalMathlib.CenteredConformance
