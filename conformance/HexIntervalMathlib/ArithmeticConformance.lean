/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import Mathlib.Tactic.NormNum
import HexIntervalMathlib.Experiment.Arithmetic
import HexInterval.Experiment.PayloadSession
import HexInterval.Experiment.ProofEmitter

/-!
# Exact arithmetic replay conformance

The live rule subtracts an upper-bounded interval from an open lower half-line.
Its exact result is again open and unbounded, so the proof exercises cut
strictness and missing endpoints rather than a closed bounded special case.
-/

namespace Hex.IntervalMathlib.ArithmeticConformance

open Hex.Interval Hex.Interval.Experiment
open Propagator PayloadArena PayloadSession SemanticReplay ChronologicalReplay ProofEmitter
open DyadicInterval DyadicRules Arithmetic

private def real : DomainId := { index := 0 }
private def sourceKey : OpKey := { name := "arithmetic-conformance.source" }

private def endpointLimit : EndpointLimit :=
  { maxEndpointHeight := 64, maxAlignmentShift := 64 }

private def config : Config :=
  { endpointLimit
    reciprocalBasePrecision := 2
    maxReciprocalEffort := 0 }

private def operations : Array Operation :=
  (arithmeticOperations real).push
    { key := sourceKey, inputs := [], output := real }

private def node (index : Nat) : NodeId := { index }
private def payload (index : Nat) : PayloadId := { index }

private def sourceInstruction : Node :=
  { domain := real, op := { index := 6 }, args := [] }

private def subtractionInstruction : Node :=
  { domain := real, op := { index := 2 }, args := [node 0, node 1] }

private def program : Program :=
  { operations
    nodes := #[sourceInstruction, sourceInstruction, subtractionInstruction] }

private def leftRange : DyadicInterval.Fact :=
  ⟨.bounds (.finite 1 true) .unbounded, by decide⟩

private def rightRange : DyadicInterval.Fact :=
  ⟨.bounds .unbounded (.finite 3 false), by decide⟩

private def differenceRange : DyadicInterval.Fact :=
  ⟨.bounds (.finite (-2) true) .unbounded, by decide⟩

@[simp] private theorem toReal_intCast (value : Int) :
    DyadicInterval.toReal (value : Dyadic) = value := by
  rw [DyadicInterval.toReal, Dyadic.toRat_intCast]
  norm_num

@[simp] private theorem toReal_one : DyadicInterval.toReal 1 = (1 : ℝ) := by
  rw [show (1 : Dyadic) = ((1 : Int) : Dyadic) from rfl, toReal_intCast]
  norm_num

@[simp] private theorem toReal_three : DyadicInterval.toReal 3 = (3 : ℝ) := by
  rw [show (3 : Dyadic) = ((3 : Int) : Dyadic) from rfl, toReal_intCast]
  norm_num

@[simp] private theorem toReal_negTwo : DyadicInterval.toReal (-2) = (-2 : ℝ) := by
  rw [show (-2 : Dyadic) = ((-2 : Int) : Dyadic) from rfl, toReal_intCast]
  norm_num

private def limits : Propagator.Limits :=
  { maxOperations := 8
    maxNodes := 4
    maxRules := 16
    maxRegistryEntries := 32
    maxReplayFormats := 16
    maxArity := 2
    maxApplications := 8
    maxQueueEntries := 16
    maxActions := 8
    maxAcceptedFacts := 4
    maxRetainedSuggestions := 0
    maxEffort := 0
    maxObservationValue := 16
    maxDiagnosticValue := 300
    maxOutcomeCandidates := 1
    maxOutcomeSuggestions := 0
    maxProposalItems := 0
    maxInstances := 0
    maxGeneration := 0
    maxNodeDepth := 1
    maxEqualities := 0
    splitEndpointLimit := endpointLimit }

private def arenaLimits : PayloadArena.Limits :=
  { maxEntries := limits.maxActions
    maxBodyCells := 0
    maxDrafts := limits.maxActions
    maxDraftCells := 0
    maxAtom := 0
    maxSchema := 0
    maxUses := limits.maxActions }

private def session? : Option (PayloadSession.Session DyadicInterval.Fact) :=
  match PayloadSession.Session.start
      (DyadicInterval.factDomain endpointLimit) program
      #[arithmeticPackage config real] #[leftRange, rightRange, .whole]
      limits arenaLimits with
  | .ok session => some session
  | .error _ => none

private def run? : Option (PayloadSession.Run DyadicInterval.Fact) := do
  let session ← session?
  pure (session.drive 8)

private def action : Action :=
  { serial := 0
    programVersion := 0
    application := { index := 0 }
    rule := { index := 3 }
    key := subForwardKey
    node := node 2
    kind := .forward
    effort := 0
    generation := 0
    inputs := [{ node := node 0, version := 0 }, { node := node 1, version := 0 }]
    writes := [node 2] }

private def event : FactEvent DyadicInterval.Fact :=
  { programVersion := 0
    node := node 2
    previous := { node := node 2, version := 0 }
    fact := differenceRange
    version := 1
    cause := .rule action differenceRange (payload 0) }

private def entry : Entry :=
  { origin := action, role := .fact, schema := 0, body := [] }

private def step : RuleStep DyadicInterval.Fact :=
  { event
    payload := payload 0
    entry
    assumptions :=
      [{ node := node 0, fact := leftRange }, { node := node 1, fact := rightRange }]
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
      | _, _ => false

private def quoteMatchesLive : Bool :=
  match run? with
  | some run =>
      run.stop == .saturated && run.session.engine.history.size == 1 &&
        run.session.engine.factAt? { node := node 2, version := 1 } ==
          some differenceRange &&
        match run.session.engine.history[0]?,
            run.session.arena.entry? (payload 0) .fact with
        | some actualEvent, some actualEntry =>
            sameEvent actualEvent event && sameEntry actualEntry entry
        | _, _ => false
  | none => false

#guard quoteMatchesLive

private def checkerInput : CheckerInput DyadicInterval.Fact :=
  { baseProgram := program
    initialFacts := #[leftRange, rightRange, .whole]
    target := { node := node 2, fact := differenceRange } }

private def base : List (NodeFact DyadicInterval.Fact) :=
  [{ node := node 0, fact := leftRange },
    { node := node 1, fact := rightRange },
    { node := node 2, fact := .whole }]

private def leftSound : Evidence
    (Arithmetic.semantics.Entails program base
      { node := node 0, fact := leftRange }) :=
  ProofEmitter.assumed (by simp [base])

private def rightSound : Evidence
    (Arithmetic.semantics.Entails program base
      { node := node 1, fact := rightRange }) :=
  ProofEmitter.assumed (by simp [base])

private def previousSound : Evidence
    (Arithmetic.semantics.Entails program base
      { node := node 2, fact := step.previous }) := by
  apply ProofEmitter.assumed
  simp [step, base]

private def assumptionsSound : Evidence
    (InputsSound Arithmetic.semantics program base step.assumptions) := by
  simpa [step, event] using
    (EntailsList.cons leftSound (EntailsList.cons rightSound EntailsList.nil)).sound

private def replayed :=
  ProofEmitter.replayRule (Arithmetic.subFactSchema endpointLimit)
    (Arithmetic.domain endpointLimit) checkerInput program
    (ProgramPrefix.refl program) base step previousSound assumptionsSound

#guard replayed.isSome

private def weakenedLeft : Evidence
    (Arithmetic.semantics.Entails program base
      { node := node 0, fact := DyadicInterval.Fact.whole }) :=
  (ProofEmitter.closeFact (Arithmetic.domain endpointLimit) program base
    (node 0) leftRange .whole leftSound).get (by rfl)

private def wrongAssumption : RuleStep DyadicInterval.Fact :=
  { step with assumptions :=
      [{ node := node 0, fact := .whole }, { node := node 1, fact := rightRange }] }

private def wrongInputs : Evidence
    (InputsSound Arithmetic.semantics program base wrongAssumption.assumptions) := by
  simpa [wrongAssumption, step, event] using
    (EntailsList.cons weakenedLeft
      (EntailsList.cons rightSound EntailsList.nil)).sound

private def assumptionRejected :=
  ProofEmitter.replayRule (Arithmetic.subFactSchema endpointLimit)
    (Arithmetic.domain endpointLimit) checkerInput program
    (ProgramPrefix.refl program) base wrongAssumption
    (by simpa [wrongAssumption, step, event] using previousSound) wrongInputs

#guard assumptionRejected.isNone

private def trailingPayload : RuleStep DyadicInterval.Fact :=
  { step with entry := { entry with body := [0] } }

private def payloadRejected :=
  ProofEmitter.replayRule (Arithmetic.subFactSchema endpointLimit)
    (Arithmetic.domain endpointLimit) checkerInput program
    (ProgramPrefix.refl program) base trailingPayload
    (by simpa [trailingPayload, step, event] using previousSound)
    (by simpa [trailingPayload, step, event] using assumptionsSound)

#guard payloadRejected.isNone

/-- The live Mathlib-free subtraction event becomes an ordinary theorem via
the arithmetic package schema and the operation-agnostic proof emitter. -/
theorem emittedSubtraction :
    Arithmetic.semantics.Entails program base checkerInput.target :=
  ProofEmitter.proofOfReplay replayed (by rfl)

private noncomputable def valuation (x y : ℝ) : NodeId → ℝ
  | ⟨0⟩ => x
  | ⟨1⟩ => y
  | ⟨2⟩ => x - y
  | _ => 0

private theorem models (x y : ℝ) : Arithmetic.Models program (valuation x y) := by
  intro output instruction found operation operationFound key
  rcases output with ⟨index⟩
  cases index with
  | zero =>
      simp [Program.node?, program, sourceInstruction] at found
      subst instruction
      simp [Program.operation?, program, operations, arithmeticOperations,
        sourceKey, subOp] at operationFound
      subst operation
      simp [subOp] at key
  | succ index =>
      cases index with
      | zero =>
          simp [Program.node?, program, sourceInstruction] at found
          subst instruction
          simp [Program.operation?, program, operations, arithmeticOperations,
            sourceKey, subOp] at operationFound
          subst operation
          simp [subOp] at key
      | succ index =>
          cases index with
          | zero =>
              simp [Program.node?, program, subtractionInstruction] at found
              subst instruction
              refine ⟨node 0, node 1, rfl, ?_⟩
              simp [node, valuation]
          | succ index => simp [Program.node?, program] at found

/-- Open and independently unbounded input facts are preserved through exact
semantic replay: `x > 1` and `y ≤ 3` imply `x - y > -2`. -/
theorem tacticSubtraction (x y : ℝ) (left : 1 < x) (right : y ≤ 3) :
    -2 < x - y := by
  have result := emittedSubtraction (valuation x y) (models x y) (by
    intro assumption member
    simp only [base, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl
    · change leftRange.Contains (valuation x y (node 0))
      simpa [leftRange, DyadicInterval.Fact.Contains, rawContains, lowerContains,
        upperContains, node, valuation] using left
    · change rightRange.Contains (valuation x y (node 1))
      simpa [rightRange, DyadicInterval.Fact.Contains, rawContains, lowerContains,
        upperContains, node, valuation] using right
    · change DyadicInterval.Fact.whole.Contains (valuation x y (node 2))
      simp [DyadicInterval.Fact.Contains, DyadicInterval.Fact.whole, rawContains,
        lowerContains, upperContains])
  change differenceRange.Contains (valuation x y (node 2)) at result
  simpa [differenceRange, DyadicInterval.Fact.Contains, rawContains, lowerContains,
    upperContains, node, valuation] using result

/--
info: 'Hex.IntervalMathlib.ArithmeticConformance.tacticSubtraction' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms tacticSubtraction

end Hex.IntervalMathlib.ArithmeticConformance
