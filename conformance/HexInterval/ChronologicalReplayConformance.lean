/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import HexInterval.Experiment.ChronologicalReplay
import HexInterval.PolicyFunctionConformance

/-!
The actual arbitrary-function contractor event is replayed as an installed
fact theorem, not merely as a package-local proposal theorem.  This composes
the retained recipe with proofs of its resolved input, the previous top fact,
and the package-independent fact-domain meet.
-/

namespace Hex.Interval.ChronologicalReplayConformance

open Experiment Propagator SemanticReplay ChronologicalReplay
open PolicyFunctionConformance

def base : List (NodeFact Rank) :=
  [{ node := node 0, fact := 0 },
   { node := node 1, fact := 0 },
   { node := node 2, fact := 0 }]

theorem baseWithinProgram : FactsWithin program base := by
  intro fact member
  simp only [base, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl <;> simp [program, node]

theorem baseWithinExtended : FactsWithin extendedProgram base := by
  intro fact member
  simp only [base, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl <;> simp [extendedProgram, program, node]

theorem baseMatchesInput : InitialContext checkerInput base := by
  refine { size := by rfl, member := ?_ }
  intro observed fact
  rcases observed with ⟨index⟩
  cases index with
  | zero => simp [base, checkerInput, node, eq_comm]
  | succ index =>
      cases index with
      | zero => simp [base, checkerInput, node, eq_comm]
      | succ index =>
          cases index with
          | zero => simp [base, checkerInput, node, eq_comm]
          | succ index => simp [base, checkerInput, node]

def previousSound (target : NodeId) :
    Evidence
      (functionSemantics.Entails extendedProgram base
        { node := target, fact := 0 }) :=
  { proof := by
      intro _ _ _
      exact Or.inl rfl }

def topInputSound (inputNode : NodeId) :
    Evidence
      (InputsSound functionSemantics extendedProgram base
        [{ node := inputNode, fact := 0 }]) :=
  { proof := by
      intro input member
      simp only [List.mem_singleton] at member
      subst input
      intro _ _ _
      exact Or.inl rfl }

/-- The semantic fact domain independently validates the exact executable
meet `top ∩ range = range` used by the function contractor. -/
def rankFacts : FactDomainSchema functionSemantics :=
  { top := fun _ => 0
    topSound := by
      intro _ _ _ _ _ _
      exact Or.inl rfl
    proveMeet := fun _ _ previous proposed installed =>
      if previousProof : previous = 0 then
        if proposedTop : proposed = 0 then
          if installedTop : installed = 0 then
            some
              { proof := by
                  subst previous
                  subst proposed
                  subst installed
                  intro _ _
                  constructor
                  · intro installedHolds
                    exact ⟨installedHolds, installedHolds⟩
                  · intro holds
                    exact holds.1 }
          else
            none
        else if proposedProof : proposed = 1 then
          if installedProof : installed = 1 then
            some
              { proof := by
                  subst previous
                  subst proposed
                  subst installed
                  intro valuation _
                  constructor
                  · intro installedHolds
                    exact ⟨Or.inl rfl, installedHolds⟩
                  · intro holds
                    exact holds.2 }
          else none
        else none
      else none }

def replaysStep (mutate : FactEvent Rank -> FactEvent Rank := id)
    (inputNode : NodeId := node 0) : Bool :=
  match semanticFixture? with
  | none => false
  | some fixture =>
      let finalProgram := fixture.session.state.engine.program
      if finalProof : finalProgram = extendedProgram then
        let baseProgramPrefix : ProgramPrefix checkerInput.baseProgram finalProgram := by
          simpa [checkerInput, finalProof] using functionPrefix
        match fixture.session.state.engine.history[0]? with
        | none => false
        | some event =>
            let event := mutate event
            let assumptions : List (NodeFact Rank) :=
              [{ node := inputNode, fact := 0 }]
            let assumptionEvidence :
                Evidence
                  (InputsSound functionSemantics finalProgram base assumptions) :=
              { proof := by
                  simpa [finalProof, assumptions] using
                    (topInputSound inputNode).proof }
            (ChronologicalReplay.replayRuleStep fixture.registry rankFacts
              checkerInput fixture.session.arena event finalProgram baseProgramPrefix
              base assumptions 0
              { proof := by
                  simpa [finalProof] using (previousSound event.node).proof }
              assumptionEvidence).isSome
      else
        false

-- The live contractor event now proves its installed fact from the caller's
-- base assumption after exact meet validation.
#guard replaysStep

-- Event/program disagreement, a malformed previous-node pointer, reordered
-- inputs, missing write authority, and a false installed-meet claim all fail
-- closed.
#guard
  !replaysStep (fun event => { event with programVersion := 0 }) &&
    !replaysStep (fun event =>
      { event with previous := { event.previous with node := node 2 } }) &&
    !replaysStep id (node 1) &&
    !replaysStep (fun event =>
      match event.cause with
      | .rule action proposed proof =>
          { event with cause := .rule { action with writes := [] } proposed proof }
      | .transport _ _ => event) &&
    !replaysStep (fun event => { event with fact := 0 })

def replaysResolved (mutate : FactEvent Rank -> FactEvent Rank := id) : Bool :=
  match semanticFixture? with
  | none => false
  | some fixture =>
      let finalProgram := fixture.session.state.engine.program
      if finalProof : finalProgram = extendedProgram then
        let baseProgramPrefix : ProgramPrefix checkerInput.baseProgram finalProgram := by
          simpa [checkerInput, finalProof] using functionPrefix
        let resolve :
            (seen : SeenVersion) ->
              Option (Resolved functionSemantics finalProgram base seen) :=
          fun seen =>
            if _versionProof : seen.version = 0 then
              if within : seen.node.index < finalProgram.nodes.size then
                some
                  { fact := 0
                    within
                    sound :=
                      { proof := by
                          simpa [finalProof] using
                            (previousSound seen.node).proof } }
              else
                none
            else
              none
        match fixture.session.state.engine.history[0]? with
        | none => false
        | some event =>
            (ChronologicalReplay.replayResolvedRule fixture.registry rankFacts
              checkerInput fixture.session.arena (mutate event) finalProgram
              baseProgramPrefix base resolve).isSome
      else
        false

-- Prefix resolution supplies both the previous fact and the action's exact
-- ordered input list; the caller no longer assembles either list manually.
#guard replaysResolved

-- A forward or cyclic reference cannot be recovered from the checked
-- version-zero prefix.
#guard
  !replaysResolved (fun event =>
    { event with
      previous := { event.previous with version := 1 } })

def foldsRule : Bool :=
  match semanticFixture? with
  | none => false
  | some fixture =>
      let finalProgram := fixture.session.state.engine.program
      if finalProof : finalProgram = extendedProgram then
        let baseProgramPrefix : ProgramPrefix checkerInput.baseProgram finalProgram := by
          simpa [checkerInput, finalProof] using functionPrefix
        let checked : Prefix functionSemantics finalProgram base :=
          Prefix.start
            (by simpa [finalProof] using baseWithinExtended)
            fun seen _ within =>
            some
              { fact := 0
                within
                sound :=
                  { proof := by
                      simpa [finalProof] using
                        (previousSound seen.node).proof } }
        match fixture.session.state.engine.history[0]? with
        | none => false
        | some event =>
            match Prefix.replayRule checked fixture.registry rankFacts
                checkerInput fixture.session.arena event baseProgramPrefix with
            | none => false
            | some step =>
                (step.next.resolve
                    { node := event.node, version := event.version }).isSome &&
                  (Prefix.replayRule step.next fixture.registry rankFacts
                    checkerInput fixture.session.arena event
                    baseProgramPrefix).isNone
      else
        false

-- A successful event extends the private prefix with its exact positive
-- version; replaying the same `(node, version)` is rejected as a duplicate.
#guard foldsRule

def replaysInstance (mutate : InstanceEvent -> InstanceEvent := id) : Bool :=
  match semanticFixture? with
  | none => false
  | some fixture =>
      let finalProgram := fixture.session.state.engine.program
      if finalProof : finalProgram = extendedProgram then
        let stepPrefix : ProgramPrefix program finalProgram := by
          simpa [finalProof] using functionPrefix
        let sameOperations : program.operations = finalProgram.operations := by
          simp [finalProof, extendedProgram, program]
        match fixture.session.state.engine.instanceHistory[0]? with
        | none => false
        | some event =>
            (ChronologicalReplay.replayInstanceStep fixture.registry checkerInput
              fixture.session.arena (mutate event) program finalProgram
              (ProgramPrefix.refl program) stepPrefix sameOperations
              (extendRefl functionSemantics program)).isSome
      else
        false

-- The package-owned instance theorem is composed with the checked base
-- program, producing a conservative-extension theorem for the current
-- session program.
#guard replaysInstance

-- Structural chronology requires one program-version increment from the
-- originating matcher action.
#guard !replaysInstance (fun event => { event with programVersion := 0 })

def functionLaws : Laws functionSemantics :=
  { holdsEq := by
      intro _ valuation left right fact _ _ valueProof
      change RankAllows fact (valuation left) ↔ RankAllows fact (valuation right)
      rw [valueProof] }

/-- The arbitrary-function interpretation restricts along its actual
instantiation step, and facts on old nodes do not change meaning. -/
def functionStep :
    StableStep functionSemantics program extendedProgram :=
  { programPrefix := functionPrefix
    modelsBefore := by
      intro valuation model
      change FunctionModels program valuation
      refine ⟨?_, ?_, ?_⟩
      · intro _
        exact model.1 (by rfl)
      · intro impossible
        simp [Program.node?, program, node] at impossible
      · intro impossible
        simp [Program.node?, program, node] at impossible
    holdsOld := by
      intro oldValue newValue fact within _ _ agreement
      change
        RankAllows fact.fact (oldValue fact.node) ↔
          RankAllows fact.fact (newValue fact.node)
      rw [agreement fact.node within] }

/-! A stability premise must cover the complete old valuation, not only the
node carrying the fact: a semantics may interpret that fact using other old
nodes.  This small adapter is a regression test for that distinction. -/

def contextualProgram : Program :=
  { operations := #[]
    nodes :=
      #[{ domain := real, op := { index := 0 }, args := [] },
        { domain := real, op := { index := 0 }, args := [] }] }

def contextualSemantics : Semantics Unit :=
  { Value := Nat
    models := fun _ _ => True
    holds := fun _ valuation _ => valuation (node 1) = 0 }

def contextualBase : List (NodeFact Unit) :=
  [{ node := node 0, fact := () }]

theorem contextualWithin : FactsWithin contextualProgram contextualBase := by
  intro fact member
  simp only [contextualBase, List.mem_singleton] at member
  subst fact
  simp [contextualProgram, node]

def contextualStep :
    StableStep contextualSemantics contextualProgram contextualProgram :=
  { programPrefix := ProgramPrefix.refl contextualProgram
    modelsBefore := by
      intro _ model
      exact model
    holdsOld := by
      intro oldValue newValue _ _ _ _ agreement
      change oldValue (node 1) = Nat.zero ↔ newValue (node 1) = Nat.zero
      rw [agreement (node 1) (by simp [contextualProgram, node])] }

def contextualSound :
    Evidence
      (contextualSemantics.Entails contextualProgram contextualBase
        { node := node 0, fact := () }) :=
  { proof := by
      intro _ _ assumptions
      exact assumptions _ (by simp [contextualBase]) }

example :
    Evidence
      (contextualSemantics.Entails contextualProgram contextualBase
        { node := node 0, fact := () }) :=
  liftEntails contextualStep contextualWithin
    (by simp [contextualProgram, node]) contextualSound

def initialSound (target : NodeId) :
    Evidence
      (functionSemantics.Entails program base
        { node := target, fact := 0 }) :=
  { proof := by
      intro _ _ _
      exact Or.inl rfl }

def foldsInstanceThenRule : Bool :=
  match semanticFixture? with
  | none => false
  | some fixture =>
      let finalProgram := fixture.session.state.engine.program
      if finalProof : finalProgram = extendedProgram then
        let stepPrefix : ProgramPrefix program finalProgram := by
          simpa [finalProof] using functionPrefix
        let sameOperations : program.operations = finalProgram.operations := by
          simp [finalProof, extendedProgram, program]
        let stable : StableStep functionSemantics program finalProgram := by
          simpa [finalProof] using functionStep
        let cursor :
            Cursor functionSemantics checkerInput base 0 program :=
          Cursor.startInput baseWithinProgram baseMatchesInput
        match fixture.session.state.engine.instanceHistory[0]?,
            fixture.session.state.engine.history[0]? with
        | some instanceEvent, some factEvent =>
            let staleEvent :=
              { instanceEvent with
                programVersion := 8
                origin :=
                  { instanceEvent.origin with programVersion := 7 } }
            let wrongNodes :=
              { instanceEvent with
                newNodes := instanceEvent.newNodes.reverse }
            let rejectsStale :=
              (Cursor.replayInstance cursor fixture.registry rankFacts
                fixture.session.arena staleEvent finalProgram stepPrefix
                sameOperations stable).isNone
            let rejectsWrongNodes :=
              (Cursor.replayInstance cursor fixture.registry rankFacts
                fixture.session.arena wrongNodes finalProgram stepPrefix
                sameOperations stable).isNone
            match Cursor.replayInstance cursor fixture.registry rankFacts
                fixture.session.arena instanceEvent finalProgram stepPrefix
                sameOperations stable with
            | none => false
            | some instantiated =>
                match Cursor.replayRule instantiated fixture.registry rankFacts
                    fixture.session.arena factEvent with
                | none => false
                | some contracted =>
                    rejectsStale && rejectsWrongNodes &&
                      (cursor.facts.resolve
                        { node := node 3, version := 0 }).isNone &&
                      (instantiated.facts.resolve
                        { node := node 0, version := 0 }).isSome &&
                      (instantiated.facts.resolve
                        { node := node 3, version := 0 }).isSome &&
                      (contracted.facts.resolve
                        { node := node 3, version := 1 }).isSome
        | _, _ => false
      else
        false

-- Starting from the caller's original graph, the actual package-owned
-- instantiator is replayed, old facts are lifted, new expressions receive
-- proved top facts, and the newly installed arbitrary-function propagator is
-- then replayed.  No function case exists in the chronological core.
#guard foldsInstanceThenRule

def baseTargetInput : CheckerInput Rank :=
  { checkerInput with target := { node := node 0, fact := 0 } }

def callerTargetEvidence? :
    Option
      (Evidence
        (functionSemantics.Entails baseTargetInput.baseProgram base
          baseTargetInput.target)) :=
  match semanticFixture? with
  | none => none
  | some fixture =>
      let finalProgram := fixture.session.state.engine.program
      if finalProof : finalProgram = extendedProgram then
        let stepPrefix : ProgramPrefix program finalProgram := by
          simpa [finalProof] using functionPrefix
        let sameOperations : program.operations = finalProgram.operations := by
          simp [finalProof, extendedProgram, program]
        let stable : StableStep functionSemantics program finalProgram := by
          simpa [finalProof] using functionStep
        let cursor :
            Cursor functionSemantics baseTargetInput base 0 program :=
          Cursor.startInput baseWithinProgram (by
            refine
              { size := ?_
                member := ?_ }
            · simpa [baseTargetInput] using baseMatchesInput.size
            · intro observed fact
              simpa [baseTargetInput] using
                baseMatchesInput.member observed fact)
        match fixture.session.state.engine.instanceHistory[0]?,
            fixture.session.state.engine.history[0]? with
        | some instanceEvent, some factEvent =>
            match Cursor.replayInstance cursor fixture.registry rankFacts
                fixture.session.arena instanceEvent finalProgram stepPrefix
                sameOperations stable with
            | none => none
            | some instantiated =>
                match Cursor.replayRule instantiated fixture.registry rankFacts
                    fixture.session.arena factEvent with
                | none => none
                | some contracted =>
                    let targetWithin :
                        baseTargetInput.target.node.index <
                          baseTargetInput.baseProgram.nodes.size := by
                      simp [baseTargetInput, checkerInput, program, node]
                    let finalStable :
                        StableStep functionSemantics
                          baseTargetInput.baseProgram finalProgram := by
                      simpa [baseTargetInput, checkerInput] using stable
                    Cursor.close contracted rankFacts finalStable
                      (by simpa [baseTargetInput, checkerInput] using
                        baseWithinProgram)
                      targetWithin { node := node 0, version := 0 }
        | _, _ => none
      else
        none

-- Final closure uses the package-proved conservative extension and semantic
-- stability to return from the enlarged graph to the caller's original
-- target. This runtime guard exercises the opaque cursor API; the ordinary
-- proof-term canary below does not rely on this compiled success observation.
#guard callerTargetEvidence?.isSome

def other : DomainId := { index := 1 }

def mixedProgram : Program :=
  { operations := #[]
    nodes :=
      #[{ domain := real, op := { index := 0 }, args := [] },
        { domain := other, op := { index := 0 }, args := [] }] }

-- Equality transport checks endpoint domains before asking any package theorem
-- or generic semantic equality law to move a fact.
#guard
  (sameDomain? mixedProgram (node 0) (node 0)).isSome &&
    (sameDomain? mixedProgram (node 0) (node 1)).isNone

def negSinSound :
    Evidence
      (functionSemantics.Entails extendedProgram base
        { node := node 4, fact := 1 }) :=
  { proof := by
      intro valuation model _
      exact Or.inr (by
        rw [model.2.2 (by rfl), model.2.1 (by rfl)]
        simp) }

def noInputsSound :
    Evidence
      (InputsSound functionSemantics extendedProgram base []) :=
  { proof := by
      intro input member
      simp at member }

def sinSound :
    Evidence
      (functionSemantics.Entails extendedProgram base
        { node := node 3, fact := 1 }) :=
  { proof := by
      intro valuation model _
      exact Or.inr (model.2.1 (by rfl)) }

/-! # Ordinary proof-term emission canary

Compiled search and the private chronological cursor are deliberately opaque.
A tactic therefore must not try to turn a successful `#guard` evaluation into
a theorem.  It may instead quote the plain trace and emit applications of the
generic soundness combinators below.  This canary constructs exactly such a
term and projects its `Evidence.proof` in the ordinary kernel. -/

def rangeMeet (target : NodeId) :
    Evidence
      (∀ valuation, functionSemantics.models extendedProgram valuation ->
        (functionSemantics.holds extendedProgram valuation
            { node := target, fact := 1 } ↔
          functionSemantics.holds extendedProgram valuation
              { node := target, fact := 0 } ∧
            functionSemantics.holds extendedProgram valuation
              { node := target, fact := 1 })) :=
  { proof := by
      intro _ _
      constructor
      · intro installed
        exact ⟨Or.inl rfl, installed⟩
      · intro holds
        exact holds.2 }

/-- Proof term emitted for the dynamically installed sine contractor. -/
def emittedContract :
    Evidence
      (functionSemantics.Entails extendedProgram base
        { node := node 3, fact := 1 }) :=
  installRule
    { proof := contractEntails [{ node := node 0, fact := 0 }] }
    (rangeMeet (node 3)) (previousSound (node 3))
    (topInputSound (node 0))

/-- A second, independently shaped propagator theorem: a zero-valued input to
negation gives a zero-valued output.  The forthcoming real-sine vertical
replaces this compact rank fact with a one-sided interval fact. -/
theorem negEntails :
    functionSemantics.Entails extendedProgram
      [{ node := node 3, fact := 1 }]
      { node := node 4, fact := 1 } := by
  change ∀ valuation : NodeId -> Int, FunctionModels extendedProgram valuation ->
    (∀ (assumption : NodeFact Rank),
      assumption ∈ ([{ node := node 3, fact := 1 }] : List (NodeFact Rank)) ->
      RankAllows assumption.fact (valuation assumption.node)) ->
    RankAllows 1 (valuation (node 4))
  intro valuation model assumptions
  have source := assumptions { node := node 3, fact := 1 } (by simp)
  have sourceZero : valuation (node 3) = 0 := by
    simpa [RankAllows] using source
  exact Or.inr (by
    rw [model.2.2 (by rfl), sourceZero]
    simp)

/-- Proof term emitted for the independent negation propagator, consuming the
sine contractor's result as its exact input dependency. -/
def emittedNegation :
    Evidence
      (functionSemantics.Entails extendedProgram base
        { node := node 4, fact := 1 }) :=
  installRule
    { proof := negEntails }
    (rangeMeet (node 4)) (previousSound (node 4))
    { proof := by
        intro input member
        simp only [List.mem_singleton] at member
        subst input
        exact emittedContract.proof }

def emittedOddnessAction : Action :=
  { serial := 0
    programVersion := 0
    application := { index := 0 }
    rule := { index := 0 }
    key := matcherKey
    node := node 2
    kind := .instantiate
    effort := 0
    generation := 0
    inputs := []
    structuralInputs := matcherInputs
    matcherEpoch := some 0 }

def emittedOddnessEdge : EqualityEdge :=
  { left := node 2
    right := node 4
    generation := 1
    origin := emittedOddnessAction
    payload := payload 1 }

def emittedOddnessDomain :
    SameDomain extendedProgram emittedOddnessEdge.left emittedOddnessEdge.right :=
  { leftNode := sinNegInstruction
    rightNode := negSinInstruction
    leftAt := by rfl
    rightAt := by rfl
    domainEq := rfl }

/-- Proof term emitted for equality transport back to the caller's original
`sin (-x)` expression. -/
def emittedTransport :
    Evidence
      (functionSemantics.Entails extendedProgram base
        { node := node 2, fact := 1 }) :=
  installTransport functionLaws emittedOddnessEdge emittedOddnessDomain
    (Or.inl ⟨rfl, rfl⟩) { proof := oddnessEntails }
    (rangeMeet (node 2)) (previousSound (node 2)) emittedNegation
    noInputsSound

def rangeTargetInput : CheckerInput Rank :=
  { checkerInput with target := { node := node 2, fact := 1 } }

def emittedTarget :
    Evidence
      (functionSemantics.Entails rangeTargetInput.baseProgram base
        rangeTargetInput.target) :=
  closeBase (input := rangeTargetInput) functionStep baseWithinProgram
    (by simp [rangeTargetInput, checkerInput, program, node])
    { proof := functionExtension } emittedTransport

/-- The ordinary downstream theorem gate: no `#guard`, `native_decide`, or
opaque success equation participates in this proof. -/
theorem callerSinNegRange :
    functionSemantics.Entails program base { node := node 2, fact := 1 } := by
  simpa [rangeTargetInput, checkerInput] using emittedTarget.proof

def transportEvent (source : NodeId := node 4) : FactEvent Rank :=
  { programVersion := 1
    node := node 2
    previous := { node := node 2, version := 0 }
    fact := 1
    version := 1
    cause :=
      .transport { index := 0 } { node := source, version := 1 } }

def replaysTransportFrom (source : NodeId)
    (sourceEvidence :
      Evidence
        (functionSemantics.Entails extendedProgram base
          { node := source, fact := 1 })) : Bool :=
  match semanticFixture? with
  | none => false
  | some fixture =>
      let finalProgram := fixture.session.state.engine.program
      if finalProof : finalProgram = extendedProgram then
        let baseProgramPrefix : ProgramPrefix checkerInput.baseProgram finalProgram := by
          simpa [checkerInput, finalProof] using functionPrefix
        match fixture.session.state.engine.equalities[0]? with
        | none => false
        | some edge =>
            let event := transportEvent source
            (ChronologicalReplay.replayTransportStep fixture.registry rankFacts
              { holdsEq := by
                  simpa [finalProof] using functionLaws.holdsEq }
              checkerInput fixture.session.arena event edge finalProgram
              baseProgramPrefix base [] 0 1
              { proof := by
                  simpa [finalProof] using (previousSound event.node).proof }
              { proof := by
                  simpa [finalProof, event, transportEvent] using
                    sourceEvidence.proof }
              { proof := by simpa [finalProof] using noInputsSound.proof }).isSome
      else
        false

def replaysTransport : Bool :=
  replaysTransportFrom (node 4) negSinSound

-- The equality produced by the arbitrary-function matcher can drive generic
-- fact transport once the source fact is available; the package theorem, not
-- the engine, supplies the endpoint equality.
#guard replaysTransport

-- The retained transport source must be the opposite endpoint of the exact
-- checked edge.
#guard
  !replaysTransportFrom (node 3) sinSound

end Hex.Interval.ChronologicalReplayConformance
