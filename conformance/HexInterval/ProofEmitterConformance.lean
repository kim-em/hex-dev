/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import HexInterval.Experiment.ProofFrontend
import HexInterval.PolicyFunctionConformance

/-!
This isolated canary quotes a plain trace for the arbitrary-function
contractor from `PolicyFunctionConformance`.  The theorem below is accepted by
ordinary kernel reduction; it does not inspect the opaque compiled session
or rely on a native decision oracle.
-/

namespace Hex.Interval.ProofEmitterConformance

open Experiment Propagator PayloadArena SemanticReplay ChronologicalReplay
open PolicyFunctionConformance
open Lean Meta

def base : List (NodeFact Rank) :=
  [{ node := node 0, fact := 0 }]

def action : Action :=
  { serial := 1
    programVersion := 1
    application := { index := 1 }
    rule := { index := 1 }
    key := contractKey
    node := node 3
    kind := .improve
    effort := 0
    generation := 1
    inputs := [{ node := node 0, version := 0 }]
    writes := [node 3] }

def entry : Entry :=
  { origin := action
    role := .fact
    schema := 5
    body := [1, 73] }

/-- The value a tactic quotes after running the opaque search.  It contains
only identifiers, facts, and the immutable package certificate body. -/
def quotedStep : ProofEmitter.RuleStep Rank :=
  { event :=
      { programVersion := 1
        node := node 3
        previous := { node := node 3, version := 0 }
        fact := 1
        version := 1
        cause := .rule action 1 { index := 2 } }
    payload := { index := 2 }
    entry
    assumptions := base
    previous := 0 }

/-- The literal is field-for-field semantic data from the real compiled search
run.  This executable comparison is only a regression for the emitter; the
kernel theorem below continues to depend on the literal, not on this Boolean
or on `contracted?`. -/
def quotedMatchesSearch : Bool :=
  match contracted? with
  | none => false
  | some session =>
      match session.state.engine.history[0]?,
          session.arena.entry? quotedStep.payload .fact with
      | some actual, some actualEntry =>
          actual.programVersion == quotedStep.event.programVersion &&
            actual.node == quotedStep.event.node &&
            actual.previous == quotedStep.event.previous &&
            actual.fact == quotedStep.event.fact &&
            actual.version == quotedStep.event.version &&
            actualEntry.origin == quotedStep.entry.origin &&
            actualEntry.role == quotedStep.entry.role &&
            actualEntry.schema == quotedStep.entry.schema &&
            actualEntry.body == quotedStep.entry.body &&
            match actual.cause, quotedStep.event.cause with
            | .rule actualAction actualProposed actualPayload,
                .rule quotedAction quotedProposed quotedPayload =>
                actualAction == quotedAction &&
                  actualProposed == quotedProposed &&
                  actualPayload == quotedPayload
            | _, _ => false
      | _, _ => false

#guard quotedMatchesSearch

def previousSound :
    Evidence
      (functionSemantics.Entails extendedProgram base
        { node := quotedStep.event.node, fact := quotedStep.previous }) :=
  { proof := by
      intro _ _ _
      exact Or.inl rfl }

def baseEvidence :
    Evidence
      (functionSemantics.Entails extendedProgram base
        { node := node 0, fact := 0 }) :=
  ProofEmitter.assumed (by simp [base])

def inputEvidence :
    ProofEmitter.EntailsList functionSemantics extendedProgram base
      quotedStep.assumptions :=
  .cons baseEvidence .nil

def repeatedEvidence :
    ProofEmitter.EntailsList functionSemantics extendedProgram base
      [{ node := node 0, fact := 0 }, { node := node 0, fact := 0 }] :=
  .cons baseEvidence (.cons baseEvidence .nil)

example :
    InputsSound functionSemantics extendedProgram base
      [{ node := node 0, fact := 0 }, { node := node 0, fact := 0 }] :=
  repeatedEvidence.sound.proof

def assumptionsSound :
    Evidence
      (InputsSound functionSemantics extendedProgram base
        quotedStep.assumptions) :=
  inputEvidence.sound

def rankFacts : FactDomainSchema functionSemantics :=
  { top := fun _ => 0
    topSound := by
      intro _ _ _ _ _ _
      exact Or.inl rfl
    proveMeet := fun _ _ previous proposed installed =>
      if previousProof : previous = 0 then
        if proposedProof : proposed = 1 then
          if installedProof : installed = 1 then
            some
              { proof := by
                  subst previous
                  subst proposed
                  subst installed
                  intro _ _
                  constructor
                  · intro installedHolds
                    exact ⟨Or.inl rfl, installedHolds⟩
                  · intro holds
                    exact holds.2 }
          else
            none
        else
          none
      else
        none }

def generatedTop :
    Evidence
      (functionSemantics.Entails extendedProgram base
        { node := node 3, fact := 0 }) :=
  ProofEmitter.topFact rankFacts extendedProgram base (node 3) sinInstruction
    (by rfl)

def replayed :
    Option
      (Evidence
        (functionSemantics.Entails extendedProgram base
          { node := quotedStep.event.node, fact := quotedStep.event.fact })) :=
  ProofEmitter.replayRule factSchema rankFacts checkerInput extendedProgram
    functionPrefix base quotedStep generatedTop assumptionsSound

/-- A malicious emitter cannot make an unauthorized write acceptable by
changing both copies of the frozen action.  This isolates the generic write
check from the separate origin-equality check. -/
def unwritableAction : Action :=
  { action with writes := [] }

def unwritableStep : ProofEmitter.RuleStep Rank :=
  { quotedStep with
    event :=
      { quotedStep.event with
        cause := .rule unwritableAction 1 { index := 2 } }
    entry := { entry with origin := unwritableAction } }

def unwritableReplay :=
  ProofEmitter.replayRule factSchema rankFacts checkerInput extendedProgram
    functionPrefix base unwritableStep
      (by simpa [unwritableStep, quotedStep] using previousSound)
      (by simpa [unwritableStep, quotedStep] using assumptionsSound)

#guard unwritableReplay.isNone

/-- This is the desired downstream interface: an ordinary theorem generated
from a literal trace by transparent proof replay.  `rfl` proves that replay
succeeded, so no external evaluator participates in the proof. -/
theorem quotedTraceProvesContract :
    functionSemantics.Entails extendedProgram base
      { node := node 3, fact := 1 } := by
  simpa [quotedStep] using
    (ProofEmitter.proofOfReplay replayed (by rfl))

/-! # Generic split joining -/

inductive SplitFact where
  | all
  | yes
  | no
  | enabled
  | certified
  deriving DecidableEq

def splitNode : NodeId := node 0

def splitBaseNode : NodeId := node 1

def splitTargetNode : NodeId := node 2

def SplitHolds (valuation : NodeId -> Bool) : NodeFact SplitFact -> Prop
  | { fact := .all, .. } => True
  | { node, fact := .yes } => valuation node = true
  | { node, fact := .no } => valuation node = false
  | { node, fact := .enabled } => valuation node = true
  | { fact := .certified, .. } =>
      valuation splitBaseNode = true /\
        (valuation splitNode = true \/ valuation splitNode = false)

def splitSemantics : SemanticReplay.Semantics SplitFact :=
  { Value := Bool
    models := fun _ _ => True
    holds := fun _ valuation fact => SplitHolds valuation fact }

def splitBase : List (NodeFact SplitFact) :=
  [{ node := splitBaseNode, fact := .enabled }]

def splitTarget : NodeFact SplitFact :=
  { node := splitTargetNode, fact := .certified }

/-- Unlike the old Boolean-decision target, certification is not true without
the inherited base fact. -/
theorem splitTargetNeedsBase :
    ¬ splitSemantics.Entails program [] splitTarget := by
  intro sound
  let valuation : NodeId -> Bool := fun _ => false
  have certified := sound valuation trivial (by simp)
  exact Bool.noConfusion certified.1

def splitSchema : ProofEmitter.SplitSchema splitSemantics Unit where
  proveCover := fun _ node parent _ left right =>
    if shape : parent = .all /\ left = .yes /\ right = .no then
      some
        { proof := by
            rcases shape with ⟨rfl, rfl, rfl⟩
            intro valuation _ _
            cases value : valuation node with
            | false => exact Or.inr value
            | true => exact Or.inl value }
    else
      none

def splitParent :
    Evidence
      (splitSemantics.Entails program splitBase
        { node := splitNode, fact := .all }) :=
  { proof := by
      intro _ _ _
      trivial }

def splitLeft :
    Evidence
      (splitSemantics.Entails program
        ({ node := splitNode, fact := .yes } :: splitBase) splitTarget) :=
  { proof := by
      intro valuation _ assumptions
      have yes :=
        assumptions { node := splitNode, fact := .yes } (by simp)
      have enabled :=
        assumptions { node := splitBaseNode, fact := .enabled } (by simp [splitBase])
      exact ⟨enabled, Or.inl yes⟩ }

def splitRight :
    Evidence
      (splitSemantics.Entails program
        ({ node := splitNode, fact := .no } :: splitBase) splitTarget) :=
  { proof := by
      intro valuation _ assumptions
      have no :=
        assumptions { node := splitNode, fact := .no } (by simp)
      have enabled :=
        assumptions { node := splitBaseNode, fact := .enabled } (by simp [splitBase])
      exact ⟨enabled, Or.inr no⟩ }

def splitReplay :=
  ProofEmitter.replaySplit splitSchema program splitBase splitNode .all () .yes .no
    splitTarget splitParent splitLeft splitRight

/-- The non-tautological target needs the inherited base fact in both branches;
the two distinct child assumptions supply its corresponding left and right
cases. The runtime policy and its split suggestion do not occur in the proof
term. -/
theorem splitCertifies :
    splitSemantics.Entails program splitBase splitTarget :=
  ProofEmitter.proofOfReplay splitReplay (by rfl)

/-- The demo schema fixes an orientation, so this swapped quotation exercises
that schema guard rather than a soundness requirement of the generic join. -/
def swappedSplit :=
  ProofEmitter.replaySplit splitSchema program splitBase splitNode .all () .no .yes
    splitTarget splitParent splitRight splitLeft

#guard swappedSplit.isNone

/-- Child order is rejected by kernel reduction of the exact quoted schema
application, independently of the executable guard above. -/
theorem swappedSplitRejected : swappedSplit = none := by
  rfl

/-- Two copies of the positive child genuinely fail to cover the parent,
independently of the demo schema's orientation guard. -/
theorem yesYesNotCovering :
    ¬ (∀ valuation, splitSemantics.models program valuation →
      splitSemantics.holds program valuation { node := splitNode, fact := .all } →
        splitSemantics.holds program valuation { node := splitNode, fact := .yes } ∨
          splitSemantics.holds program valuation { node := splitNode, fact := .yes }) := by
  intro cover
  have covered := cover (fun _ => false) trivial trivial
  rcases covered with yes | yes <;> exact Bool.noConfusion yes

/--
info: 'Hex.Interval.ProofEmitterConformance.splitCertifies' depends on axioms: [propext]
-/
#guard_msgs in
#print axioms splitCertifies

def branchBase : List (NodeFact SplitFact) :=
  [{ node := splitBaseNode, fact := .yes }]

/-- The child carries a derived parent consequence at node one, not the
literal fact in `branchBase`. -/
def branchInitial : Array SplitFact := #[.yes, .enabled, .all]

def branchFacts : List (NodeFact SplitFact) :=
  { node := splitNode, fact := .yes } :: branchBase

def branchInput : CheckerInput SplitFact :=
  { baseProgram := program
    initialFacts := branchInitial
    target := splitTarget }

def inheritedSplitFact (observed : NodeId) (different : observed ≠ splitNode)
    (fact : SplitFact) (found : branchInitial[observed.index]? = some fact) :
    Evidence
      (splitSemantics.Entails program branchBase { node := observed, fact }) :=
  { proof := by
      intro valuation _ assumptions
      cases observed with
      | mk index =>
          cases index with
          | zero => simp [splitNode, node] at different
          | succ index =>
              cases index with
              | zero =>
                  simp [branchInitial] at found
                  subst fact
                  have yes := assumptions
                    { node := splitBaseNode, fact := .yes }
                    (by simp [branchBase])
                  exact yes
              | succ index =>
                  cases index with
                  | zero =>
                      simp [branchInitial] at found
                      subst fact
                      trivial
                  | succ index => simp [branchInitial] at found }

def branchSeed :
    ProofEmitter.BranchSeed splitSemantics branchInput branchBase
      { node := splitNode, fact := .yes } :=
  ProofEmitter.BranchSeed.make branchInput { node := splitNode, fact := .yes }
    (by rfl) (by rfl) inheritedSplitFact

/-- The split node is proved from the new child assumption. -/
def branchSide : Evidence
    (splitSemantics.Entails program branchFacts
      { node := splitNode, fact := .yes }) :=
  branchSeed.sound splitNode .yes (by rfl)

example :
    splitSemantics.Entails program
      ({ node := splitNode, fact := .yes } :: branchBase)
      { node := splitNode, fact := .yes } :=
  branchSide.proof

/-- A derived version-zero fact is inherited as a parent consequence under the
larger child context. -/
def branchInherited : Evidence
    (splitSemantics.Entails program branchFacts
      { node := splitBaseNode, fact := .enabled }) :=
  branchSeed.sound splitBaseNode .enabled (by rfl)

example :
    splitSemantics.Entails program
      ({ node := splitNode, fact := .yes } :: branchBase)
      { node := splitBaseNode, fact := .enabled } :=
  branchInherited.proof

/-- The inherited child fact above is a proved consequence, not a literal
member of the parent base-assumption list. -/
example :
    ({ node := splitBaseNode, fact := .enabled } : NodeFact SplitFact) ∉
      branchBase := by
  simp [branchBase]

/-- The unrelated version-zero top entry is also present in the exact seed
table and has its own inherited proof. -/
example :
    splitSemantics.Entails program
      ({ node := splitNode, fact := .yes } :: branchBase)
      { node := splitTargetNode, fact := .all } :=
  (branchSeed.sound splitTargetNode .all (by rfl)).proof

private def splitFactExpr : SplitFact → Expr
  | .all => mkConst ``SplitFact.all
  | .yes => mkConst ``SplitFact.yes
  | .no => mkConst ``SplitFact.no
  | .enabled => mkConst ``SplitFact.enabled
  | .certified => mkConst ``SplitFact.certified

private def splitEncoder : FrontendEncoder.Encoder SplitFact :=
  FrontendEncoder.make (mkConst ``SplitFact)
    (fun fact => pure (splitFactExpr fact))

/-- The Meta frontend obtains the branch assumption and every inherited entry
from the exact child-input-indexed proof table. -/
example : True := by
  run_tac
    let known ←
      ProofFrontend.seedBranch splitEncoder (mkConst ``splitSemantics)
        (mkConst ``branchInput) (mkConst ``branchFacts) branchInput
        (mkConst ``branchSeed)
    let some side :=
        ProofFrontend.findFact? known { node := splitNode, version := 0 } .yes
      | throwError "branch seed test: split assumption is missing"
    let some inherited :=
        ProofFrontend.findFact? known { node := splitBaseNode, version := 0 } .enabled
      | throwError "branch seed test: inherited parent fact is missing"
    let some top :=
        ProofFrontend.findFact? known { node := splitTargetNode, version := 0 } .all
      | throwError "branch seed test: unrelated top fact is missing"
    unless ← isDefEq (← inferType side.proof) (← inferType (mkConst ``branchSide)) do
      throwError "branch seed test: split proof has the wrong proposition"
    unless ← isDefEq (← inferType inherited.proof)
        (← inferType (mkConst ``branchInherited)) do
      throwError "branch seed test: inherited proof has the wrong proposition"
    unless top.seen.node == splitTargetNode && top.fact == .all do
      throwError "branch seed test: unrelated top fact has the wrong identity"
    let wrongInput : CheckerInput SplitFact :=
      { branchInput with target := { node := node 1, fact := .yes } }
    if (← observing? <| ProofFrontend.seedBranch splitEncoder
        (mkConst ``splitSemantics) (mkConst ``branchInput)
        (mkConst ``branchFacts) wrongInput (mkConst ``branchSeed)).isSome then
      throwError "branch seed test: mismatched checker input was accepted"
    if (← observing? <| ProofFrontend.seedBranch splitEncoder
        (mkConst ``splitSemantics) (mkConst ``branchInput)
        (mkConst ``branchBase) branchInput (mkConst ``branchSeed)).isSome then
      throwError "branch seed test: mismatched child assumptions were accepted"
  trivial

end Hex.Interval.ProofEmitterConformance
