/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import HexIntervalMathlib.Experiment.ExpSign
import HexInterval.Experiment.GoalFrontend
import HexInterval.Experiment.GoalClosure
import HexInterval.Experiment.ProofFrontend
import HexInterval.Experiment.TargetRun
import HexInterval.Experiment.BranchStart
import HexInterval.Experiment.BranchTree
import HexInterval.Experiment.BranchProof
import Mathlib.Lean.Elab.Tactic.Meta

/-!
# Branch-dependent function propagation conformance

This module checks that a retained split tree whose children use different
function-specific propagators can be folded into one kernel-checked proof.
-/

namespace Hex.IntervalMathlib.ReluConformance

open Lean Elab Tactic Meta
open Hex.Interval.Experiment
open Propagator PolicySession SemanticReplay ChronologicalReplay ProofEmitter
open Frontend FrontendEncoder ProofFrontend ProofRegistry GoalFrontend ExpSign
open GoalClosure BranchStart

private def splitOffer? (view : Propagator.Policy.View Bound) :
    Option Propagator.Policy.OfferView :=
  view.offers.toList.find? fun offer =>
    match offer.key with
    | .invoke invocation => invocation.rule == splitRuleKey
    | .split _ _ _ _ => true
    | _ => false

private def splitPolicy : TargetRun.Controller Bound Unit :=
  { update := fun state _ => state
    choose := fun state view =>
      match splitOffer? view with
      | some offer => .select offer state
      | none => .stop state }

private def signSplitter : BranchStart.Splitter Bound :=
  { split := fun graph target instruction parent point =>
      if graph.node? target == some instruction && instruction.domain == real &&
          parent == .all && point == 0 then
        some (.nonnegative, .negative)
      else
        none }

private def branchLimits : BranchStart.Limits :=
  { maxDepth := 4, maxScopes := 8 }

private def treeLimits (maxSteps := 3) (maxSplits := 1)
    (maxLeaves := 2) : BranchTree.Limits :=
  { branch := branchLimits
    maxSteps
    maxSplits
    maxLeaves
    leafFuel := limits.policy.maxDecisions }

private def boundExpr : Bound → Expr
  | .all => mkConst ``Bound.all
  | .nonnegative => mkConst ``Bound.nonnegative
  | .negative => mkConst ``Bound.negative
  | .empty => mkConst ``Bound.empty

private def boundEncoder : FrontendEncoder.Encoder Bound :=
  FrontendEncoder.make (mkConst ``Bound) (fun fact => pure (boundExpr fact))

/-! ## Branch-dependent ReLU propagation

Unlike exponential positivity, these two propagators are intentionally
conditional.  The nonnegative-side rule proves `max x 0 = x` from `0 <= x`;
the negative-side rule proves `max x 0 = 0` from `x < 0`.  The runtime and
proof packages know those two function-specific facts, while branch creation,
branch seeding, chronology replay, and the two-proof join stay generic. -/

private def reluKey : OpKey := { name := "relu-sign.max-zero" }

private def reluNonnegativeKey : RuleKey :=
  { name := "relu-sign.max-zero.nonnegative" }

private def reluNegativeKey : RuleKey :=
  { name := "relu-sign.max-zero.negative" }

private def reluOperation : Operation :=
  { key := reluKey, inputs := [real], output := real }

private def reluOperations : Array Operation := #[sourceOperation, reluOperation]

private def reluInstruction : Node :=
  { domain := real, op := { index := 1 }, args := [node 0] }

private def reluProgram : Program :=
  { operations := reluOperations, nodes := #[sourceInstruction, reluInstruction] }

private def reluNonnegativeRule : Registration :=
  { key := reluNonnegativeKey
    head := reluKey
    kind := .forward
    watches := [.argument 0]
    writes := [.result] }

private def reluNegativeRule : Registration :=
  { key := reluNegativeKey
    head := reluKey
    kind := .forward
    watches := [.argument 0]
    writes := [.result] }

private def reluFormat (side : Bound) : ReplayFormat :=
  { role := .fact
    schema := 1
    validateBody := fun body => body == [side.code] }

private def reluPlan (side : Bound) (request : RuleRequest Bound) : Plan Bound :=
  match request.inputs, request.writes with
  | [source], [target] =>
      if source.fact == side then
        { outcome :=
            .success
              [{ node := target, fact := .nonnegative, payload := payload 0 }]
              [] {}
          drafts :=
            [{ label := payload 0
               role := .fact
               schema := 1
               body := [side.code] }] }
      else
        { outcome := .failed 10, drafts := [] }
  | _, _ => { outcome := .failed 11, drafts := [] }

private def reluPackage : Package Bound :=
  { Cache := Unit
    cache := ()
    operations := #[reluOperation]
    handlers :=
      #[Handler.statelessPlanned reluNonnegativeRule
          (reluPlan .nonnegative) #[reluFormat .nonnegative],
        Handler.statelessPlanned reluNegativeRule
          (reluPlan .negative) #[reluFormat .negative]] }

private def reluPackages : Array (Package Bound) := #[sourcePackage, reluPackage]

private def reluSplitPackages : Array (Package Bound) :=
  #[sourcePackage, reluPackage, splitPackage]

private def reluModel : OperationSemantics.Model ℝ :=
  { operation := reluOperation
    relation := fun inputs output =>
      match inputs with
      | [input] => output = max input 0
      | _ => False }

private def reluModels : Array (OperationSemantics.Model ℝ) :=
  #[sourceModel, reluModel]

private def reluSemantics : Semantics Bound :=
  OperationSemantics.semantics reluModels Contains

private def reluBoundSchema : FactDomainSchema reluSemantics :=
  { top := fun _ => .all
    topSound := by
      intro _ _ _ _ _ _
      trivial
    proveMeet := fun _ _ previous proposed installed =>
      if exact : installed = previous.meet proposed then
        some
          { proof := by
              subst installed
              intro valuation _
              exact containsMeet previous proposed (valuation _) }
      else
        none }

private def reluLaws : Laws reluSemantics :=
  { holdsEq := by
      intro _ valuation left right fact _ _ values
      change Contains fact (valuation left) ↔ Contains fact (valuation right)
      rw [values] }

private def reluStableLaw : GenericInstanceReconstruction.StableLaw reluSemantics :=
  OperationSemantics.stableLaw reluModels Contains

private def reluSplitSchema : SplitSchema reluSemantics Unit where
  proveCover := fun _ _ parent _ left right =>
    if shape : parent = .all ∧ left = .nonnegative ∧ right = .negative then
      some
        { proof := by
            rcases shape with ⟨rfl, rfl, rfl⟩
            intro valuation _ _
            change NodeId → ℝ at valuation
            change (0 : ℝ) ≤ valuation _ ∨ valuation _ < 0
            exact le_or_gt 0 (valuation _) }
    else
      none

private theorem reluSideEntails (side : Bound)
    (accepted : side = .nonnegative ∨ side = .negative)
    (graph : Program) (assumptions : List (NodeFact Bound))
    (output : NodeId) (instruction : Node) (input : NodeId)
    (found : graph.node? output = some instruction)
    (operation : instruction.op = { index := 1 })
    (arguments : instruction.args = [input])
    (exactAssumptions : assumptions = [{ node := input, fact := side }]) :
    reluSemantics.Entails graph assumptions
      { node := output, fact := .nonnegative } := by
  change ∀ valuation : NodeId → ℝ,
    OperationSemantics.Models reluModels graph valuation →
      (∀ assumption, assumption ∈ assumptions →
        Contains assumption.fact (valuation assumption.node)) →
      Contains .nonnegative (valuation output)
  intro valuation model holds
  obtain ⟨meaning, meaningAt, related⟩ :=
    model.2 output instruction found
  simp [reluModels, operation] at meaningAt
  subst meaning
  have outputEq : valuation output = max (valuation input) 0 := by
    simpa [reluModel, arguments, List.map] using related
  have inputH : Contains side (valuation input) :=
    holds { node := input, fact := side } (by simp [exactAssumptions])
  rcases accepted with rfl | rfl
  · change (0 : ℝ) ≤ valuation output
    rw [outputEq, max_eq_left inputH]
    exact inputH
  · change (0 : ℝ) ≤ valuation output
    change valuation input < 0 at inputH
    rw [outputEq, max_eq_right inputH.le]

private theorem reluFactWith (fact : NodeFact Bound) {value : Bound}
    (equal : fact.fact = value) :
    fact = { node := fact.node, fact := value } := by
  cases fact
  simp_all

private def reluFactSchema (key : RuleKey) (side : Bound)
    (accepted : side = .nonnegative ∨ side = .negative) :
    PackedFactSchema reluSemantics where
  rule := key
  schema := 1
  Certificate := Unit
  decode := fun body => if body == [side.code] then some () else none
  replay := fun _ _ context _ =>
    if proposedFact : context.proposed.fact = .nonnegative then
      match found : context.program.node? context.proposed.node with
      | some instruction =>
          if operation : instruction.op = ({ index := 1 } : OpId) then
            match arguments : instruction.args with
            | [input] =>
                if exactAssumptions :
                    context.assumptions = [{ node := input, fact := side }] then
                  some
                    { proof := by
                        have proposedEq :
                            context.proposed =
                              { node := context.proposed.node,
                                fact := .nonnegative } :=
                          reluFactWith context.proposed proposedFact
                        rw [proposedEq]
                        exact
                          reluSideEntails side accepted context.program
                            context.assumptions context.proposed.node instruction
                            input found operation arguments exactAssumptions }
                else
                  none
            | _ => none
          else
            none
      | none => none
    else
      none

private def reluNonnegativeSchema : PackedFactSchema reluSemantics :=
  reluFactSchema reluNonnegativeKey .nonnegative (Or.inl rfl)

private def reluNegativeSchema : PackedFactSchema reluSemantics :=
  reluFactSchema reluNegativeKey .negative (Or.inr rfl)

private def reluSourceProof : ProofRegistry.Package reluSemantics Name :=
  { semantic := { factSchemas := #[] }
    emit := { schemas := [] } }

private def reluProof : ProofRegistry.Package reluSemantics Name :=
  { semantic :=
      { factSchemas := #[reluNonnegativeSchema, reluNegativeSchema] }
    emit :=
      { schemas :=
          [{ key := reluNonnegativeSchema.key,
             handle := ``reluNonnegativeSchema },
           { key := reluNegativeSchema.key,
             handle := ``reluNegativeSchema }] } }

private def reluProofPackages :
    Array (ProofRegistry.Package reluSemantics Name) :=
  #[reluSourceProof, reluProof]

private def reluSplitProof : ProofRegistry.Package reluSemantics Name :=
  { semantic := { factSchemas := #[] }
    emit := { schemas := [] } }

private def reluSplitProofPackages :
    Array (ProofRegistry.Package reluSemantics Name) :=
  #[reluSourceProof, reluProof, reluSplitProof]

private def reluBaseFacts : List (NodeFact Bound) :=
  [{ node := node 0, fact := .all }, { node := node 1, fact := .all }]

private def reluInput : CheckerInput Bound :=
  { baseProgram := reluProgram
    initialFacts := #[.all, .all]
    target := { node := node 1, fact := .nonnegative } }

private theorem reluBaseWithin : FactsWithin reluProgram reluBaseFacts := by
  intro fact member
  simp only [reluBaseFacts, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl <;> simp [reluProgram, node]

private theorem reluBasePrefix : ProgramPrefix reluProgram reluProgram :=
  ProgramPrefix.refl reluProgram

private theorem reluSameOperations :
    reluProgram.operations = reluProgram.operations := rfl

private def reluInitialExtension :
    Evidence (reluSemantics.Extends reluProgram reluProgram) :=
  extendRefl reluSemantics reluProgram

private noncomputable def reluValuation (x : ℝ) : NodeId → ℝ
  | ⟨0⟩ => x
  | ⟨1⟩ => max x 0
  | _ => 0

private theorem reluValuationModels (x : ℝ) :
    reluSemantics.models reluProgram (reluValuation x) := by
  refine ⟨?_, ?_⟩
  · simp [reluProgram, reluOperations, reluModels, sourceModel, reluModel]
  rintro ⟨index⟩ instruction found
  cases index with
  | zero =>
      simp [Program.node?, reluProgram, sourceInstruction] at found
      subst instruction
      exact ⟨sourceModel, by rfl, by rfl⟩
  | succ index =>
      cases index with
      | zero =>
          simp [Program.node?, reluProgram, reluInstruction] at found
          subst instruction
          exact ⟨reluModel, by rfl, by rfl⟩
      | succ index =>
          simp [Program.node?, reluProgram] at found

private theorem closeRelu (x : ℝ)
    (result : Evidence
      (reluSemantics.Entails reluProgram reluBaseFacts reluInput.target)) :
    0 ≤ max x 0 := by
  have holds := result.proof (reluValuation x) (reluValuationModels x)
    (by
      intro fact member
      simp only [reluBaseFacts, List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl <;> trivial)
  exact holds

private def reluOffer? (key : RuleKey) (view : Propagator.Policy.View Bound) :
    Option Propagator.Policy.OfferView :=
  view.offers.toList.find? fun offer =>
    match offer.key with
    | .invoke invocation => invocation.rule == key
    | _ => false

private def reluRulePolicy (key : RuleKey) :
    TargetRun.Controller Bound Unit :=
  { update := fun state _ => state
    choose := fun state view =>
      match reluOffer? key view with
      | some offer => .select offer state
      | none => .stop state }

private def reluRunWith? (runtimePackages : Array (Package Bound))
    (input : CheckerInput Bound) (controller : TargetRun.Controller Bound Unit)
    (scope : Propagator.Policy.ScopeId := { index := 0 }) :
    Option (TargetRun.Result Bound Unit) := do
  let .ok session := PolicySession.Session.start factDomain
      input.baseProgram runtimePackages input.initialFacts limits scope
    | none
  some (TargetRun.drive factDomain input.target.node input.target.fact controller
    limits.policy.maxDecisions session ())

private def reluPrepared? :
    Option (ULift.{1, 0} (BranchStart.Children Bound)) :=
  match reluRunWith? reluSplitPackages reluInput splitPolicy with
  | none => none
  | some result =>
      match result.stop with
      | .split plan =>
          match BranchStart.prepare branchLimits
              (BranchStart.State.start { index := 0 }) 0 result.session plan
              reluInput.target signSplitter with
          | .ok (_, children) => some (ULift.up children)
          | .error _ => none
      | _ => none

private def reluBranchFact (side : Bound) : NodeFact Bound :=
  { node := node 0, fact := side }

private def reluBranchFacts (side : Bound) : List (NodeFact Bound) :=
  reluBranchFact side :: reluBaseFacts

private def reluBranchInput (side : Bound) : CheckerInput Bound :=
  { baseProgram := reluProgram
    initialFacts := #[side, .all]
    target := reluInput.target }

private def reluInherit (side : Bound) (observed : NodeId)
    (different : observed ≠ node 0) (fact : Bound)
    (found : (reluBranchInput side).initialFacts[observed.index]? = some fact) :
    Evidence
      (reluSemantics.Entails reluProgram reluBaseFacts { node := observed, fact }) :=
  { proof := by
      intro _ _ assumptions
      cases observed with
      | mk index =>
          cases index with
          | zero => simp [node] at different
          | succ index =>
              cases index with
              | zero =>
                  simp [reluBranchInput] at found
                  subst fact
                  exact assumptions _ (by simp [reluBaseFacts, node])
              | succ index => simp [reluBranchInput] at found }

private def reluLeftInput : CheckerInput Bound :=
  reluBranchInput .nonnegative

private def reluRightInput : CheckerInput Bound :=
  reluBranchInput .negative

private def reluLeftFacts : List (NodeFact Bound) :=
  reluBranchFacts .nonnegative

private def reluRightFacts : List (NodeFact Bound) :=
  reluBranchFacts .negative

private def reluLeftSeed :
    ProofEmitter.BranchSeed reluSemantics reluLeftInput reluBaseFacts
      (reluBranchFact .nonnegative) :=
  ProofEmitter.BranchSeed.make reluLeftInput (reluBranchFact .nonnegative)
    (by rfl) (by rfl) (reluInherit .nonnegative)

private def reluRightSeed :
    ProofEmitter.BranchSeed reluSemantics reluRightInput reluBaseFacts
      (reluBranchFact .negative) :=
  ProofEmitter.BranchSeed.make reluRightInput (reluBranchFact .negative)
    (by rfl) (by rfl) (reluInherit .negative)

private structure ReluRun where
  session : PolicySession.Session Bound
  registry : ProofRegistry.Registry reluSemantics Name
  reached : TargetRun.Reached Bound

private def reluRunChild? (side : Bound) (input : CheckerInput Bound)
    (scope : Propagator.Policy.ScopeId) : Option ReluRun := do
  let key := if side == .nonnegative then reluNonnegativeKey else reluNegativeKey
  let result ← reluRunWith? reluPackages input (reluRulePolicy key) scope
  let .target reached := result.stop | none
  let .ok registry := ProofRegistry.build result.session.registry reluProofPackages
    | none
  some { session := result.session, registry, reached }

private def reluTreePolicy : TargetRun.Controller Bound Unit :=
  { update := fun state _ => state
    choose := fun state view =>
      let selected :=
        if view.scope.index == 0 then splitOffer? view
        else if view.scope.index == 1 then reluOffer? reluNonnegativeKey view
        else if view.scope.index == 2 then reluOffer? reluNegativeKey view
        else none
      match selected with
      | some offer => .select offer state
      | none => .stop state }

private def reluTreeConfig (resources : BranchTree.Limits) :
    BranchTree.Config Bound Unit :=
  { factDomain
    packages := reluSplitPackages
    sessionLimits := limits
    controller := reluTreePolicy
    splitter := signSplitter
    forkPolicy := fun state _ => state
    order := .depthFirst
    limits := resources }

private def reluTree? (resources : BranchTree.Limits := treeLimits) :
    Option (BranchTree.State Bound Unit) := do
  let .ok state := BranchTree.start (reluTreeConfig resources) { index := 0 }
      reluInput () | none
  let .ok state := BranchTree.run (reluTreeConfig resources) state | none
  some state

#guard
  reluTree?.any fun state =>
    state.settled && state.nodes.size == 3 && state.steps == 3 &&
      state.splits == 1 && state.leaves == 2 &&
      match state.nodes[1]?, state.nodes[2]? with
      | some (BranchTree.Node.leaf left (BranchTree.LeafEnd.result leftRun)),
          some (BranchTree.Node.leaf right (BranchTree.LeafEnd.result rightRun)) =>
          left.scope.index == 1 && left.input.initialFacts == #[.nonnegative, .all] &&
            right.scope.index == 2 && right.input.initialFacts == #[.negative, .all] &&
            (match leftRun.stop with | .target _ => true | _ => false) &&
            (match rightRun.stop with | .target _ => true | _ => false)
      | _, _ => false

#guard
  reluPrepared?.any fun lifted =>
    let children := lifted.down
    children.leftScope == ({ index := 1 } : Propagator.Policy.ScopeId) &&
      children.rightScope == ({ index := 2 } : Propagator.Policy.ScopeId) &&
      children.left.baseProgram == reluLeftInput.baseProgram &&
      children.left.initialFacts == reluLeftInput.initialFacts &&
      children.left.target == reluLeftInput.target &&
      children.right.baseProgram == reluRightInput.baseProgram &&
      children.right.initialFacts == reluRightInput.initialFacts &&
      children.right.target == reluRightInput.target

private def reluTraceUses? (side : Bound) (input : CheckerInput Bound)
    (scope : Propagator.Policy.ScopeId) : Bool :=
  match reluRunChild? side input scope with
  | none => false
  | some run =>
      match Frontend.trace? run.session.state.engine run.session.arena with
      | some trace =>
          match trace.events with
          | [.rule step] =>
              step.assumptions == [reluBranchFact side] &&
                step.event.fact == .nonnegative &&
                step.entry.replayKey ==
                  (if side == .nonnegative then reluNonnegativeSchema.key
                   else reluNegativeSchema.key)
          | _ => false
      | none => false

#guard reluTraceUses? .nonnegative reluLeftInput { index := 1 }
#guard reluTraceUses? .negative reluRightInput { index := 2 }

private def reluRejectsUnsplit? (key : RuleKey) : Bool :=
  reluRunWith? reluPackages reluInput (reluRulePolicy key) |>.any fun result =>
    (match result.stop with | .target _ => false | _ => true) &&
      result.session.state.engine.facts == #[.all, .all] &&
      result.session.state.engine.history.isEmpty

#guard reluRejectsUnsplit? reluNonnegativeKey
#guard reluRejectsUnsplit? reluNegativeKey

private theorem reluBranchWithin (side : Bound) :
    FactsWithin reluProgram (reluBranchFacts side) := by
  intro fact member
  simp only [reluBranchFacts, reluBranchFact, reluBaseFacts, List.mem_cons,
    List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl <;> simp [reluProgram, node]

private def reluSeedAssumed (graph : Program) (base : List (NodeFact Bound))
    (index : Nat) (fact : NodeFact Bound) (found : base[index]? = some fact) :
    Evidence (reluSemantics.Entails graph base fact) :=
  ProofEmitter.assumedAt graph base index fact found

private def reluContext (input facts within : Expr)
    (factValues : List (NodeFact Bound)) : ProofFrontend.Context Bound Name :=
  { encoder := boundEncoder
    resolveSchema := pure
    semantics := mkConst ``reluSemantics
    domain := mkConst ``reluBoundSchema
    laws := mkConst ``reluLaws
    stableLaw := mkConst ``reluStableLaw
    input
    assumed := ``reluSeedAssumed
    baseFacts := factValues
    baseFactsTerm := facts
    baseProgram := reluProgram
    baseProgramTerm := mkConst ``reluProgram
    basePrefix := mkConst ``reluBasePrefix
    baseWithin := within
    initialExtension := mkConst ``reluInitialExtension
    finalPrefix := mkConst ``reluBasePrefix
    sameOperations := mkConst ``reluSameOperations
    top := reluBoundSchema.top }

private def reluLeftContext : ProofFrontend.Context Bound Name :=
  reluContext (mkConst ``reluLeftInput) (mkConst ``reluLeftFacts)
    (mkApp (mkConst ``reluBranchWithin) (mkConst ``Bound.nonnegative))
    reluLeftFacts

private def reluRightContext : ProofFrontend.Context Bound Name :=
  reluContext (mkConst ``reluRightInput) (mkConst ``reluRightFacts)
    (mkApp (mkConst ``reluBranchWithin) (mkConst ``Bound.negative))
    reluRightFacts

private def reluParent : Evidence
    (reluSemantics.Entails reluProgram reluBaseFacts (reluBranchFact .all)) :=
  ProofEmitter.assumed (by simp [reluBaseFacts, reluBranchFact, node])

private meta def emitReluChild (context : ProofFrontend.Context Bound Name)
    (side : Bound) (input : CheckerInput Bound)
    (scope : Propagator.Policy.ScopeId) (seed : Expr) : MetaM Expr := do
  let some run := reluRunChild? side input scope
    | throwError "interval_relu_split: child search failed"
  let some trace := Frontend.trace? run.session.state.engine run.session.arena
    | throwError "interval_relu_split: child chronology quotation failed"
  let state ← ProofFrontend.emitBranch context input seed trace.program
    trace.events run.registry.emit
  ProofFrontend.closeTarget context state run.reached.seen run.reached.fact input.target

private meta def emitReluSplit : MetaM Expr := do
  let some lifted := reluPrepared?
    | throwError "interval_relu_split: branch preparation failed"
  let children := lifted.down
  let left ← emitReluChild reluLeftContext .nonnegative children.left
    children.leftScope (mkConst ``reluLeftSeed)
  let right ← emitReluChild reluRightContext .negative children.right
    children.rightScope (mkConst ``reluRightSeed)
  let result ←
    mkAppM ``ProofEmitter.replaySplit
      #[mkConst ``reluSplitSchema, mkConst ``reluProgram,
        mkConst ``reluBaseFacts, ← boundEncoder.nodeId (node 0),
        ← boundEncoder.fact .all, mkConst ``Unit.unit,
        ← boundEncoder.fact .nonnegative, ← boundEncoder.fact .negative,
        ← boundEncoder.nodeFact reluInput.target,
        mkConst ``reluParent, left, right]
  ProofFrontend.replayResult result

/-- The emitted term contains both live child replays and the checked generic
split join.  Assigning that term to this declaration makes the ordinary kernel,
not the Meta evaluator, validate the complete proof. -/
private def reluJoined : Evidence
    (reluSemantics.Entails reluProgram reluBaseFacts reluInput.target) := by
  run_tac
    let goal ← getMainGoal
    goal.assign (← emitReluSplit)

/-- A genuinely branch-dependent arbitrary-function vertical: neither ReLU
propagator fires before the zero split, and each child proof consumes its own
strictly narrower source fact before the generic join closes the theorem. -/
theorem tacticReluSplit (x : ℝ) : 0 ≤ max x 0 :=
  closeRelu x reluJoined

private meta def emitReluTreeLeaf (source : BranchTree.Leaf Bound Unit)
    (run : TargetRun.Result Bound Unit) : MetaM Expr := do
  let .target reached := run.stop
    | throwError "interval_relu_tree: leaf did not reach its target"
  let .ok registry := ProofRegistry.build run.session.registry reluSplitProofPackages
    | throwError "interval_relu_tree: child proof registry failed"
  let some trace := Frontend.trace? run.session.state.engine run.session.arena
    | throwError "interval_relu_tree: child chronology quotation failed"
  let (context, seed) ←
    match source.input.initialFacts[0]? with
    | some .nonnegative =>
        unless source.scope.index == 1 do
          throwError "interval_relu_tree: left child has the wrong scope"
        pure (reluLeftContext, mkConst ``reluLeftSeed)
    | some .negative =>
        unless source.scope.index == 2 do
          throwError "interval_relu_tree: right child has the wrong scope"
        pure (reluRightContext, mkConst ``reluRightSeed)
    | _ => throwError "interval_relu_tree: leaf has no split-side fact"
  let state ← ProofFrontend.emitBranch context source.input seed trace.program
    trace.events registry.emit
  ProofFrontend.closeTarget context state reached.seen reached.fact source.input.target

private meta def emitReluTreeSplit (source : BranchTree.Leaf Bound Unit)
    (run : TargetRun.Result Bound Unit) (children : BranchStart.Children Bound)
    (left right : Expr) : MetaM Expr := do
  let .split plan := run.stop
    | throwError "interval_relu_tree: internal node did not retain a split"
  unless source.scope.index == 0 &&
      BranchProof.sameInput source.input reluInput &&
      BranchProof.sameInput children.parent reluInput &&
      BranchProof.sameInput children.left reluLeftInput &&
      BranchProof.sameInput children.right reluRightInput &&
      children.leftScope.index == 1 && children.rightScope.index == 2 &&
      plan.node == node 0 && plan.fact == .all && plan.point == 0 do
    throwError "interval_relu_tree: retained split does not match the proof adapter"
  let result ←
    mkAppM ``ProofEmitter.replaySplit
      #[mkConst ``reluSplitSchema, mkConst ``reluProgram,
        mkConst ``reluBaseFacts, ← boundEncoder.nodeId (node 0),
        ← boundEncoder.fact .all, mkConst ``Unit.unit,
        ← boundEncoder.fact .nonnegative, ← boundEncoder.fact .negative,
        ← boundEncoder.nodeFact reluInput.target,
        mkConst ``reluParent, left, right]
  ProofFrontend.replayResult result

private def reluTreeEmitter : BranchProof.Emitter Bound Unit :=
  { leaf := emitReluTreeLeaf
    split := emitReluTreeSplit }

private def reluProofLimits : BranchProof.Limits :=
  { maxNodes := 16, maxDepth := 8 }

/-- Unlike `reluJoined`, this ordinary proof term is produced by folding the
generic retained tree rather than by a fixed two-child orchestration. -/
private def reluTreeJoined : Evidence
    (reluSemantics.Entails reluProgram reluBaseFacts reluInput.target) := by
  run_tac
    let some tree := reluTree?
      | throwError "interval_relu_tree: runtime tree failed"
    let goal ← getMainGoal
    goal.assign (← BranchProof.emit reluProofLimits reluTreeEmitter tree
      (← goal.getType))

theorem tacticReluTree (x : ℝ) : 0 ≤ max x 0 :=
  closeRelu x reluTreeJoined

/--
info: 'Hex.IntervalMathlib.ReluConformance.tacticReluTree' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms tacticReluTree

set_option linter.unusedTactic false in
example : True := by
  run_tac
    let expected ← inferType (mkConst ``reluJoined)
    let partialResources := treeLimits (maxSteps := 1)
    let some partialTree := reluTree? partialResources
      | throwError "interval_relu_tree test: partial tree failed"
    if (← observing? <| BranchProof.emit reluProofLimits reluTreeEmitter partialTree
        expected).isSome then
      throwError "interval_relu_tree test: pending children produced a proof"
    let some tree := reluTree?
      | throwError "interval_relu_tree test: complete tree failed"
    let some root := tree.nodes[0]?
      | throwError "interval_relu_tree test: root is missing"
    let BranchTree.Node.split source run children left _ := root
      | throwError "interval_relu_tree test: root is not a split"
    let shared :=
      { tree with
        nodes := tree.nodes.set! 0
          (BranchTree.Node.split source run children left left) }
    if (← observing? <| BranchProof.emit reluProofLimits reluTreeEmitter shared
        expected).isSome then
      throwError "interval_relu_tree test: a shared sibling produced a proof"
    let some extra := tree.nodes[1]?
      | throwError "interval_relu_tree test: child is missing"
    let unreachable := { tree with nodes := tree.nodes.push extra }
    if (← observing? <| BranchProof.emit reluProofLimits reluTreeEmitter unreachable
        expected).isSome then
      throwError "interval_relu_tree test: an unreachable node produced a proof"
  trivial

set_option linter.unusedTactic false in
example : True := by
  run_tac
    let checkMutation (context : ProofFrontend.Context Bound Name)
        (side wrong : Bound) (input : CheckerInput Bound)
        (scope : Propagator.Policy.ScopeId) (seed : Expr) : MetaM Unit := do
      let some run := reluRunChild? side input scope
        | throwError "interval_relu_split mutation: child search failed"
      let some trace := Frontend.trace? run.session.state.engine run.session.arena
        | throwError "interval_relu_split mutation: trace missing"
      let [.rule step] := trace.events
        | throwError "interval_relu_split mutation: wrong trace shape"
      let mutated : RuleStep Bound :=
        { step with assumptions := [reluBranchFact wrong] }
      if (← observing? <| ProofFrontend.emitBranch context input seed trace.program
          [.rule mutated] run.registry.emit).isSome then
        throwError
          "interval_relu_split mutation: opposite split assumption was accepted"
    checkMutation reluLeftContext .nonnegative .negative reluLeftInput
      { index := 1 } (mkConst ``reluLeftSeed)
    checkMutation reluRightContext .negative .nonnegative reluRightInput
      { index := 2 } (mkConst ``reluRightSeed)
  trivial

end Hex.IntervalMathlib.ReluConformance
