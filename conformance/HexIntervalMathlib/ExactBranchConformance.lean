/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import HexIntervalMathlib.Experiment.Centered
import HexInterval.Experiment.BranchProof
import HexInterval.Experiment.OperationSemantics
import HexInterval.Experiment.PayloadSession
import HexInterval.Experiment.ProofRegistry
import Mathlib.Lean.Elab.Tactic.Meta

/-!
# Exact contraction, split, and branch-dependent replay

A live backward contractor narrows `x` from the whole line to `[1/4, 3/4]`.
The retained post-run snapshot is split exactly at `1/2`. The left child proves
an absolute-distance bound from `[1/4, 1/2]`; the right child combines
`(1/2, 3/4]` with an identity guard bounded above by `1/2`, derives exact
empty, and closes through package-owned refutation.
-/

namespace Hex.IntervalMathlib.ExactBranchConformance

open Lean Elab Tactic Meta
open Hex.Interval Hex.Interval.Experiment
open Propagator PayloadArena PolicySession SemanticReplay ChronologicalReplay
open ProofEmitter ProofFrontend ProofRegistry FrontendEncoder
open GenericInstanceReconstruction
open DyadicInterval DyadicRules Centered

private def real : DomainId := { index := 0 }
private def node (index : Nat) : NodeId := { index }
private def payload (index : Nat) : PayloadId := { index }

private def leftRange : DyadicInterval.Fact :=
  ⟨.bounds (.finite quarter false) (.finite half false), by decide⟩

private def rightRange : DyadicInterval.Fact :=
  ⟨.bounds (.finite half true) (.finite threeQuarters false), by decide⟩

private def guardRange : DyadicInterval.Fact :=
  ⟨.bounds .unbounded (.finite half false), by decide⟩

private def distanceRange : DyadicInterval.Fact :=
  ⟨.bounds (.finite 0 false) (.finite quarter false), by decide⟩

private def sourceKey : OpKey := { name := "exact-branch.source" }
private def guardKey : OpKey := { name := "exact-branch.identity-guard" }
private def distanceKey : OpKey := { name := "exact-branch.distance" }

private def backwardKey : RuleKey := { name := "exact-branch.centered-backward" }
private def splitKey : RuleKey := { name := "exact-branch.split-half" }
private def leftKey : RuleKey := { name := "exact-branch.distance-left" }
private def rejectKey : RuleKey := { name := "exact-branch.reject-right" }

private def sourceOperation : Operation :=
  { key := sourceKey, inputs := [], output := real }

private def centeredOperation : Operation :=
  { key := centeredOp, inputs := [real], output := real }

private def guardOperation : Operation :=
  { key := guardKey, inputs := [real], output := real }

private def distanceOperation : Operation :=
  { key := distanceKey, inputs := [real, real], output := real }

private def operations : Array Operation :=
  #[sourceOperation, centeredOperation, guardOperation, distanceOperation]

private def sourceInstruction : Node :=
  { domain := real, op := { index := 0 }, args := [] }
private def centeredInstruction : Node :=
  { domain := real, op := { index := 1 }, args := [node 0] }
private def guardInstruction : Node :=
  { domain := real, op := { index := 2 }, args := [node 0] }
private def distanceInstruction : Node :=
  { domain := real, op := { index := 3 }, args := [node 0, node 2] }

private def program : Program :=
  { operations
    nodes := #[sourceInstruction, centeredInstruction, guardInstruction,
      distanceInstruction] }

private def backwardRule : Registration :=
  { key := backwardKey, head := centeredOp, kind := .backward
    watches := [.result], writes := [.argument 0] }
private def splitRule : Registration :=
  { key := splitKey, head := centeredOp, kind := .split
    watches := [.argument 0], writes := [] }
private def leftRule : Registration :=
  { key := leftKey, head := distanceKey, kind := .forward
    watches := [.argument 0, .argument 1], writes := [.result] }
private def rejectRule : Registration :=
  { key := rejectKey, head := distanceKey, kind := .forward
    watches := [.argument 0, .argument 1], writes := [.result] }

private def emptyFormat : ReplayFormat :=
  { role := .fact, schema := 0, validateBody := fun body => body.isEmpty }

private def factPlan (target : NodeId) (fact : DyadicInterval.Fact) :
    Plan DyadicInterval.Fact :=
  { outcome :=
      .success [{ node := target, fact, payload := payload 0 }] []
        { visitedEntries := 1, estimatedProofNodes := 1 }
    drafts := [{ label := payload 0, role := .fact, schema := 0, body := [] }] }

private def backwardPlan (request : RuleRequest DyadicInterval.Fact) :
    Plan DyadicInterval.Fact :=
  match request.inputs, request.writes with
  | [output], [input] =>
      if output.fact == highRange then factPlan input middleRange
      else { outcome := .inapplicable, drafts := [] }
  | _, _ => { outcome := .failed 1, drafts := [] }

private def splitPlan (request : RuleRequest DyadicInterval.Fact) :
    Outcome DyadicInterval.Fact :=
  match request.inputs, request.writes with
  | [input], [] =>
      .success []
        [.split { node := input.node, point := half, reason := .criticalPoint }]
        { visitedEntries := 1, estimatedProofNodes := 1 }
  | _, _ => .failed 2

private def leftPlan (request : RuleRequest DyadicInterval.Fact) :
    Plan DyadicInterval.Fact :=
  match request.inputs, request.writes with
  | [input, guard], [target] =>
      if input.fact == leftRange && guard.fact == guardRange then
        factPlan target distanceRange
      else { outcome := .inapplicable, drafts := [] }
  | _, _ => { outcome := .failed 3, drafts := [] }

private def rejectPlan (request : RuleRequest DyadicInterval.Fact) :
    Plan DyadicInterval.Fact :=
  match request.inputs, request.writes with
  | [input, guard], [target] =>
      if input.fact == rightRange && guard.fact == guardRange then
        factPlan target .empty
      else { outcome := .inapplicable, drafts := [] }
  | _, _ => { outcome := .failed 4, drafts := [] }

private def runtimePackage : Propagator.Package DyadicInterval.Fact :=
  { Cache := Unit
    cache := ()
    operations
    handlers :=
      #[Handler.statelessPlanned backwardRule backwardPlan #[emptyFormat],
        Handler.statelessDroppingDrafts splitRule splitPlan,
        Handler.statelessPlanned leftRule leftPlan #[emptyFormat],
        Handler.statelessPlanned rejectRule rejectPlan #[emptyFormat]] }

private def runtimePackages : Array (Propagator.Package DyadicInterval.Fact) :=
  #[runtimePackage]

private def sourceModel : OperationSemantics.Model ℝ :=
  { operation := sourceOperation, relation := fun inputs _ => inputs = [] }
private def centeredModel : OperationSemantics.Model ℝ :=
  { operation := centeredOperation
    relation := fun inputs output =>
      match inputs with
      | [input] => output = (1 / 4 : ℝ) - (input - (1 / 2 : ℝ)) ^ 2
      | _ => False }
private def guardModel : OperationSemantics.Model ℝ :=
  { operation := guardOperation
    relation := fun inputs output =>
      match inputs with | [input] => output = input | _ => False }
private def distanceModel : OperationSemantics.Model ℝ :=
  { operation := distanceOperation
    relation := fun inputs output =>
      match inputs with
      | [input, _] => output = |input - (1 / 2 : ℝ)|
      | _ => False }

private def models : Array (OperationSemantics.Model ℝ) :=
  #[sourceModel, centeredModel, guardModel, distanceModel]
private def semantics : Semantics DyadicInterval.Fact :=
  OperationSemantics.semantics models DyadicInterval.Fact.Contains
private def endpointLimit : EndpointLimit := Centered.endpointLimit
private def domain : FactDomainSchema semantics :=
  DyadicInterval.factSchema endpointLimit (OperationSemantics.Models models)
private def laws : Laws semantics :=
  { holdsEq := by
      intro _ valuation left right fact _ _ values
      change fact.Contains (valuation left) ↔ fact.Contains (valuation right)
      rw [values] }
private def stableLaw : StableLaw semantics :=
  OperationSemantics.stableLaw models DyadicInterval.Fact.Contains

private theorem factWith (fact : NodeFact DyadicInterval.Fact)
    {value : DyadicInterval.Fact} (equal : fact.fact = value) :
    fact = { node := fact.node, fact := value } := by
  cases fact
  simp_all

private theorem backwardEntails (graph : Program)
    (assumptions : List (NodeFact DyadicInterval.Fact))
    (input output : NodeId) (instruction : Node)
    (found : graph.node? output = some instruction)
    (operation : instruction.op = ({ index := 1 } : OpId))
    (arguments : instruction.args = [input])
    (exact : assumptions = [{ node := output, fact := highRange }]) :
    semantics.Entails graph assumptions { node := input, fact := middleRange } := by
  intro valuation model assumptionHolds
  change NodeId → ℝ at valuation
  change OperationSemantics.Models models graph valuation at model
  obtain ⟨meaning, meaningAt, related⟩ := model.2 output instruction found
  simp [models, operation] at meaningAt
  subst meaning
  have outputEq :
      valuation output = (1 / 4 : ℝ) - (valuation input - (1 / 2 : ℝ)) ^ 2 := by
    simpa [centeredModel, arguments, List.map] using related
  have outputRange := assumptionHolds { node := output, fact := highRange } (by
    simp [exact])
  change highRange.Contains (valuation output) at outputRange
  change middleRange.Contains (valuation input)
  simp only [highRange, middleRange, DyadicInterval.Fact.Contains, rawContains,
    lowerContains, upperContains, toReal_threeSixteenths, toReal_quarter,
    toReal_threeQuarters] at outputRange ⊢
  rw [outputEq] at outputRange
  constructor <;>
    nlinarith [sq_nonneg (valuation input - (1 / 4 : ℝ)),
      sq_nonneg (valuation input - (3 / 4 : ℝ))]

private theorem leftEntails (graph : Program)
    (assumptions : List (NodeFact DyadicInterval.Fact))
    (output input guard : NodeId) (instruction : Node)
    (found : graph.node? output = some instruction)
    (operation : instruction.op = ({ index := 3 } : OpId))
    (arguments : instruction.args = [input, guard])
    (exact : assumptions =
      [{ node := input, fact := leftRange }, { node := guard, fact := guardRange }]) :
    semantics.Entails graph assumptions { node := output, fact := distanceRange } := by
  intro valuation model assumptionHolds
  change NodeId → ℝ at valuation
  change OperationSemantics.Models models graph valuation at model
  obtain ⟨meaning, meaningAt, related⟩ := model.2 output instruction found
  simp [models, operation] at meaningAt
  subst meaning
  have outputEq : valuation output = |valuation input - (1 / 2 : ℝ)| := by
    simpa [distanceModel, arguments, List.map] using related
  have inputRange := assumptionHolds { node := input, fact := leftRange } (by
    simp [exact])
  change leftRange.Contains (valuation input) at inputRange
  change distanceRange.Contains (valuation output)
  simp only [leftRange, distanceRange, DyadicInterval.Fact.Contains, rawContains,
    lowerContains, upperContains, DyadicInterval.toReal_zero, toReal_quarter,
    toReal_half] at inputRange ⊢
  rw [outputEq, abs_of_nonpos (by linarith [inputRange.2])]
  constructor <;> linarith [inputRange.1, inputRange.2]

private theorem rejectEntails (graph : Program)
    (assumptions : List (NodeFact DyadicInterval.Fact))
    (output input guard : NodeId) (guardInstruction : Node)
    (guardFound : graph.node? guard = some guardInstruction)
    (guardOperationAt : guardInstruction.op = ({ index := 2 } : OpId))
    (guardArguments : guardInstruction.args = [input])
    (exact : assumptions =
      [{ node := input, fact := rightRange }, { node := guard, fact := guardRange }]) :
    semantics.Entails graph assumptions { node := output, fact := .empty } := by
  intro valuation model assumptionHolds
  change NodeId → ℝ at valuation
  change OperationSemantics.Models models graph valuation at model
  have inputRange := assumptionHolds { node := input, fact := rightRange } (by
    simp [exact])
  have guardHolds := assumptionHolds { node := guard, fact := guardRange } (by
    simp [exact])
  obtain ⟨meaning, meaningAt, related⟩ := model.2 guard guardInstruction guardFound
  simp [models, guardOperationAt] at meaningAt
  subst meaning
  have guardEq : valuation guard = valuation input := by
    simpa [guardModel, guardArguments, List.map] using related
  change rightRange.Contains (valuation input) at inputRange
  change guardRange.Contains (valuation guard) at guardHolds
  change DyadicInterval.Fact.empty.Contains (valuation output)
  simp only [rightRange, guardRange, DyadicInterval.Fact.Contains, rawContains,
    lowerContains, upperContains, toReal_half, toReal_threeQuarters,
    true_and] at inputRange guardHolds
  rw [guardEq] at guardHolds
  exfalso
  linarith [inputRange.1, guardHolds]

private def backwardSchema : PackedFactSchema semantics where
  rule := backwardKey
  schema := 0
  Certificate := Unit
  decode := fun body => if body.isEmpty then some () else none
  replay := fun _ _ context _ =>
    if proposed : context.proposed.fact = middleRange then
      match context.assumptions with
      | [{ node := output, fact := outputFact }] =>
          if outputExact : outputFact = highRange then
            match found : context.program.node? output with
            | some instruction =>
                if operation : instruction.op = ({ index := 1 } : OpId) then
                  match arguments : instruction.args with
                  | [input] =>
                      if sameInput : input = context.proposed.node then
                        some
                          { proof := by
                              rw [factWith context.proposed proposed]
                              have result := backwardEntails context.program
                                [{ node := output, fact := outputFact }]
                                input output instruction found operation arguments
                                (by simp [outputExact])
                              simpa only [sameInput] using result }
                      else none
                  | _ => none
                else none
            | none => none
          else none
      | _ => none
    else none

private def leftSchema : PackedFactSchema semantics where
  rule := leftKey
  schema := 0
  Certificate := Unit
  decode := fun body => if body.isEmpty then some () else none
  replay := fun _ _ context _ =>
    if proposed : context.proposed.fact = distanceRange then
      match context.assumptions with
      | [{ node := input, fact := inputFact }, { node := guard, fact := guardFact }] =>
          if inputExact : inputFact = leftRange then
            if guardExact : guardFact = guardRange then
              match found : context.program.node? context.proposed.node with
              | some instruction =>
                  if operation : instruction.op = ({ index := 3 } : OpId) then
                    match arguments : instruction.args with
                    | [actualInput, actualGuard] =>
                        if sameInput : actualInput = input then
                          if sameGuard : actualGuard = guard then
                            some
                              { proof := by
                                  rw [factWith context.proposed proposed]
                                  exact leftEntails context.program
                                    [{ node := input, fact := inputFact },
                                      { node := guard, fact := guardFact }]
                                    context.proposed.node input guard instruction found
                                    operation (by simpa [sameInput, sameGuard] using arguments)
                                    (by simp [inputExact, guardExact]) }
                          else none
                        else none
                    | _ => none
                  else none
              | none => none
            else none
          else none
      | _ => none
    else none

private def rejectSchema : PackedFactSchema semantics where
  rule := rejectKey
  schema := 0
  Certificate := Unit
  decode := fun body => if body.isEmpty then some () else none
  replay := fun _ _ context _ =>
    if proposed : context.proposed.fact = DyadicInterval.Fact.empty then
      match context.assumptions with
      | [{ node := input, fact := inputFact }, { node := guard, fact := guardFact }] =>
          if inputExact : inputFact = rightRange then
            if guardExact : guardFact = guardRange then
              match outputFound : context.program.node? context.proposed.node with
              | some outputInstruction =>
                  if outputOperation : outputInstruction.op = ({ index := 3 } : OpId) then
                    match outputArguments : outputInstruction.args with
                    | [actualInput, actualGuard] =>
                        if sameInput : actualInput = input then
                          if sameGuard : actualGuard = guard then
                            match guardFound : context.program.node? guard with
                            | some guardInstruction =>
                                if guardOperationAt :
                                    guardInstruction.op = ({ index := 2 } : OpId) then
                                  match guardArguments : guardInstruction.args with
                                  | [guardInput] =>
                                      if guardInputExact : guardInput = input then
                                        some
                                          { proof := by
                                              rw [factWith context.proposed proposed]
                                              exact rejectEntails context.program
                                                [{ node := input, fact := inputFact },
                                                  { node := guard, fact := guardFact }]
                                                context.proposed.node input guard
                                                guardInstruction guardFound
                                                guardOperationAt
                                                (by simpa [guardInputExact] using
                                                  guardArguments)
                                                (by simp [inputExact, guardExact]) }
                                      else none
                                  | _ => none
                                else none
                            | none => none
                          else none
                        else none
                    | _ => none
                  else none
              | none => none
            else none
          else none
      | _ => none
    else none

/- The exact cut is closed on the left and strict on the right. -/
private def splitSchema : SplitSchema semantics Dyadic where
  proveCover := fun _ _ parent cut left right =>
    if shape : parent = middleRange ∧ cut = half ∧
        left = leftRange ∧ right = rightRange then
      some
        { proof := by
            rcases shape with ⟨rfl, rfl, rfl, rfl⟩
            intro valuation _ parentHolds
            change NodeId → ℝ at valuation
            change middleRange.Contains (valuation _) at parentHolds
            change leftRange.Contains (valuation _) ∨
              rightRange.Contains (valuation _)
            simp only [middleRange, leftRange, rightRange,
              DyadicInterval.Fact.Contains, rawContains, lowerContains,
              upperContains, toReal_quarter, toReal_half,
              toReal_threeQuarters] at parentHolds ⊢
            rcases le_or_gt (valuation _) (1 / 2 : ℝ) with left | right
            · exact Or.inl ⟨parentHolds.1, left⟩
            · exact Or.inr ⟨right, parentHolds.2⟩ }
    else none

private def emptyRefute : RefuteSchema semantics where
  proveFalse := fun _ _ fact =>
    if shape : fact = DyadicInterval.Fact.empty then
      some
        { proof := by
            subst fact
            intro _ _ impossible
            exact impossible }
    else none

private def proofPackage : ProofRegistry.Package semantics Name :=
  { semantic := { factSchemas := #[backwardSchema, leftSchema, rejectSchema] }
    emit :=
      { schemas :=
          [{ key := backwardSchema.key, handle := ``backwardSchema },
            { key := leftSchema.key, handle := ``leftSchema },
            { key := rejectSchema.key, handle := ``rejectSchema }] }
    refute :=
      [{ accepts := fun fact => fact == DyadicInterval.Fact.empty
         handle := ``emptyRefute }] }

private def proofPackages : Array (ProofRegistry.Package semantics Name) :=
  #[proofPackage]

private def limits : Hex.Interval.State.Limits :=
  { maxOperations := 8
    maxNodes := 8
    maxRules := 8
    maxRegistryEntries := 16
    maxReplayFormats := 8
    maxArity := 2
    maxApplications := 16
    maxQueueEntries := 64
    maxActions := 32
    maxAcceptedFacts := 16
    maxRetainedSuggestions := 8
    maxEffort := 0
    maxObservationValue := 64
    maxDiagnosticValue := 300
    maxOutcomeCandidates := 2
    maxOutcomeSuggestions := 2
    maxProposalItems := 4
    maxInstances := 0
    maxGeneration := 0
    maxNodeDepth := 4
    maxEqualities := 0
    splitEndpointLimit := endpointLimit }

private def arenaLimits : PayloadArena.Limits :=
  { maxEntries := PayloadSession.requiredUses limits
    maxBodyCells := 0
    maxDrafts := PayloadSession.requiredUses limits
    maxDraftCells := 0
    maxAtom := 0
    maxSchema := 0
    maxUses := PayloadSession.requiredUses limits }

private def sessionLimits : PolicySession.Limits :=
  { engine := limits
    arena := arenaLimits
    policy := { maxDecisions := 8, maxTraversal := 128, maxLiveOffers := 32 } }

private def target : NodeFact DyadicInterval.Fact :=
  { node := node 3, fact := distanceRange }

private def input : CheckerInput DyadicInterval.Fact :=
  { baseProgram := program
    initialFacts := #[.whole, highRange, guardRange, .whole]
    target }

private def baseFacts : List (NodeFact DyadicInterval.Fact) :=
  [{ node := node 0, fact := .whole },
    { node := node 1, fact := highRange },
    { node := node 2, fact := guardRange },
    { node := node 3, fact := .whole }]

private inductive Route where
  | contract | split | left | right
  deriving DecidableEq, Repr

private def offerFor (key : RuleKey)
    (view : Propagator.Policy.View DyadicInterval.Fact) :
    Option Propagator.Policy.OfferView :=
  view.offers.toList.find? fun offer =>
    match offer.key with
    | .invoke invocation => invocation.rule == key
    | .split _ _ _ _ => key == splitKey
    | _ => false

private def controller : TargetRun.Controller DyadicInterval.Fact Route :=
  { update := fun state event =>
      match state, event with
      | .contract, .rule _ => .split
      | state, _ => state
    choose := fun state view =>
      let selected :=
        match state with
        | .contract => offerFor backwardKey view
        | .split => offerFor splitKey view
        | .left => offerFor leftKey view
        | .right => offerFor rejectKey view
      match selected with
      | some offer => .select offer state
      | none => .stop state }

private def splitter : BranchStart.Splitter DyadicInterval.Fact :=
  { split := fun graph splitNode instruction parent point =>
      if graph.node? splitNode == some instruction && splitNode == node 0 &&
          parent == middleRange && point == half then
        match DyadicInterval.split endpointLimit parent point with
        | .ok children => some children
        | .error _ => none
      else none }

private def treeLimits : BranchTree.Limits :=
  { branch := { maxDepth := 1, maxScopes := 3 }
    maxSteps := 3, maxSplits := 1, maxLeaves := 2
    leafFuel := sessionLimits.policy.maxDecisions }

private def config : BranchTree.Config DyadicInterval.Fact Route :=
  { factDomain := DyadicInterval.factDomain endpointLimit
    packages := runtimePackages
    sessionLimits
    controller
    splitter
    forkPolicy := fun _ side => match side with | .left => .left | .right => .right
    order := .depthFirst
    limits := treeLimits }

private def tree? : Option (BranchTree.State DyadicInterval.Fact Route) := do
  let .ok state := BranchTree.start config { index := 0 } input .contract | none
  let .ok state := BranchTree.run config state | none
  some state

private def leftInput : CheckerInput DyadicInterval.Fact :=
  { input with initialFacts := #[leftRange, highRange, guardRange, .whole] }
private def rightInput : CheckerInput DyadicInterval.Fact :=
  { input with initialFacts := #[rightRange, highRange, guardRange, .whole] }

#guard
  tree?.any fun tree =>
    tree.settled && tree.nodes.size == 3 && tree.steps == 3 &&
      match tree.nodes[0]?, tree.nodes[1]?, tree.nodes[2]? with
      | some (BranchTree.Node.split source run children _ _),
          some (BranchTree.Node.leaf left (.result leftRun)),
          some (BranchTree.Node.leaf right (.result rightRun)) =>
          !BranchProof.sameInput source.input children.parent &&
            BranchProof.sameParent source run children.parent &&
            children.parent.initialFacts ==
              #[middleRange, highRange, guardRange, .whole] &&
            BranchProof.sameInput children.left leftInput &&
            BranchProof.sameInput children.right rightInput &&
            left.input.initialFacts == leftInput.initialFacts &&
            right.input.initialFacts == rightInput.initialFacts &&
            (match leftRun.stop with | .target _ => true | _ => false) &&
            (match rightRun.stop with | .contradiction => true | _ => false)
      | _, _, _ => false

private meta def factExpr (fact : DyadicInterval.Fact) : MetaM Expr :=
  if fact == DyadicInterval.Fact.whole then
    pure (mkConst ``DyadicInterval.Fact.whole)
  else if fact == DyadicInterval.Fact.empty then
    pure (mkConst ``DyadicInterval.Fact.empty)
  else if fact == highRange then pure (mkConst ``highRange)
  else if fact == middleRange then pure (mkConst ``middleRange)
  else if fact == leftRange then pure (mkConst ``leftRange)
  else if fact == rightRange then pure (mkConst ``rightRange)
  else if fact == guardRange then pure (mkConst ``guardRange)
  else if fact == distanceRange then pure (mkConst ``distanceRange)
  else throwError "exact branch encoder: unknown interval fact"

private def encoder : FrontendEncoder.Encoder DyadicInterval.Fact :=
  FrontendEncoder.make (mkConst ``DyadicInterval.Fact) factExpr

private theorem baseWithin : FactsWithin program baseFacts := by
  intro fact member
  simp only [baseFacts, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl <;> simp [program, node]

private theorem basePrefix : ProgramPrefix program program :=
  ProgramPrefix.refl program
private theorem sameOperations : program.operations = program.operations := rfl
private def initialExtension : Evidence (semantics.Extends program program) :=
  extendRefl semantics program

private def seedAssumed (graph : Program)
    (base : List (NodeFact DyadicInterval.Fact)) (index : Nat)
    (fact : NodeFact DyadicInterval.Fact) (found : base[index]? = some fact) :
    Evidence (semantics.Entails graph base fact) :=
  ProofEmitter.assumedAt graph base index fact found

private def context (inputTerm factsTerm within : Expr)
    (facts : List (NodeFact DyadicInterval.Fact)) :
    ProofFrontend.Context DyadicInterval.Fact Name :=
  { encoder
    resolveSchema := pure
    semantics := mkConst ``semantics
    domain := mkConst ``domain
    laws := mkConst ``laws
    stableLaw := mkConst ``stableLaw
    input := inputTerm
    assumed := ``seedAssumed
    baseFacts := facts
    baseFactsTerm := factsTerm
    baseProgram := program
    baseProgramTerm := mkConst ``program
    basePrefix := mkConst ``basePrefix
    baseWithin := within
    initialExtension := mkConst ``initialExtension
    finalPrefix := mkConst ``basePrefix
    sameOperations := mkConst ``sameOperations
    top := fun _ => DyadicInterval.Fact.whole }

private def rootContext : ProofFrontend.Context DyadicInterval.Fact Name :=
  context (mkConst ``input) (mkConst ``baseFacts) (mkConst ``baseWithin) baseFacts

private def branchFact (side : DyadicInterval.Fact) : NodeFact DyadicInterval.Fact :=
  { node := node 0, fact := side }
private def branchFacts (side : DyadicInterval.Fact) :
    List (NodeFact DyadicInterval.Fact) :=
  branchFact side :: baseFacts
private def leftFacts := branchFacts leftRange
private def rightFacts := branchFacts rightRange

private theorem branchWithin (side : DyadicInterval.Fact) :
    FactsWithin program (branchFacts side) := by
  intro fact member
  simp only [branchFacts, branchFact, baseFacts, List.mem_cons,
    List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl <;> simp [program, node]

private def inherit (child : CheckerInput DyadicInterval.Fact)
    (childFacts : child.initialFacts = #[leftRange, highRange, guardRange, .whole] ∨
      child.initialFacts = #[rightRange, highRange, guardRange, .whole])
    (observed : NodeId)
    (different : observed ≠ node 0) (fact : DyadicInterval.Fact)
    (found : child.initialFacts[observed.index]? = some fact) :
    Evidence (semantics.Entails program baseFacts { node := observed, fact }) := by
  apply ProofEmitter.assumed
  rcases childFacts with childFacts | childFacts <;> rw [childFacts] at found
  all_goals
    cases observed with
    | mk index =>
        cases index with
        | zero => simp [node] at different
        | succ index =>
            cases index with
            | zero => simp_all [baseFacts, node]
            | succ index =>
                cases index with
                | zero => simp_all [baseFacts, node]
                | succ index =>
                    cases index with
                    | zero => simp_all [baseFacts, node]
                    | succ index => simp_all

private def leftSeed :
    ProofEmitter.BranchSeed semantics leftInput baseFacts (branchFact leftRange) :=
  ProofEmitter.BranchSeed.make leftInput (branchFact leftRange)
    (by rfl) (by rfl) (inherit leftInput (Or.inl rfl))

private def rightSeed :
    ProofEmitter.BranchSeed semantics rightInput baseFacts (branchFact rightRange) :=
  ProofEmitter.BranchSeed.make rightInput (branchFact rightRange)
    (by rfl) (by rfl) (inherit rightInput (Or.inr rfl))

private def leftContext : ProofFrontend.Context DyadicInterval.Fact Name :=
  context (mkConst ``leftInput) (mkConst ``leftFacts)
    (mkApp (mkConst ``branchWithin) (mkConst ``leftRange)) leftFacts
private def rightContext : ProofFrontend.Context DyadicInterval.Fact Name :=
  context (mkConst ``rightInput) (mkConst ``rightFacts)
    (mkApp (mkConst ``branchWithin) (mkConst ``rightRange)) rightFacts

private meta def emitLeaf (source : BranchTree.Leaf DyadicInterval.Fact Route)
    (run : TargetRun.Result DyadicInterval.Fact Route) : MetaM Expr := do
  let .ok registry := ProofRegistry.build run.session.registry proofPackages
    | throwError "exact branch: proof registry failed"
  let some trace := Frontend.trace? run.session.state.engine run.session.arena
    | throwError "exact branch: child trace quotation failed"
  if source.input.initialFacts == leftInput.initialFacts then
    let .target reached := run.stop
      | throwError "exact branch: left child did not reach its target"
    let state ← ProofFrontend.emitBranch leftContext source.input
      (mkConst ``leftSeed) trace.program trace.events registry.emit
    ProofFrontend.closeTarget leftContext state reached.seen reached.fact source.input.target
  else if source.input.initialFacts == rightInput.initialFacts then
    let .contradiction := run.stop
      | throwError "exact branch: right child did not contradict"
    let state ← ProofFrontend.emitBranch rightContext source.input
      (mkConst ``rightSeed) trace.program trace.events registry.emit
    ProofFrontend.refuteCurrent rightContext state registry.refute
      run.session.state.engine.facts run.session.state.engine.versions source.input.target
  else
    throwError "exact branch: leaf has unknown exact input"

private meta def emitSplit (_source : BranchTree.Leaf DyadicInterval.Fact Route)
    (run : TargetRun.Result DyadicInterval.Fact Route)
    (children : BranchStart.Children DyadicInterval.Fact)
    (left right : Expr) : MetaM Expr := do
  let .split plan := run.stop
    | throwError "exact branch: internal node did not stop at a split"
  unless plan.node == node 0 && plan.fact == middleRange && plan.point == half &&
      children.parent.initialFacts == #[middleRange, highRange, guardRange, .whole] &&
      BranchProof.sameInput children.left leftInput &&
      BranchProof.sameInput children.right rightInput do
    throwError "exact branch: retained contraction or exact children changed"
  let .ok registry := ProofRegistry.build run.session.registry proofPackages
    | throwError "exact branch: root proof registry failed"
  let some trace := Frontend.trace? run.session.state.engine run.session.arena
    | throwError "exact branch: root trace quotation failed"
  let state ← ProofFrontend.emitTrace rootContext trace.program trace.events registry.emit
  let some parent := ProofFrontend.findProof? state.known
      { node := node 0, version := 1 } middleRange
    | throwError "exact branch: live contraction proof is missing"
  let result ← mkAppM ``ProofEmitter.replaySplit
    #[mkConst ``splitSchema, mkConst ``program, mkConst ``baseFacts,
      ← encoder.nodeId (node 0), mkConst ``middleRange, mkConst ``half,
      mkConst ``leftRange, mkConst ``rightRange, ← encoder.nodeFact target,
      parent, left, right]
  ProofFrontend.replayResult result

private def emitter : BranchProof.Emitter DyadicInterval.Fact Route :=
  { leaf := emitLeaf, split := emitSplit }
private def proofLimits : BranchProof.Limits :=
  { maxNodes := 3, maxDepth := 1 }

private def joined : Evidence (semantics.Entails program baseFacts target) := by
  run_tac
    let some tree := tree? | throwError "exact branch: runtime tree failed"
    let goal ← getMainGoal
    goal.assign (← BranchProof.emit proofLimits emitter tree (← goal.getType))

set_option linter.unusedTactic false in
example : True := by
  run_tac
    let some tree := tree? | throwError "exact branch mutation: runtime tree failed"
    let check (id : Nat) (side wrong : DyadicInterval.Fact)
        (context : ProofFrontend.Context DyadicInterval.Fact Name)
        (seed : Expr) : MetaM Unit := do
      let some (BranchTree.Node.leaf source (.result run)) := tree.nodes[id]?
        | throwError "exact branch mutation: child is missing"
      let .ok registry := ProofRegistry.build run.session.registry proofPackages
        | throwError "exact branch mutation: proof registry failed"
      let some trace := Frontend.trace? run.session.state.engine run.session.arena
        | throwError "exact branch mutation: trace is missing"
      let [.rule step] := trace.events
        | throwError "exact branch mutation: wrong trace shape"
      unless step.assumptions ==
          [branchFact side, { node := node 2, fact := guardRange }] do
        throwError "exact branch mutation: live rule did not consume its side"
      let mutated : RuleStep DyadicInterval.Fact :=
        { step with assumptions :=
            [branchFact wrong, { node := node 2, fact := guardRange }] }
      if (← observing? <| ProofFrontend.emitBranch context source.input seed
          trace.program [.rule mutated] registry.emit).isSome then
        throwError "exact branch mutation: sibling assumption was accepted"
    check 1 leftRange rightRange leftContext (mkConst ``leftSeed)
    check 2 rightRange leftRange rightContext (mkConst ``rightSeed)
  trivial

private noncomputable def valuation (x : ℝ) : NodeId → ℝ
  | ⟨0⟩ => x
  | ⟨1⟩ => (1 / 4 : ℝ) - (x - (1 / 2 : ℝ)) ^ 2
  | ⟨2⟩ => x
  | ⟨3⟩ => |x - (1 / 2 : ℝ)|
  | _ => 0

private theorem valuationModels (x : ℝ) : semantics.models program (valuation x) := by
  refine ⟨?_, ?_⟩
  · simp [program, operations, models, sourceModel, centeredModel, guardModel,
      distanceModel, sourceOperation, centeredOperation, guardOperation,
      distanceOperation]
  · rintro ⟨index⟩ instruction found
    cases index with
    | zero =>
        simp [Program.node?, program, sourceInstruction] at found
        subst instruction
        exact ⟨sourceModel, by simp [models], by rfl⟩
    | succ index =>
        cases index with
        | zero =>
            simp [Program.node?, program, centeredInstruction] at found
            subst instruction
            exact ⟨centeredModel, by simp [models],
              by simp [centeredModel, valuation, node]⟩
        | succ index =>
            cases index with
            | zero =>
                simp [Program.node?, program, guardInstruction] at found
                subst instruction
                exact ⟨guardModel, by simp [models],
                  by simp [guardModel, valuation, node]⟩
            | succ index =>
                cases index with
                | zero =>
                    simp [Program.node?, program, distanceInstruction] at found
                    subst instruction
                    exact ⟨distanceModel, by simp [models],
                      by simp [distanceModel, valuation, node]⟩
                | succ index => simp [Program.node?, program] at found

/-- The branch theorem emitted from the live retained tree. Both exact child
assumptions are load-bearing: the left rule accepts only `[1/4,1/2]`, while
the right rejection accepts only `(1/2,3/4]`. -/
theorem tacticExactBranch (x : ℝ)
    (lower : 3 / 16 ≤ (1 / 4 : ℝ) - (x - (1 / 2 : ℝ)) ^ 2)
    (upper : (1 / 4 : ℝ) - (x - (1 / 2 : ℝ)) ^ 2 ≤ 1 / 4)
    (guard : x ≤ 1 / 2) :
    0 ≤ |x - (1 / 2 : ℝ)| ∧ |x - (1 / 2 : ℝ)| ≤ 1 / 4 := by
  have result := joined.proof (valuation x) (valuationModels x) (by
    intro fact member
    simp only [baseFacts, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl
    · change DyadicInterval.Fact.whole.Contains (valuation x (node 0))
      simp [DyadicInterval.Fact.Contains, DyadicInterval.Fact.whole,
        rawContains, lowerContains, upperContains]
    · change highRange.Contains (valuation x (node 1))
      simpa only [highRange, DyadicInterval.Fact.Contains, rawContains,
        lowerContains, upperContains, toReal_threeSixteenths, toReal_quarter,
        valuation, node, and_true] using And.intro lower upper
    · change guardRange.Contains (valuation x (node 2))
      simpa only [guardRange, DyadicInterval.Fact.Contains, rawContains,
        lowerContains, upperContains, toReal_half, valuation, node, true_and]
        using guard
    · change DyadicInterval.Fact.whole.Contains (valuation x (node 3))
      simp [DyadicInterval.Fact.Contains, DyadicInterval.Fact.whole,
        rawContains, lowerContains, upperContains])
  change distanceRange.Contains (valuation x (node 3)) at result
  simpa only [distanceRange, DyadicInterval.Fact.Contains, rawContains,
    lowerContains, upperContains, DyadicInterval.toReal_zero, toReal_quarter,
    valuation, node, and_true] using result

-- The theorem's three hypotheses are jointly inhabited; the right-child
-- contradiction closes only one branch and does not make the root statement
-- vacuous.
private theorem premiseWitness :
    3 / 16 ≤ (1 / 4 : ℝ) - ((1 / 2 : ℝ) - 1 / 2) ^ 2 ∧
      (1 / 4 : ℝ) - ((1 / 2 : ℝ) - 1 / 2) ^ 2 ≤ 1 / 4 ∧
      (1 / 2 : ℝ) ≤ 1 / 2 := by
  norm_num

example :
    0 ≤ |(1 / 2 : ℝ) - 1 / 2| ∧ |(1 / 2 : ℝ) - 1 / 2| ≤ 1 / 4 := by
  exact tacticExactBranch (1 / 2) premiseWitness.1 premiseWitness.2.1
    premiseWitness.2.2

/--
info: 'Hex.IntervalMathlib.ExactBranchConformance.tacticExactBranch' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms tacticExactBranch

end Hex.IntervalMathlib.ExactBranchConformance
