/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import HexIntervalMathlib.Runtime
import HexIntervalMathlib.Experiment.SineSign

/-!
# Typed runtime-to-proof conformance

This canary runs the real `sin (-x)` vertical through the supported sealed
runtime adapter.  Each root/child chronology is instance, equality, direct
fact, and engine-owned transport.  The split children restart their runtime
serial, equality arena, and executable extension from the same base assembly.
-/

namespace Hex.IntervalMathlib.RuntimeProofConformance

open Hex.Interval
open Hex.Interval.Executable
open Hex.Interval.Runtime
open Hex.Interval.RuntimeProof
open Hex.Interval.Experiment.SineSign

def scope : Policy.ScopeId := { index := 0 }

def instanceRule : Registration :=
  { key := oddnessRuleKey, head := sineKey, kind := .instantiate,
    watches := [], writes := [] }

def equalityKey : RuleKey := { name := "sine-sign.runtime.equality" }
def transportKey : RuleKey := { name := "sine-sign.runtime.transport" }
def factKey : RuleKey := { name := "sine-sign.runtime.fact" }
def splitKey : RuleKey := { name := "sine-sign.runtime.split" }

def equalityRule : Registration :=
  { key := equalityKey, head := sineKey, kind := .rewrite,
    watches := [], writes := [], binding := .scoped }

def transportRule : Registration :=
  { key := transportKey, head := sineKey, kind := .rewrite,
    watches := [], writes := [], binding := .scoped }

def factRule : Registration :=
  { key := factKey, head := negationKey, kind := .forward,
    watches := [], writes := [], binding := .scoped }

def splitRule : Registration :=
  { key := splitKey, head := negationKey, kind := .split,
    watches := [], writes := [], binding := .scoped }

def registrations : Array Registration :=
  #[instanceRule, equalityRule, transportRule, factRule, splitRule]

def equalityBinding : ScopeBinding :=
  { rule := equalityKey, anchor := node 2, watches := [], writes := [] }

def transportBinding : ScopeBinding :=
  { rule := transportKey, anchor := node 2,
    watches := [node 4], writes := [node 2] }

def factBinding : ScopeBinding :=
  { rule := factKey, anchor := node 4,
    watches := [node 0], writes := [node 4] }

def bindings : Array ScopeBinding :=
  #[equalityBinding, transportBinding, factBinding]

def instanceQuote : Quote := { role := .instance, schema := 1, body := [1] }
def equalityQuote : Quote := { role := .equality, schema := 1, body := [1] }
def factQuote : Quote :=
  { role := .fact, schema := 1, body := [Range.nonpositive.code] }

def instanceBatch (request : RuleRequest Range) : Runtime.Batch Range Nat :=
  { events := #[.instance
      { action := request.action, after := extendedProgram,
        freshFacts := #[.all, .all], bindings,
        newNodes := [node 3, node 4],
        newBindings := [equalityBinding, transportBinding, factBinding],
        newApplications := [{ index := 1 }, { index := 2 }, { index := 3 }, { index := 4 }],
        generation := 1, quote := instanceQuote }] }

def equalityBatch (request : RuleRequest Range) : Runtime.Batch Range Nat :=
  { events := #[.equality
      { action := request.action, equality := { index := 0 },
        left := node 2, right := node 4, generation := 1,
        assumptions := [], quote := equalityQuote }] }

def factBatch (request : RuleRequest Range) : Runtime.Batch Range Nat :=
  { events := #[.fact
      { action := request.action,
        update :=
          { programVersion := 1
            node := node 4
            previous := { node := node 4, version := 0 }
            fact := .nonpositive
            version := 1
            cause := 40 },
        proposed := .nonpositive, quote := factQuote }] }

def transportBatch (request : RuleRequest Range) : Runtime.Batch Range Nat :=
  { events := #[.transport
      { action := request.action,
        update :=
          { programVersion := 1
            node := node 2
            previous := { node := node 2, version := 0 }
            fact := .nonpositive
            version := 1
            cause := 41 },
        equality := { index := 0 }, source := { node := node 4, version := 1 } }] }

def exactFormat (role : Executable.Role) (body : List Nat) : ReplayFormat :=
  { role, schema := 1, validateBody := fun actual => actual == body }

def handler (registration : Registration) (formats : Array ReplayFormat)
    (accepts : Program → ScopeBinding → Bool)
    (run : RuleRequest Range → Runtime.Batch Range Nat) :
    Handler Range (Runtime.Batch Range Nat) Unit :=
  { registration, formats, acceptsScope := accepts,
    invoke := fun cache request =>
      let result := run request
      ({ result, quotes := result.events.toList.filterMap (fun
          | .fact step => some step.quote
          | .equality step => some step.quote
          | .instance step => some step.quote
          | .transport _ => none) |>.toArray }, cache) }

def accepts (program : Program) (binding : ScopeBinding) : Bool :=
  program == extendedProgram &&
    (binding == equalityBinding || binding == transportBinding || binding == factBinding)

def inertBatch (_ : RuleRequest Range) : Runtime.Batch Range Nat :=
  { events := #[] }

def instanceHandler : Handler Range (Runtime.Batch Range Nat) Unit :=
  handler instanceRule #[exactFormat .instance [1]] (fun _ _ => false) instanceBatch

def equalityHandler : Handler Range (Runtime.Batch Range Nat) Unit :=
  handler equalityRule #[exactFormat .equality [1]] accepts equalityBatch

def transportHandler : Handler Range (Runtime.Batch Range Nat) Unit :=
  handler transportRule #[] accepts transportBatch

def factHandler : Handler Range (Runtime.Batch Range Nat) Unit :=
  handler factRule #[exactFormat .fact [Range.nonpositive.code]] accepts factBatch

def splitHandler : Handler Range (Runtime.Batch Range Nat) Unit :=
  handler splitRule #[] (fun _ _ => false) inertBatch

def runtimePackage : Package Range (Runtime.Batch Range Nat) :=
  { Cache := Unit, cache := (), operations := operations,
    handlers :=
      #[instanceHandler, equalityHandler, transportHandler, factHandler, splitHandler],
    measure :=
      { metadata := { bytes := 10, work := 10 },
        application := fun _ => { bytes := 1, work := 1 },
        cache := fun _ => {},
        result := fun batch => { bytes := batch.events.size, work := batch.events.size } } }

def stateLimits : State.Limits :=
  { maxOperations := 3, maxNodes := 5, maxRules := 5,
    maxRegistryEntries := 32, maxReplayFormats := 3, maxArity := 1,
    maxScopeNodes := 1, maxApplications := 5, maxQueueEntries := 8,
    maxActions := 4, maxMatcherVisits := 0, matcherBatchSize := 0,
    maxAcceptedFacts := 2, maxRetainedSuggestions := 0, maxEffort := 0,
    maxObservationValue := 8, maxDiagnosticValue := 8,
    maxOutcomeCandidates := 1, maxOutcomeSuggestions := 0, maxProposalItems := 1,
    maxInstances := 1, maxGeneration := 1, maxNodeDepth := 2, maxEqualities := 1,
    splitEndpointLimit := { maxEndpointHeight := 8, maxAlignmentShift := 8 } }

def executableLimits : Executable.Limits :=
  { state := stateLimits, maxPackages := 1,
    maxMetadataBytes := 64, maxMetadataWork := 64,
    maxCacheBytes := 0, maxCacheWork := 0,
    maxResultBytes := 1, maxResultWork := 1,
    maxQuotes := 1, maxQuoteCells := 1, maxAtom := 3, maxSchema := 1 }

def runtimeLimits : Runtime.Limits :=
  { executable := executableLimits, maxEvents := 1 }

def assembly? : Option (RuntimeProof.Assembly Range Nat) :=
  (Executable.buildWithin executableLimits #[runtimePackage] baseProgram).toOption

def branchWith? (facts : Array Range) : Option (State.Branch Range Nat) :=
  (State.Branch.startWithin stateLimits baseProgram facts).toOption

def branch? : Option (State.Branch Range Nat) :=
  branchWith? #[.unit, .all, .all]

def action (serial programVersion application rule : Nat) (key : RuleKey)
    (anchor : NodeId) (kind : ActionKind) (generation : Nat)
    (inputs : List SeenVersion) (writes : List NodeId := []) : Action :=
  { serial, programVersion, application := { index := application },
    rule := { index := rule }, key, node := anchor, kind, effort := 0,
    generation, inputs, writes }

def instanceAction : Action :=
  action 0 0 0 0 oddnessRuleKey (node 2) .instantiate 0 []

def equalityAction : Action :=
  action 1 1 1 1 equalityKey (node 2) .rewrite 1 []

def factAction : Action :=
  action 2 1 3 3 factKey (node 4) .forward 1
    [{ node := node 0, version := 0 }] [node 4]

def transportAction : Action :=
  action 3 1 2 2 transportKey (node 2) .rewrite 1
    [{ node := node 4, version := 1 }] [node 2]

/-! ## Theorem registry -/

def semantics : Proof.Semantics Range :=
  { Value := ℝ, models := Models,
    holds := fun _ valuation fact => Contains fact.fact (valuation fact.node),
    holdsAgree := by
      intro _ left right fact within _ _ agree
      rw [agree fact.node within] }

def domain : Proof.Domain semantics :=
  { top := fun _ => .all,
    topSound := by simp [semantics, Contains],
    meet := fun program target previous proposed installed =>
      if exact : installed = previous.meet proposed then
        some
          { proof := by
              subst installed
              intro valuation _
              exact containsMeet previous proposed (valuation target) }
      else none }

theorem laws : Proof.Laws semantics :=
  { holdsEq := by
      intro _ valuation left right fact _ equal
      change Contains fact (valuation left) ↔ Contains fact (valuation right)
      rw [equal] }

theorem factProof : semantics.Entails extendedProgram
    [{ node := node 0, fact := .unit }] { node := node 4, fact := .nonpositive } := by
  change ∀ valuation : NodeId → ℝ, Models extendedProgram valuation →
    (∀ assumption, assumption ∈
      ([{ node := node 0, fact := Range.unit }] : List (Proof.NodeFact Range)) →
      Contains assumption.fact (valuation assumption.node)) →
    Contains .nonpositive (valuation (node 4))
  intro valuation model assumptions
  have inputRange := assumptions { node := node 0, fact := .unit } (by simp)
  have sineNonnegative : 0 ≤ valuation (node 3) := by
    rw [model.2.2.1 (by rfl)]
    exact Real.sin_nonneg_of_nonneg_of_le_pi inputRange.1
      (inputRange.2.trans (by linarith [Real.one_le_pi_div_two]))
  change valuation (node 4) ≤ 0
  rw [model.2.2.2 (by rfl)]
  exact neg_nonpos.mpr sineNonnegative

theorem equalityProof : semantics.EntailsEq extendedProgram [] (node 2) (node 4) := by
  change ∀ valuation : NodeId → ℝ, Models extendedProgram valuation →
    (∀ assumption, assumption ∈ ([] : List (Proof.NodeFact Range)) →
      Contains assumption.fact (valuation assumption.node)) →
    valuation (node 2) = valuation (node 4)
  intro valuation model _
  have negated := model.1 (by rfl)
  have original := model.2.1 (by rfl)
  have positive := model.2.2.1 (by rfl)
  have negative := model.2.2.2 (by rfl)
  calc
    valuation (node 2) = Real.sin (valuation (node 1)) := original
    _ = Real.sin (-valuation (node 0)) := congrArg Real.sin negated
    _ = -Real.sin (valuation (node 0)) := Real.sin_neg _
    _ = -valuation (node 3) := congrArg Neg.neg positive.symm
    _ = valuation (node 4) := negative.symm

theorem stable : Proof.Stable semantics baseProgram extendedProgram :=
  { appendOnly :=
      { operationSize := programPrefix.operationSize,
        nodeSize := programPrefix.nodeSize,
        operationAt := programPrefix.operationAt,
        nodeAt := programPrefix.nodeAt },
    modelsBefore := by
      intro valuation model
      change Models extendedProgram valuation at model
      change Models baseProgram valuation
      refine ⟨?_, ?_, ?_, ?_⟩
      · intro _; exact model.1 (by rfl)
      · intro _; exact model.2.1 (by rfl)
      · intro impossible
        simp [baseProgram, Program.node?, node] at impossible
      · intro impossible
        simp [baseProgram, Program.node?, node] at impossible
    holdsOld := by
      intro oldValue newValue fact within _ _ agreement
      change Contains fact.fact (oldValue fact.node) ↔ Contains fact.fact (newValue fact.node)
      rw [agreement fact.node within] }

def extension : Proof.Evidence (semantics.Extends baseProgram extendedProgram) :=
  { proof := by
      change ∀ valuation : NodeId → ℝ, Models baseProgram valuation →
        ∃ extended : NodeId → ℝ, Models extendedProgram extended ∧
          ∀ observed, observed.index < baseProgram.nodes.size →
            valuation observed = extended observed
      intro valuation model
      refine ⟨extendValuation valuation, ?_, ?_⟩
      · refine ⟨?_, ?_, ?_, ?_⟩
        · intro _
          have old := model.1 (by rfl)
          simpa [extendValuation, node] using old
        · intro _
          have old := model.2.1 (by rfl)
          simpa [extendValuation, node] using old
        · intro _; simp [extendValuation, node]
        · intro _; simp [extendValuation, node]
      · intro observed within
        have old : observed.index < 3 := by simpa [baseProgram] using within
        have notThree : observed ≠ node 3 := by
          intro equal; subst observed; simp [node] at old
        have notFour : observed ≠ node 4 := by
          intro equal; subst observed; simp [node] at old
        simp [extendValuation, notThree, notFour] }

def instanceProofKey : Proof.Key :=
  { rule := oddnessRuleKey, role := .instance, bodySchema := 1 }
def equalityProofKey : Proof.Key :=
  { rule := equalityKey, role := .equality, bodySchema := 1 }
def factProofKey : Proof.Key :=
  { rule := factKey, role := .fact, bodySchema := 1 }
def splitProofKey : Proof.Key :=
  { rule := splitKey, role := .split, bodySchema := 1 }

def decode (body : List Nat) : Option Unit :=
  if body == [1] then some () else none

def instanceSchema : Proof.InstanceSchema semantics :=
  { key := instanceProofKey, Certificate := Unit, decode,
    prove := fun context _ =>
      if shape : context.before = baseProgram ∧ context.after = extendedProgram ∧
          context.beforeVersion = 0 ∧ context.afterVersion = 1 ∧
          context.newNodes = [node 3, node 4] then
        some
          { stable := by simpa [shape.1, shape.2.1] using stable
            extension := by simpa [shape.1, shape.2.1] using extension }
      else none }

def equalitySchema : Proof.EqualitySchema semantics :=
  { key := equalityProofKey, Certificate := Unit, decode,
    prove := fun context _ =>
      if shape : context.program = extendedProgram ∧ context.left = node 2 ∧
          context.right = node 4 ∧ context.assumptions = [] then
        some
          { proof := by
              simpa only [shape.1, shape.2.1, shape.2.2.1, shape.2.2.2] using
                equalityProof }
      else none }

def factSchema : Proof.FactSchema semantics :=
  { key := factProofKey, Certificate := Unit,
    decode := fun body => if body == [Range.nonpositive.code] then some () else none,
    prove := fun context _ =>
      if shape : context.program = extendedProgram ∧
          context.assumptions = [{ node := node 0, fact := .unit }] ∧
          context.proposed = { node := node 4, fact := .nonpositive } then
        some
          { proof := by simpa [shape.1, shape.2.1, shape.2.2] using factProof }
      else none }

def splitSchema : Proof.SplitSchema semantics Nat :=
  { key := splitProofKey, Certificate := Unit, decode,
    prove := fun context _ =>
      if shape : context.program = baseProgram ∧ context.parent.node = node 1 ∧
          context.left = { node := node 1, fact := .nonnegative } ∧
          context.right = { node := node 1, fact := .nonpositive } then
        some
          { proof := by
              rcases shape with ⟨programEq, _, leftEq, rightEq⟩
              intro valuation _ _
              change NodeId → ℝ at valuation
              rcases le_total 0 (valuation (node 1)) with left | right
              · left
                simpa [programEq, leftEq, semantics, Contains] using left
              · right
                simpa [programEq, rightEq, semantics, Contains] using right }
      else none }

def proofPackage : Proof.Package semantics Nat :=
  { registrations, facts := #[factSchema], equalities := #[equalitySchema],
    instances := #[instanceSchema], splits := #[splitSchema] }

def proofLimits : Proof.Limits :=
  { maxPackages := 1, maxSchemas := 4, maxBodyCells := 1,
    maxDependencies := 1, maxChronology := 4 }

def proofRegistry? : Option (Proof.Registry semantics Nat) :=
  (Proof.Registry.buildWithin proofLimits baseProgram #[proofPackage]).toOption

def adapterKey : RuntimeProof.Key := { name := "sine-runtime-proof", version := 1 }

def registry? : Option (RuntimeProof.Registry Range semantics Nat Nat) := do
  let assembly ← assembly?
  let proof ← proofRegistry?
  (RuntimeProof.Registry.buildWithin executableLimits adapterKey assembly proof).toOption

#guard assembly?.isSome
#guard proofRegistry?.isSome
#guard registry?.isSome

/-! ## Root and restarted split-child replay -/

def searchLimits : Search.Limits :=
  { maxSteps := 12, maxSplits := 1, maxLeaves := 2, maxFrontier := 2,
    maxDepth := 1, maxScopes := 3, leafFuel := 12 }

def resultLimits : Search.Result.Limits :=
  { search := searchLimits, runtime := runtimeLimits, maxNodes := 3,
    maxBodyCells := 8, maxBytes := 8192, maxWork := 8192, maxCode := 8 }

def unitCost : Search.Result.Cost := { bytes := 1, work := 1 }

def measure : Search.Result.Measure Range Nat Nat Proof.Key :=
  { node := unitCost,
    branch := fun branch =>
      { bytes := branch.program.nodes.size + branch.history.size,
        work := branch.program.nodes.size + branch.history.size },
    fact := fun _ => unitCost, action := fun _ => unitCost,
    plan := fun _ => unitCost, schema := fun _ => unitCost,
    body := fun _ => unitCost, code := fun _ => unitCost }

def adapterLimits : RuntimeProof.Limits :=
  { result := resultLimits, proof := proofLimits,
    tree := { maxNodes := 3, maxDepth := 1, maxBodyCells := 7, maxWork := 128 },
    maxTransitions := 8, maxEvents := 8, maxStructuralCells := 138 }

def input : Proof.Input Range :=
  { scope, program := baseProgram, facts := #[.unit, .all, .all],
    target := { node := node 2, fact := .nonpositive } }

private def advance (tree : Search.Result.Tree Range Nat Nat Proof.Key)
    (runtime : Runtime.State Range Nat) : List Action →
    Option (Search.Result.Tree Range Nat Nat Proof.Key × Runtime.State Range Nat)
  | [] => some (tree, runtime)
  | next :: rest =>
      match runtime.stepWithin runtimeLimits next with
      | .error _ => none
      | .ok (transition, runtime) =>
          match Search.Result.advanceRuntimeWithin resultLimits measure tree transition with
          | .error _ => none
          | .ok tree => advance tree runtime rest

private def runCurrent (tree : Search.Result.Tree Range Nat Nat Proof.Key)
    (assembly : RuntimeProof.Assembly Range Nat) :
    Option (Search.Result.Tree Range Nat Nat Proof.Key) :=
  match Search.Result.current? tree with
  | none => none
  | some (_, source) =>
      match Runtime.State.startWithin runtimeLimits assembly source.branch with
      | .error _ => none
      | .ok runtime =>
          match advance tree runtime
              [instanceAction, equalityAction, factAction, transportAction] with
          | none => none
          | some (tree, _) =>
              (Search.Result.settleWithin resultLimits measure tree (.target
                { scope := source.scope, programVersion := 1,
                  seen := { node := node 2, version := 1 } })).toOption

def rootTree? : Option (Search.Result.Tree Range Nat Nat Proof.Key) :=
  match branch?, assembly? with
  | some branch, some assembly =>
      match Search.Result.startWithin resultLimits measure scope branch with
      | .error _ => none
      | .ok tree => runCurrent tree assembly
  | _, _ => none

def splitAction : Action :=
  action 0 0 0 4 splitKey (node 1) .split 0
    [{ node := node 1, version := 0 }]

def splitRecipe : Search.Result.Split Nat Proof.Key :=
  { scope, programVersion := 0, action := splitAction,
    parent := { node := node 1, version := 0 }, plan := 1,
    schema := splitProofKey, body := [1] }

def leftSeed : Search.Result.Seed Range :=
  { node := node 1, previous := splitRecipe.parent, fact := .nonnegative }

def rightSeed : Search.Result.Seed Range :=
  { node := node 1, previous := splitRecipe.parent, fact := .nonpositive }

def splitTree? : Option (Search.Result.Tree Range Nat Nat Proof.Key) :=
  match branch?, assembly? with
  | some branch, some assembly =>
      match Search.Result.startWithin resultLimits measure scope branch with
      | .error _ => none
      | .ok root =>
          match Search.Result.splitWithin resultLimits measure .depthFirst root
              splitRecipe leftSeed rightSeed with
          | .error _ => none
          | .ok tree => (runCurrent tree assembly).bind fun tree => runCurrent tree assembly
  | _, _ => none

#guard rootTree?.any fun tree =>
  tree.check resultLimits measure && tree.transitions.size == 4 && tree.pending.isEmpty

#guard splitTree?.any fun tree =>
  tree.check resultLimits measure && tree.transitions.size == 8 && tree.pending.isEmpty

def rootBundle? : Option (RuntimeProof.Bundle Range Nat Nat) :=
  match registry?, rootTree? with
  | some registry, some tree =>
      (RuntimeProof.quoteTreeWithin adapterLimits measure registry tree).toOption
  | _, _ => none

def splitBundle? : Option (RuntimeProof.Bundle Range Nat Nat) :=
  match registry?, splitTree? with
  | some registry, some tree =>
      (RuntimeProof.quoteTreeWithin adapterLimits measure registry tree).toOption
  | _, _ => none

def rootReplay? : Option (Proof.Evidence
    (semantics.Entails input.program (Proof.initialBase input) input.target)) :=
  match registry?, rootBundle? with
  | some registry, some bundle =>
      (RuntimeProof.replayTree adapterLimits measure registry domain laws input bundle).toOption
  | _, _ => none

def splitReplay? : Option (Proof.Evidence
    (semantics.Entails input.program (Proof.initialBase input) input.target)) :=
  match registry?, splitBundle? with
  | some registry, some bundle =>
      (RuntimeProof.replayTree adapterLimits measure registry domain laws input bundle).toOption
  | _, _ => none

#guard rootBundle?.isSome
#guard splitBundle?.isSome
#guard rootReplay?.isSome
#guard splitReplay?.isSome

def fallback : Proof.Evidence
    (semantics.Entails input.program (Proof.initialBase input) input.target) :=
  { proof := by
      change ∀ valuation : NodeId → ℝ, Models baseProgram valuation →
        (∀ assumption, assumption ∈ Proof.initialBase input →
          Contains assumption.fact (valuation assumption.node)) →
        Contains .nonpositive (valuation (node 2))
      intro valuation model assumptions
      have inputRange := assumptions { node := node 0, fact := .unit } (by
        have baseEq : Proof.initialBase input =
            [{ node := node 0, fact := .unit }, { node := node 1, fact := .all },
              { node := node 2, fact := .all }] := by rfl
        rw [baseEq]
        simp)
      change valuation (node 2) ≤ 0
      rw [model.2.1 (by rfl)]
      rw [model.1 (by rfl), Real.sin_neg]
      exact neg_nonpos.mpr (Real.sin_nonneg_of_nonneg_of_le_pi inputRange.1
        (inputRange.2.trans (by linarith [Real.one_le_pi_div_two]))) }

def rootEvidence := rootReplay?.getD fallback
def splitEvidence := splitReplay?.getD fallback

/-- Ordinary theorem obtained from the root typed-runtime chronology. -/
theorem rootSinNeg {x : ℝ} (nonnegative : 0 ≤ x) (atMostOne : x ≤ 1) :
    Real.sin (-x) ≤ 0 := by
  have result := rootEvidence.proof (baseValuation x) (baseModels x) (by
    intro assumption member
    have baseEq : Proof.initialBase input =
        [{ node := node 0, fact := .unit }, { node := node 1, fact := .all },
          { node := node 2, fact := .all }] := by rfl
    rw [baseEq] at member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl
    · exact ⟨nonnegative, atMostOne⟩
    · trivial
    · trivial)
  exact result

/-- The same ordinary theorem obtained after both split children restart and
replay independent instance/equality/fact/transport chronologies. -/
theorem splitSinNeg {x : ℝ} (nonnegative : 0 ≤ x) (atMostOne : x ≤ 1) :
    Real.sin (-x) ≤ 0 := by
  have result := splitEvidence.proof (baseValuation x) (baseModels x) (by
    intro assumption member
    have baseEq : Proof.initialBase input =
        [{ node := node 0, fact := .unit }, { node := node 1, fact := .all },
          { node := node 2, fact := .all }] := by rfl
    rw [baseEq] at member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl
    · exact ⟨nonnegative, atMostOne⟩
    · trivial
    · trivial)
  exact result

/-! ## Exact rejection canaries -/

private def quoteError (limits : RuntimeProof.Limits) : Option RuntimeProof.Error :=
  match registry?, rootTree? with
  | some registry, some tree =>
      match RuntimeProof.quoteTreeWithin limits measure registry tree with
      | .error error => some error
      | .ok _ => none
  | _, _ => none

#guard quoteError { adapterLimits with maxTransitions := 3 } ==
  some (.resource .transitions)
#guard quoteError { adapterLimits with maxEvents := 3 } ==
  some (.resource .events)
#guard quoteError { adapterLimits with maxStructuralCells := 68 } ==
  some (.resource .structuralCells)

-- A one-under proof chronology cap is independent of the retained runtime cap.
#guard quoteError { adapterLimits with proof := { proofLimits with maxChronology := 3 } } ==
  some (.proof .chronologyLimit)

def packageWith (instanceHandler equalityHandler transportHandler factHandler :
    Handler Range (Runtime.Batch Range Nat) Unit) :
    Package Range (Runtime.Batch Range Nat) :=
  { runtimePackage with handlers :=
      #[instanceHandler, equalityHandler, transportHandler, factHandler,
        splitHandler] }

def badInstanceBatch (request : RuleRequest Range) : Runtime.Batch Range Nat :=
  { events := #[.instance
      { action := request.action, after := extendedProgram,
        freshFacts := #[.all, .all], bindings,
        newNodes := [node 3, node 4],
        newBindings := [equalityBinding, transportBinding, factBinding],
        newApplications := [{ index := 1 }, { index := 3 }, { index := 2 }, { index := 4 }],
        generation := 1, quote := instanceQuote }] }

def badEqualityBatch (request : RuleRequest Range) : Runtime.Batch Range Nat :=
  { events := #[.equality
      { action := request.action, equality := { index := 0 },
        left := node 2, right := node 2, generation := 1,
        assumptions := [], quote := equalityQuote }] }

def badTransportBatch (request : RuleRequest Range) : Runtime.Batch Range Nat :=
  { events := #[.transport
      { action := request.action,
        update :=
          { programVersion := 1
            node := node 2
            previous := { node := node 2, version := 0 }
            fact := .nonpositive
            version := 1
            cause := 41 },
        equality := { index := 0 }, source := { node := node 3, version := 0 } }] }

def badInstanceHandler : Handler Range (Runtime.Batch Range Nat) Unit :=
  handler instanceRule #[exactFormat .instance [1]] (fun _ _ => false) badInstanceBatch

def badEqualityHandler : Handler Range (Runtime.Batch Range Nat) Unit :=
  handler equalityRule #[exactFormat .equality [1]] accepts badEqualityBatch

def badTransportHandler : Handler Range (Runtime.Batch Range Nat) Unit :=
  handler transportRule #[] accepts badTransportBatch

private def runtimeWith? (package : Package Range (Runtime.Batch Range Nat)) :
    Option (Runtime.State Range Nat) :=
  match Executable.buildWithin executableLimits #[package] baseProgram, branch? with
  | .ok assembly, some branch =>
      (Runtime.State.startWithin runtimeLimits assembly branch).toOption
  | _, _ => none

private def instanceError (package : Package Range (Runtime.Batch Range Nat)) :
    Option Runtime.Error :=
  match runtimeWith? package with
  | none => none
  | some runtime =>
      match runtime.stepWithin runtimeLimits instanceAction with
      | .error error => some error
      | .ok _ => none

private def equalityError (package : Package Range (Runtime.Batch Range Nat)) :
    Option Runtime.Error :=
  match runtimeWith? package with
  | none => none
  | some runtime =>
      match runtime.stepWithin runtimeLimits instanceAction with
      | .error _ => none
      | .ok (_, runtime) =>
          match runtime.stepWithin runtimeLimits equalityAction with
          | .error error => some error
          | .ok _ => none

private def transportError (package : Package Range (Runtime.Batch Range Nat)) :
    Option Runtime.Error :=
  match runtimeWith? package with
  | none => none
  | some runtime =>
      match runtime.stepWithin runtimeLimits instanceAction with
      | .error _ => none
      | .ok (_, runtime) =>
          match runtime.stepWithin runtimeLimits equalityAction with
          | .error _ => none
          | .ok (_, runtime) =>
              match runtime.stepWithin runtimeLimits factAction with
              | .error _ => none
              | .ok (_, runtime) =>
                  match runtime.stepWithin runtimeLimits transportAction with
                  | .error error => some error
                  | .ok _ => none

#guard instanceError (packageWith badInstanceHandler equalityHandler
    transportHandler factHandler) == some .malformed

#guard equalityError (packageWith instanceHandler badEqualityHandler
    transportHandler factHandler) == some .wrongEquality

#guard transportError (packageWith instanceHandler equalityHandler
    badTransportHandler factHandler) == some .unauthorized

def proposedFactBatch (request : RuleRequest Range) : Runtime.Batch Range Nat :=
  { factBatch request with events := (factBatch request).events.map fun
      | .fact step => .fact { step with proposed := .all }
      | event => event }

def proposedFactHandler : Handler Range (Runtime.Batch Range Nat) Unit :=
  handler factRule #[exactFormat .fact [Range.nonpositive.code]] accepts proposedFactBatch

def proposedPackage : Package Range (Runtime.Batch Range Nat) :=
  packageWith instanceHandler equalityHandler transportHandler proposedFactHandler

def looseFactQuote : Quote := { role := .fact, schema := 1, body := [0] }

def looseFactBatch (request : RuleRequest Range) : Runtime.Batch Range Nat :=
  { factBatch request with events := (factBatch request).events.map fun
      | .fact step => .fact { step with quote := looseFactQuote }
      | event => event }

def looseFactHandler : Handler Range (Runtime.Batch Range Nat) Unit :=
  handler factRule
    #[{ role := .fact, schema := 1, validateBody := fun body => body.length == 1 }]
    accepts looseFactBatch

def loosePackage : Package Range (Runtime.Batch Range Nat) :=
  packageWith instanceHandler equalityHandler transportHandler looseFactHandler

private def assemblyWith? (package : Package Range (Runtime.Batch Range Nat)) :
    Option (RuntimeProof.Assembly Range Nat) :=
  (Executable.buildWithin executableLimits #[package] baseProgram).toOption

private def registryWith? (package : Package Range (Runtime.Batch Range Nat)) :
    Option (RuntimeProof.Registry Range semantics Nat Nat) :=
  match assemblyWith? package, proofRegistry? with
  | some assembly, some proof =>
      (RuntimeProof.Registry.buildWithin executableLimits adapterKey assembly proof).toOption
  | _, _ => none

private def treeWith? (package : Package Range (Runtime.Batch Range Nat)) :
    Option (Search.Result.Tree Range Nat Nat Proof.Key) :=
  match branch?, assemblyWith? package with
  | some branch, some assembly =>
      match Search.Result.startWithin resultLimits measure scope branch with
      | .error _ => none
      | .ok tree => runCurrent tree assembly
  | _, _ => none

private def packageQuoteError
    (package : Package Range (Runtime.Batch Range Nat)) : Option RuntimeProof.Error :=
  match registryWith? package, treeWith? package with
  | some registry, some tree =>
      match RuntimeProof.quoteTreeWithin adapterLimits measure registry tree with
      | .error error => some error
      | .ok _ => none
  | _, _ => none

private def packageReplayError
    (package : Package Range (Runtime.Batch Range Nat)) : Option RuntimeProof.Error :=
  match registryWith? package, treeWith? package with
  | some registry, some tree =>
      match RuntimeProof.quoteTreeWithin adapterLimits measure registry tree with
      | .error _ => none
      | .ok bundle =>
          match RuntimeProof.replayTree adapterLimits measure registry domain laws input bundle with
          | .error error => some error
          | .ok _ => none
  | _, _ => none

#guard packageQuoteError loosePackage == some (.invalidBody factProofKey)
#guard packageReplayError proposedPackage == some (.proof .malformedBody)

-- The proof package cannot attach an equality schema to another package's rule.
def foreignFactPackage : Proof.Package semantics Nat :=
  { registrations := #[factRule], equalities := #[equalitySchema] }

#guard match Proof.Registry.buildWithin proofLimits baseProgram #[foreignFactPackage] with
  | .error (.foreignSchema 0 key) => key == equalityProofKey
  | _ => false

-- Numeric schema drift is rejected by bidirectional registry coverage.
def schemaTwoFormat : ReplayFormat :=
  { role := .fact, schema := 2, validateBody := fun body => body == [3] }

def schemaTwoHandler : Handler Range (Runtime.Batch Range Nat) Unit :=
  handler factRule #[schemaTwoFormat] accepts factBatch

def schemaTwoPackage : Package Range (Runtime.Batch Range Nat) :=
  { runtimePackage with handlers := runtimePackage.handlers.set! 3 schemaTwoHandler }

def schemaTwoAssembly? : Option (RuntimeProof.Assembly Range Nat) :=
  (Executable.buildWithin { executableLimits with maxSchema := 2 }
    #[schemaTwoPackage] baseProgram).toOption

#guard match schemaTwoAssembly?, proofRegistry? with
  | some assembly, some proof =>
      match RuntimeProof.Registry.buildWithin { executableLimits with maxSchema := 2 }
          adapterKey assembly proof with
      | .error .invalidRegistry => true
      | _ => false
  | _, _ => false

-- Search/runtime sealing rejects chronology reuse and a transition splice
-- across independently restarted split children before quotation can begin.
#guard match branch?, rootTree?, splitTree? with
  | some branch, some root, some split =>
      match Search.Result.startWithin resultLimits measure scope branch,
          root.transitions[0]?.map (·.2), split.transitions[4]?.map (·.2) with
      | .ok fresh, some first, some foreign =>
          match Search.Result.advanceRuntimeWithin resultLimits measure fresh first with
          | .error _ => false
          | .ok afterFirst =>
              match Search.Result.advanceRuntimeWithin resultLimits measure afterFirst first,
                  Search.Result.advanceRuntimeWithin resultLimits measure fresh foreign with
              | .error .malformed, .error .malformed => true
              | _, _ => false
      | _, _, _ => false
  | _, _, _ => false

/--
info: 'Hex.IntervalMathlib.RuntimeProofConformance.rootSinNeg' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms rootSinNeg

/--
info: 'Hex.IntervalMathlib.RuntimeProofConformance.splitSinNeg' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms splitSinNeg

end Hex.IntervalMathlib.RuntimeProofConformance
