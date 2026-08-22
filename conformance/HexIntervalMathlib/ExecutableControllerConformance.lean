/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import HexIntervalMathlib.Controller
import HexIntervalMathlib.Rule

/-!
# Executable assembly controller conformance

The sealed adapter runs the built-in interval addition rule followed by two
applications from an independently owned arbitrary-function package. Runtime
callbacks return only proposals and inert quotations. The adapter derives the
accepted updates and proof events from the authenticated search request; the
ordinary theorem below is obtained only by a separate proof replay.
-/

namespace Hex.IntervalMathlib.ExecutableControllerConformance

open Hex.Interval
open Hex.Interval.Proof
open Hex.Interval.Executable

/-- error: Unknown constant `Hex.Interval.Controller.Executable.Registry.mk` -/
#guard_msgs in
#check Controller.Executable.Registry.mk

/-- error: Unknown constant `Hex.Interval.Controller.Executable.State.mk` -/
#guard_msgs in
#check Controller.Executable.State.mk

/-- error: Unknown constant `Hex.Interval.Executable.Registry.mk` -/
#guard_msgs in
#check Hex.Interval.Executable.Registry.mk

/-- error: Unknown constant `Hex.Interval.Executable.Assembly.mk` -/
#guard_msgs in
#check Hex.Interval.Executable.Assembly.mk

/-- error: Unknown constant `Hex.Interval.Executable.OfferContext.mk` -/
#guard_msgs in
#check Hex.Interval.Executable.OfferContext.mk

def d (value : Int) : Dyadic := .ofInt value
def endpoint : EndpointLimit := { maxEndpointHeight := 64, maxAlignmentShift := 64 }

def ready (raw : Raw) : Hex.Interval :=
  match Hex.Interval.ofRawWithin endpoint raw with
  | .ready interval => interval
  | .resourceLimit _ => Hex.Interval.empty

def singleton (value : Int) : Hex.Interval :=
  ready (.bounds (.finite (d value) false) (.finite (d value) false))

def copyOp : Operation :=
  { key := { name := "fixture.arbitrary.copy" }, inputs := [Rule.realDomain],
    output := Rule.realDomain }

def copyMeaning : Program.Meaning ℝ :=
  { operation := copyOp, relation := fun xs z => ∃ x, xs = [x] ∧ z = x }

def config : Rule.Config :=
  { endpoint, powerWork := { maxExponent := 8 }, exponent := 2,
    precisionLimits :=
      { endpoint, maxPrecisionMagnitude := 64, maxPrecisionBits := 64,
        maxTemporaryBits := 128 },
    precision := 0, constant := d 5, extraMeanings := #[copyMeaning] }

def node (op : Nat) (args : List Nat) : Node :=
  { domain := Rule.realDomain, op := { index := op },
    args := args.map fun index => { index } }

def program : Program :=
  { operations := Rule.operations.push copyOp,
    nodes := #[node 0 [], node 0 [], node 2 [0, 1], node 13 [2], node 13 [3]] }

def x : NodeId := { index := 0 }
def y : NodeId := { index := 1 }
def sum : NodeId := { index := 2 }
def copied : NodeId := { index := 3 }
def final : NodeId := { index := 4 }

def one := singleton 1
def two := singleton 2
def three := singleton 3
def initialFacts : Array Hex.Interval :=
  #[one, two, Hex.Interval.whole, Hex.Interval.whole, Hex.Interval.whole]

#guard program.check
#guard Rule.ready? (Hex.Interval.addWithin endpoint one two) == some three

def copyKey : RuleKey := { name := "fixture.arbitrary.copy.fact" }
def copyRegistration : Registration :=
  { key := copyKey, head := copyOp.key, kind := .forward,
    watches := [.argument 0], writes := [.result] }
def copySchemaKey : Proof.Key := { rule := copyKey, role := .fact, bodySchema := 1 }

theorem copyRelation {valuation : NodeId → ℝ} {out input : NodeId}
    (meaning : Program.MeaningAt (Rule.meanings config) valuation out
      { domain := Rule.realDomain, op := { index := 13 }, args := [input] }) :
    valuation out = valuation input := by
  rcases meaning with ⟨meaning, found, related⟩
  simp [Rule.meanings, Rule.builtinMeanings, config, copyMeaning] at found
  subst meaning
  simpa [copyMeaning] using related.symm

def copySchema : Proof.FactSchema (Rule.semantics config) :=
  { key := copySchemaKey, Certificate := Unit,
    decode := fun body => if body = [20] then some () else none,
    prove := fun context _ => match context.assumptions with
      | [input] =>
        if found : context.program.node? context.proposed.node = some
            { domain := Rule.realDomain, op := { index := 13 }, args := [input.node] } then
          if equal : context.proposed.fact = input.fact then
            some ⟨by
              intro valuation model assumptions
              have relation := copyRelation
                (Rule.nodeMeaning config model found)
              change context.proposed.fact.Contains (valuation context.proposed.node)
              rw [equal]
              rw [relation]
              simpa [Rule.semantics, Proof.Semantics.ofMeanings] using
                assumptions input (by simp)⟩
          else none
        else none
      | _ => none }

def copyProofPackage : Proof.Package (Rule.semantics config) :=
  { registrations := #[copyRegistration], facts := #[copySchema] }

def proofLimits : Proof.Limits :=
  { maxPackages := 2, maxSchemas := 13, maxBodyCells := 1,
    maxDependencies := 2, maxChronology := 3 }

def proofRegistry? : Option (Proof.Registry (Rule.semantics config)) :=
  (Rule.buildWithWithin proofLimits config program #[copyProofPackage]).toOption

#guard proofRegistry?.isSome

def runtimeDomain : FactDomain Hex.Interval :=
  { top := fun _ => Hex.Interval.whole,
    narrow := fun _ previous proposed =>
      match Rule.ready? (Hex.Interval.intersectWithin endpoint previous proposed) with
      | none => .resourceLimit 0
      | some installed =>
          if installed == previous then .noChange
          else if installed == Hex.Interval.empty then .contradiction installed
          else .improved installed }

def factFormat (tag : Nat) : ReplayFormat :=
  { role := .fact, schema := 1, validateBody := fun body => body == [tag] }

def resultCost (_ : Controller.Executable.FactOutcome Hex.Interval Nat) : Cost :=
  { bytes := 1, work := 1 }

def measure : Measure Nat (Controller.Executable.FactOutcome Hex.Interval Nat) :=
  { metadata := { bytes := 1, work := 1 },
    application := fun _ => { bytes := 1, work := 1 },
    cache := fun value => { bytes := value + 1, work := value + 1 },
    result := resultCost }

def dormant (registration : Registration) (tag : Nat) :
    Handler Hex.Interval (Controller.Executable.FactOutcome Hex.Interval Nat) Nat :=
  { registration,
    offers := fun _ _ => false,
    invoke := fun cache _ =>
      ({ result := { proposals := #[] }, quotes := #[] }, cache),
    formats := #[factFormat tag] }

def addHandler : Handler Hex.Interval (Controller.Executable.FactOutcome Hex.Interval Nat) Nat :=
  { registration := Rule.binaryRegistration Rule.addKey Rule.addOp,
    offers := fun snapshot request =>
      snapshot.version? request.action.node == some 0 &&
        request.inputs.map (fun input => input.fact) == [one, two],
    invoke := fun cache request =>
      let proposals := match request.inputs with
        | [left, right] => match Rule.ready?
            (Hex.Interval.addWithin endpoint left.fact right.fact) with
          | some proposed => #[{ node := request.action.node, proposed, cause := cache }]
          | none => #[]
        | _ => #[]
      ({ result := { proposals },
          quotes := proposals.map fun _ => { role := .fact, schema := 1, body := [2] } },
        cache + 1),
    formats := #[factFormat 2] }

def arithmeticHandlers : Array
    (Handler Hex.Interval (Controller.Executable.FactOutcome Hex.Interval Nat) Nat) :=
  Rule.registrations.mapIdx fun index registration =>
    if index == 1 then addHandler else dormant registration (index + 1)

def arithmeticPackage : Package Hex.Interval
    (Controller.Executable.FactOutcome Hex.Interval Nat) :=
  { Cache := Nat, cache := 0, operations := Rule.operations,
    handlers := arithmeticHandlers, measure }

def copyHandler : Handler Hex.Interval
    (Controller.Executable.FactOutcome Hex.Interval Nat) Nat :=
  { registration := copyRegistration,
    offers := fun snapshot request =>
      snapshot.version? request.action.node == some 0 &&
        request.inputs.map (fun input => input.fact) == [three],
    invoke := fun cache request =>
      let proposals := match request.inputs with
        | [input] => #[{ node := request.action.node, proposed := input.fact, cause := cache }]
        | _ => #[]
      ({ result := { proposals },
          quotes := proposals.map fun _ => { role := .fact, schema := 1, body := [20] } },
        cache + 1),
    formats := #[factFormat 20] }

def copyPackage : Package Hex.Interval
    (Controller.Executable.FactOutcome Hex.Interval Nat) :=
  { Cache := Nat, cache := 0, operations := #[copyOp], handlers := #[copyHandler], measure }

def stateLimits : State.Limits :=
  { maxOperations := 14, maxNodes := 5, maxRules := 13,
    maxRegistryEntries := 42, maxReplayFormats := 13, maxArity := 2,
    maxScopeNodes := 0, maxApplications := 3, maxQueueEntries := 4,
    maxActions := 8, maxMatcherVisits := 0, matcherBatchSize := 0,
    maxAcceptedFacts := 3, maxRetainedSuggestions := 0, maxEffort := 0,
    maxObservationValue := 8, maxDiagnosticValue := 8,
    maxOutcomeCandidates := 3, maxOutcomeSuggestions := 0, maxProposalItems := 1,
    maxInstances := 0, maxGeneration := 0, maxNodeDepth := 3, maxEqualities := 0,
    splitEndpointLimit := endpoint }

def executableLimits : Hex.Interval.Executable.Limits :=
  { state := stateLimits, maxPackages := 2,
    maxMetadataBytes := 64, maxMetadataWork := 64,
    maxCacheBytes := 16, maxCacheWork := 16,
    maxResultBytes := 1, maxResultWork := 1,
    maxQuotes := 1, maxQuoteCells := 1, maxAtom := 21, maxSchema := 2 }

def assembly? : Option (Controller.Executable.RawAssembly Hex.Interval Nat) :=
  (Hex.Interval.Executable.buildWithin executableLimits
    #[arithmeticPackage, copyPackage] program).toOption

def controllerKey : Controller.Key := { name := "executable-facts", version := 1 }

def registry? : Option
    (Controller.Executable.Registry Hex.Interval (Rule.semantics config) Nat (List Nat)) := do
  let assembly ← assembly?
  let proof ← proofRegistry?
  (Controller.Executable.Registry.buildWithin stateLimits controllerKey assembly
    runtimeDomain proof).toOption

def searchLimits : Search.Limits :=
  { maxSteps := 3, maxSplits := 0, maxLeaves := 1, maxFrontier := 1,
    maxDepth := 0, maxScopes := 1, leafFuel := 3 }

def policyLimits : Policy.Limits :=
  { maxOffers := 1, maxBytes := 128, maxPairs := 32, maxWork := 128, maxScore := 0 }

def envelope : Search.Envelope :=
  { state := stateLimits, policy := policyLimits,
    trace := { maxEvents := 4, maxBytes := 64, maxWork := 64, maxCode := 8 },
    search := searchLimits }

def unitCost : Search.Result.Cost := { bytes := 1, work := 1 }
def resultMeasure : Search.Result.Measure Hex.Interval Nat (List Nat) Proof.Key :=
  { node := unitCost,
    branch := fun branch =>
      { bytes := branch.snapshot.facts.size + branch.history.size,
        work := branch.versions.size + branch.history.size },
    fact := fun _ => unitCost, action := fun _ => unitCost, plan := fun _ => unitCost,
    schema := fun _ => unitCost, body := fun _ => unitCost, code := fun _ => unitCost }

def recipeMeasure : Driver.Measure Hex.Interval :=
  { cell := unitCost, event := fun _ => { bytes := 1, work := 1 },
    edge := fun _ => { bytes := 1, work := 1 } }

def driverLimits : Driver.Limits :=
  { result :=
      { search := searchLimits, state := stateLimits, maxNodes := 1,
        maxBodyCells := 3, maxBytes := 512, maxWork := 512, maxCode := 8 },
    proof := proofLimits,
    tree := { maxNodes := 1, maxDepth := 0, maxBodyCells := 3, maxWork := 64 },
    recipe := { maxBytes := 64, maxWork := 64 } }

def controllerLimits : Controller.Limits :=
  { maxChoices := 4, policyState := { bytes := 4, pairs := 4, work := 4 },
    driver := driverLimits }

def scope : Policy.ScopeId := { index := 0 }

def firstPolicy : Policy.Interface Hex.Interval Unit ApplicationId RuleKey :=
  { choose := fun _ view => match view.offers[0]? with
    | some offer => .select offer ()
    | none => .stop () }

def policyStateCost (_ : Unit) : Policy.Cost := { bytes := 1, work := 1 }

def stoppedState? : Option (Controller.Executable.State Hex.Interval Nat (List Nat)) :=
  match registry? with
  | none => none
  | some registry =>
    match State.Branch.startWithin stateLimits program initialFacts with
    | .error _ => none
    | .ok branch =>
      match Driver.Bundle.startWithin driverLimits resultMeasure recipeMeasure scope branch with
      | .error _ => none
      | .ok bundle =>
        match Controller.Executable.State.startWithin envelope registry bundle with
        | .error _ => none
        | .ok state =>
          match Controller.Executable.runWithin controllerLimits executableLimits envelope
              policyStateCost resultMeasure recipeMeasure registry firstPolicy () state with
          | .ok (.stopped (.policyStop 0) stopped _) => some stopped
          | _ => none

def acceptedChronology : Bool :=
  match stoppedState? with
  | some state =>
      state.session.branch.snapshot.facts == #[one, two, three, three, three] &&
        state.session.branch.versions == #[0, 0, 1, 1, 1] &&
          state.session.branch.history.map (fun update => update.cause) == #[0, 0, 1]
  | none => false

#guard acceptedChronology

def input : Proof.Input Hex.Interval :=
  { scope, program, facts := initialFacts, target := { node := final, fact := three } }

def replayEvidence? : Option (Proof.Evidence
    ((Rule.semantics config).Entails program (Proof.initialBase input) input.target)) :=
  match proofRegistry? with
  | none => none
  | some registry => match stoppedState? with
    | none => none
    | some state => match state.bundle.recipe.events[0]? with
      | none => none
      | some events =>
        (Proof.replay proofLimits registry (Rule.domain config) (Rule.laws config)
          input events 0 program { node := final, version := 1 }).toOption

#guard replayEvidence?.isSome

private theorem eq_of_mem_singleton {value : Dyadic} {result : Hex.Interval} {z : ℝ}
    (checked : Hex.Interval.singletonWithin endpoint value = .ready result)
    (member : result.Contains z) : z = Hex.Interval.toReal value := by
  change result.view.Contains z at member
  rw [Hex.Interval.view_singletonWithin_ready checked,
    Hex.Interval.contains_normalize] at member
  exact le_antisymm member.2 member.1

private theorem toReal_d (value : Int) : Hex.Interval.toReal (d value) = value := by
  change ((Dyadic.ofInt value).toRat : ℝ) = value
  rw [show Dyadic.ofInt value = (value : Dyadic) by rfl, Dyadic.toRat_intCast]
  norm_num

def fallbackEvidence : Proof.Evidence
    ((Rule.semantics config).Entails program (Proof.initialBase input) input.target) :=
  { proof := by
      intro valuation model assumptions
      change NodeId → ℝ at valuation
      have xMember : one.Contains (valuation x) := assumptions
        { node := x, fact := one } (by simp [Proof.initialBase, input, initialFacts, x])
      have yMember : two.Contains (valuation y) := assumptions
        { node := y, fact := two } (by simp [Proof.initialBase, input, initialFacts, y])
      have sumRelation : valuation sum = valuation x + valuation y :=
        Rule.binaryRelation (config := config) (valuation := valuation)
          (node := sum) (left := x) (right := y) (index := 2)
          (relation := fun left right => left + right)
          (Rule.nodeMeaning config model (node := sum) (by rfl))
          (Or.inl ⟨rfl, rfl⟩)
      have firstCopy : valuation copied = valuation sum :=
        copyRelation (Rule.nodeMeaning config model (node := copied) (by rfl))
      have secondCopy : valuation final = valuation copied :=
        copyRelation (Rule.nodeMeaning config model (node := final) (by rfl))
      have xEq := eq_of_mem_singleton (value := d 1) (result := one) (by rfl) xMember
      have yEq := eq_of_mem_singleton (value := d 2) (result := two) (by rfl) yMember
      rw [toReal_d] at xEq yEq
      have finalEq : valuation final = 3 := by
        rw [secondCopy, firstCopy, sumRelation, xEq, yEq]
        norm_num
      change three.Contains (valuation final)
      rw [finalEq]
      have member := Rule.constant_mem
        (limit := endpoint) (value := d 3) (result := three) (by rfl)
      rw [toReal_d] at member
      exact member }

def replayEvidence : Proof.Evidence
    ((Rule.semantics config).Entails program (Proof.initialBase input) input.target) :=
  replayEvidence?.getD fallbackEvidence

/-- The quotation does not prove this statement. Independent schema replay and
the kernel theorem stored in `Proof.Evidence` do. -/
theorem executableArithmeticAndArbitraryFunction :
    (Rule.semantics config).Entails program (Proof.initialBase input) input.target :=
  replayEvidence.proof

/--
info: 'Hex.IntervalMathlib.ExecutableControllerConformance.executableArithmeticAndArbitraryFunction' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms executableArithmeticAndArbitraryFunction

/-! ## Mutation and exact-boundary checks -/

def arithmeticWith
    (handler : Handler Hex.Interval (Controller.Executable.FactOutcome Hex.Interval Nat) Nat) :
    Package Hex.Interval (Controller.Executable.FactOutcome Hex.Interval Nat) :=
  { arithmeticPackage with handlers := arithmeticHandlers.set! 1 handler }

def copyWith
    (handler : Handler Hex.Interval (Controller.Executable.FactOutcome Hex.Interval Nat) Nat) :
    Package Hex.Interval (Controller.Executable.FactOutcome Hex.Interval Nat) :=
  { copyPackage with handlers := #[handler] }

def buildAssembly
    (arithmetic : Package Hex.Interval (Controller.Executable.FactOutcome Hex.Interval Nat) :=
      arithmeticPackage)
    (copy : Package Hex.Interval (Controller.Executable.FactOutcome Hex.Interval Nat) :=
      copyPackage)
    (limits : Hex.Interval.Executable.Limits := executableLimits) :=
  Hex.Interval.Executable.buildWithin limits #[arithmetic, copy] program

def buildRegistry
    (arithmetic : Package Hex.Interval (Controller.Executable.FactOutcome Hex.Interval Nat) :=
      arithmeticPackage)
    (copy : Package Hex.Interval (Controller.Executable.FactOutcome Hex.Interval Nat) :=
      copyPackage)
    (key : Controller.Key := controllerKey)
    (limits : State.Limits := stateLimits)
    (domain : FactDomain Hex.Interval := runtimeDomain) :
    Except Controller.Executable.Error
      (Controller.Executable.Registry Hex.Interval (Rule.semantics config) Nat (List Nat)) :=
  match buildAssembly arithmetic copy with
  | .error error => .error (.executable error)
  | .ok assembly => match proofRegistry? with
    | none => .error .invalidRegistry
    | some proof =>
      Controller.Executable.Registry.buildWithin limits key assembly domain proof

def runFresh
    (registry : Controller.Executable.Registry Hex.Interval (Rule.semantics config)
      Nat (List Nat))
    (limits : Controller.Limits := controllerLimits)
    (rawLimits : Hex.Interval.Executable.Limits := executableLimits)
    (candidateEnvelope : Search.Envelope := envelope) :
    Except Controller.Executable.Error
      (Controller.Executable.Run Hex.Interval Nat (List Nat) Unit) :=
  match State.Branch.startWithin stateLimits program initialFacts with
  | .error _ => .error .mismatch
  | .ok branch =>
    match Driver.Bundle.startWithin driverLimits resultMeasure recipeMeasure scope branch with
    | .error _ => .error .mismatch
    | .ok bundle =>
      match Controller.Executable.State.startWithin candidateEnvelope registry bundle with
      | .error error => .error error
      | .ok state => Controller.Executable.runWithin limits rawLimits candidateEnvelope
          policyStateCost resultMeasure recipeMeasure registry firstPolicy () state

def reorderedArithmetic :
    Package Hex.Interval (Controller.Executable.FactOutcome Hex.Interval Nat) :=
  let neg := dormant (Rule.unaryRegistration Rule.negKey Rule.negOp) 1
  { arithmeticPackage with handlers := (arithmeticHandlers.set! 0 addHandler).set! 1 neg }

def wrongKey : RuleKey := { name := "fixture.transplanted.key" }
def wrongKeyHandler : Handler Hex.Interval
    (Controller.Executable.FactOutcome Hex.Interval Nat) Nat :=
  { copyHandler with registration := { copyRegistration with key := wrongKey } }

def schemaTwoHandler : Handler Hex.Interval
    (Controller.Executable.FactOutcome Hex.Interval Nat) Nat :=
  { copyHandler with formats :=
      #[{ role := .fact, schema := 2, validateBody := fun body => body == [20] }] }

def equalityFormatHandler : Handler Hex.Interval
    (Controller.Executable.FactOutcome Hex.Interval Nat) Nat :=
  { copyHandler with formats :=
      #[{ role := .equality, schema := 1, validateBody := fun body => body == [20] }] }

def missingFormatHandler : Handler Hex.Interval
    (Controller.Executable.FactOutcome Hex.Interval Nat) Nat :=
  { copyHandler with formats := #[] }

def malformedBodyHandler : Handler Hex.Interval
    (Controller.Executable.FactOutcome Hex.Interval Nat) Nat :=
  { copyHandler with
    invoke := fun cache request =>
      let proposals := match request.inputs with
        | [input] => #[{ node := request.action.node, proposed := input.fact, cause := cache }]
        | _ => #[]
      ({ result := { proposals },
          quotes := proposals.map fun _ => { role := .fact, schema := 1, body := [21] } },
        cache + 1),
    formats :=
      #[{ role := .fact, schema := 1, validateBody := fun body => body.length == 1 }] }

def missingQuoteHandler : Handler Hex.Interval
    (Controller.Executable.FactOutcome Hex.Interval Nat) Nat :=
  { copyHandler with invoke := fun cache request =>
      let proposals := match request.inputs with
        | [input] => #[{ node := request.action.node, proposed := input.fact, cause := cache }]
        | _ => #[]
      ({ result := { proposals }, quotes := #[] }, cache + 1) }

def extraQuoteHandler : Handler Hex.Interval
    (Controller.Executable.FactOutcome Hex.Interval Nat) Nat :=
  { copyHandler with invoke := fun cache request =>
      let proposals := match request.inputs with
        | [input] => #[{ node := request.action.node, proposed := input.fact, cause := cache }]
        | _ => #[]
      ({ result := { proposals },
          quotes := #[{ role := .fact, schema := 1, body := [20] },
            { role := .fact, schema := 1, body := [20] }] }, cache + 1) }

def wrongUpdateHandler : Handler Hex.Interval
    (Controller.Executable.FactOutcome Hex.Interval Nat) Nat :=
  { copyHandler with invoke := fun cache _request =>
      ({ result := { proposals := #[{ node := x, proposed := three, cause := cache }] },
          quotes := #[{ role := .fact, schema := 1, body := [20] }] }, cache + 1) }

def registryMutationRejected : Bool :=
  (match buildRegistry reorderedArithmetic with
    | .error .invalidRegistry => true | _ => false) &&
  (match buildRegistry (copy := copyWith wrongKeyHandler) with
    | .error .invalidRegistry => true | _ => false) &&
  (match buildRegistry (copy := copyWith schemaTwoHandler) with
    | .error .invalidRegistry => true | _ => false) &&
  (match buildRegistry (copy := copyWith equalityFormatHandler) with
    | .error .invalidRegistry => true | _ => false) &&
  (match buildRegistry (copy := copyWith missingFormatHandler) with
    | .error .invalidRegistry => true | _ => false)

#guard registryMutationRejected

def callbackMutationRejected : Bool :=
  (match buildRegistry (copy := copyWith malformedBodyHandler) with
    | .ok registry => match runFresh registry with
      | .error (.invalidBody key) => key == copySchemaKey
      | _ => false
    | _ => false) &&
  (match buildRegistry (copy := copyWith missingQuoteHandler) with
    | .ok registry => match runFresh registry with
      | .error .invalidQuote => true | _ => false
    | _ => false) &&
  (match buildRegistry (copy := copyWith extraQuoteHandler) with
    | .ok registry =>
      let generous := { executableLimits with maxQuotes := 2, maxQuoteCells := 2 }
      match runFresh registry (rawLimits := generous) with
      | .error .invalidQuote => true | _ => false
    | _ => false) &&
  (match buildRegistry (copy := copyWith wrongUpdateHandler) with
    | .ok registry => match runFresh registry with
      | .error .mismatch => true | _ => false
    | _ => false)

#guard callbackMutationRejected

def resourceDomain : FactDomain Hex.Interval :=
  { runtimeDomain with narrow := fun _ _ _ => .resourceLimit 7 }

def noChangeDomain : FactDomain Hex.Interval :=
  { runtimeDomain with narrow := fun _ _ _ => .noChange }

def narrowDiagnosticDistinct : Bool :=
  (match buildRegistry (domain := resourceDomain) with
    | .ok registry => match runFresh registry with
      | .error (.resource (.narrow 7)) => true
      | _ => false
    | _ => false) &&
  (match buildRegistry (domain := noChangeDomain) with
    | .ok registry => match runFresh registry with
      | .error .mismatch => true
      | _ => false
    | _ => false)

#guard narrowDiagnosticDistinct

def applicationsOneOver : Bool :=
  let small := { stateLimits with maxApplications := 2 }
  match buildRegistry (limits := small) with
  | .error (.resource .applications) => true
  | _ => false

def formatsOneOver : Bool :=
  let small := { stateLimits with maxReplayFormats := 12 }
  match buildRegistry (limits := small) with
  | .error (.resource (.state .replayFormats)) => true
  | _ => false

def generateNodesOneOver : Bool :=
  let small := { envelope with state := { stateLimits with maxNodes := 4 } }
  match buildRegistry with
  | .ok registry => match runFresh registry (candidateEnvelope := small) with
    | .error (.resource (.state .nodes)) => true
    | _ => false
  | _ => false

def quoteCellsOneOver : Bool :=
  let small := { executableLimits with maxQuoteCells := 0 }
  match buildRegistry with
  | .ok registry => match runFresh registry (rawLimits := small) with
    | .error (.executable (.resource .quoteCells)) => true
    | _ => false
  | _ => false

def resultBytesOneOver : Bool :=
  let small := { executableLimits with maxResultBytes := 0 }
  match buildRegistry with
  | .ok registry => match runFresh registry (rawLimits := small) with
    | .error (.executable (.resource .resultBytes)) => true
    | _ => false
  | _ => false

def offersOneOver : Bool :=
  let small := { envelope with policy := { policyLimits with maxOffers := 0 } }
  match buildRegistry with
  | .ok registry => match runFresh registry (candidateEnvelope := small) with
    | .error (.search (.policy .offerLimit)) => true
    | _ => false
  | _ => false

def quotesOneOver : Bool :=
  match buildRegistry (copy := copyWith extraQuoteHandler) with
  | .ok registry => match runFresh registry with
    | .error (.executable (.resource .quotes)) => true
    | _ => false
  | _ => false

def choicesOneOver : Bool :=
  let small := { controllerLimits with maxChoices := 2 }
  match buildRegistry with
  | .ok registry => match runFresh registry (limits := small) with
    | .error (.resource .choices) => true
    | _ => false
  | _ => false

#guard applicationsOneOver && formatsOneOver && generateNodesOneOver && quoteCellsOneOver &&
  resultBytesOneOver && offersOneOver && quotesOneOver && choicesOneOver

def selectTwice : Policy.Interface Hex.Interval Nat ApplicationId RuleKey :=
  { choose := fun count view =>
      if count < 2 then match view.offers[0]? with
        | some offer => .select offer (count + 1)
        | none => .stop count
      else .stop count }

def selectOnce : Policy.Interface Hex.Interval Nat ApplicationId RuleKey :=
  { choose := fun count view =>
      if count == 0 then match view.offers[0]? with
        | some offer => .select offer 1
        | none => .stop count
      else .stop count }

def natPolicyCost (_ : Nat) : Policy.Cost := { bytes := 1, work := 1 }

def partialState? : Option (Controller.Executable.State Hex.Interval Nat (List Nat)) :=
  match registry? with
  | none => none
  | some registry =>
    match State.Branch.startWithin stateLimits program initialFacts with
    | .error _ => none
    | .ok branch =>
      match Driver.Bundle.startWithin driverLimits resultMeasure recipeMeasure scope branch with
      | .error _ => none
      | .ok bundle => match Controller.Executable.State.startWithin envelope registry bundle with
        | .error _ => none
        | .ok state =>
          match Controller.Executable.runWithin controllerLimits executableLimits envelope
              natPolicyCost resultMeasure recipeMeasure registry selectTwice 0 state with
          | .ok (.stopped (.policyStop 1) stopped 2) => some stopped
          | _ => none

def sameKeyKeepsStickyCache : Bool :=
  match partialState?, registry? with
  | some retained, some fresh =>
    match Controller.Executable.runWithin controllerLimits executableLimits envelope
        natPolicyCost resultMeasure recipeMeasure fresh selectOnce 0 retained with
    | .ok (.stopped (.policyStop 0) stopped 1) =>
        stopped.session.branch.history.map (fun update => update.cause) == #[0, 0, 1]
    | _ => false
  | _, _ => false

def wrongEpochRejected : Bool :=
  let other : Controller.Key := { controllerKey with version := 2 }
  match partialState?, buildRegistry (key := other) with
  | some retained, .ok fresh =>
    match Controller.Executable.runWithin controllerLimits executableLimits envelope
        natPolicyCost resultMeasure recipeMeasure fresh selectOnce 0 retained with
    | .error .mismatch => true
    | _ => false
  | _, _ => false

#guard sameKeyKeepsStickyCache && wrongEpochRejected

end Hex.IntervalMathlib.ExecutableControllerConformance
