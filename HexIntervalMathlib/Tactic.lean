/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexIntervalMathlib.Frontend
public import HexIntervalMathlib.RuntimeRuleEmit
public meta import HexIntervalMathlib.Frontend
public meta import HexIntervalMathlib.RuntimeRuleEmit
public import Mathlib.Lean.Elab.Tactic.Basic
public meta import Mathlib.Tactic.NormNum

@[expose] public section

/-!
# Supported arithmetic tactic frontend

This module is the first supported Meta client of `Frontend`, `Rule`, and
`Proof`. The tactic runs the reified program through the typed controller,
settles the retained target lineage, and passes that sealed chronology through
`RuntimeEmit`. The resulting ordinary theorem crosses `Proof.emitChecked`;
runtime success is never reflected into proof syntax.

The current production subset is forward arithmetic over real local variables,
the configured constant, natural power, precision, reciprocal, and division.
Every computed arithmetic row is followed by the package's authenticated
outward regularization row. The bare tactic uses precision `16`, hence the
dyadic grid `2⁻¹⁶`; programmatic callers may supply another admitted precision.
Automatic regularization contributes a second `Frontend.Term` layer for every
computed arithmetic layer, so the default term-depth cap `32` admits roughly
16 nested arithmetic operations along one expression spine.
Caller cuts use integer endpoints. Unsupported syntax and every resource
refusal fail transactionally.
-/

namespace Hex.Interval.Tactic

open Lean Meta Elab
open Proof

/-! ## Checked result projections used by quoted proof terms -/

def BuildResult.isReady (result : BuildResult) : Bool :=
  match result with
  | .ready _ => true
  | .resourceLimit _ => false

def BuildResult.getValue (result : BuildResult)
    (success : BuildResult.isReady result = true) :
    Hex.Interval :=
  match result with
  | .ready interval => interval
  | .resourceLimit _ => False.elim (by simp [BuildResult.isReady] at success)

theorem BuildResult.eq_ready (result : BuildResult)
    (success : BuildResult.isReady result = true) :
    result = .ready (BuildResult.getValue result success) := by
  cases result with
  | ready _ => rfl
  | resourceLimit _ =>
      simp [Hex.Interval.Tactic.BuildResult.isReady] at success

/-- Extract the exact transparent reification result after kernel-checked
success. -/
def checkedResult (result : Except Frontend.Error Frontend.Result)
    (success : result.toOption.isSome = true) : Frontend.Result :=
  result.toOption.get success

namespace Sources

theorem nil : List.Forall₂
    (fun value : ℝ => fun source : Hex.Interval => source.Contains value) [] [] :=
  .nil

theorem cons {value : ℝ} {source : Hex.Interval} {values : List ℝ}
    {sources : List Hex.Interval} (member : source.Contains value)
    (tail : List.Forall₂
      (fun value : ℝ => fun source : Hex.Interval => source.Contains value)
      values sources) :
    List.Forall₂
      (fun value : ℝ => fun source : Hex.Interval => source.Contains value)
      (value :: values) (source :: sources) :=
  .cons member tail

end Sources

namespace Eval

theorem source {config : Rule.Config} {values : Nat → ℝ} {index : Nat} {value : ℝ}
    (equal : values index = value) :
    (Frontend.Term.source index).eval config values = value := equal

theorem constantMk {endpoint : EndpointLimit} {powerWork : Arithmetic.PowLimits}
    {exponent : Nat} {precisionLimits : Arithmetic.PrecisionLimits}
    {precision : Precision} {constant : Dyadic}
    {extraMeanings : Array (Program.Meaning ℝ)} {values : Nat → ℝ} {value : ℝ}
    (equal : toReal constant = value) :
    Frontend.Term.constant.eval
      { endpoint, powerWork, exponent, precisionLimits, precision, constant,
        extraMeanings } values = value := by
  simpa [Frontend.Term.eval] using equal

theorem neg {config : Rule.Config} {values : Nat → ℝ} {input : Frontend.Term}
    {value : ℝ} (equal : input.eval config values = value) :
    (Frontend.Term.neg input).eval config values = -value := by
  simp [Frontend.Term.eval, equal]

theorem add {config : Rule.Config} {values : Nat → ℝ} {left right : Frontend.Term}
    {leftValue rightValue : ℝ} (leftEq : left.eval config values = leftValue)
    (rightEq : right.eval config values = rightValue) :
    (Frontend.Term.add left right).eval config values = leftValue + rightValue := by
  simp [Frontend.Term.eval, leftEq, rightEq]

theorem sub {config : Rule.Config} {values : Nat → ℝ} {left right : Frontend.Term}
    {leftValue rightValue : ℝ} (leftEq : left.eval config values = leftValue)
    (rightEq : right.eval config values = rightValue) :
    (Frontend.Term.sub left right).eval config values = leftValue - rightValue := by
  simp [Frontend.Term.eval, leftEq, rightEq]

theorem mul {config : Rule.Config} {values : Nat → ℝ} {left right : Frontend.Term}
    {leftValue rightValue : ℝ} (leftEq : left.eval config values = leftValue)
    (rightEq : right.eval config values = rightValue) :
    (Frontend.Term.mul left right).eval config values = leftValue * rightValue := by
  simp [Frontend.Term.eval, leftEq, rightEq]

theorem pow {config : Rule.Config} {values : Nat → ℝ} {input : Frontend.Term}
    {value : ℝ} (equal : input.eval config values = value) :
    (Frontend.Term.pow input).eval config values = value ^ config.exponent := by
  simp [Frontend.Term.eval, equal]

theorem abs {config : Rule.Config} {values : Nat → ℝ} {input : Frontend.Term}
    {value : ℝ} (equal : input.eval config values = value) :
    (Frontend.Term.abs input).eval config values = |value| := by
  simp [Frontend.Term.eval, equal]

theorem min {config : Rule.Config} {values : Nat → ℝ} {left right : Frontend.Term}
    {leftValue rightValue : ℝ} (leftEq : left.eval config values = leftValue)
    (rightEq : right.eval config values = rightValue) :
    (Frontend.Term.min left right).eval config values = min leftValue rightValue := by
  simp [Frontend.Term.eval, leftEq, rightEq, min_def]

theorem max {config : Rule.Config} {values : Nat → ℝ} {left right : Frontend.Term}
    {leftValue rightValue : ℝ} (leftEq : left.eval config values = leftValue)
    (rightEq : right.eval config values = rightValue) :
    (Frontend.Term.max left right).eval config values = max leftValue rightValue := by
  simp [Frontend.Term.eval, leftEq, rightEq, max_def]

theorem inv {config : Rule.Config} {values : Nat → ℝ} {input : Frontend.Term}
    {value : ℝ} (equal : input.eval config values = value) :
    (Frontend.Term.inv input).eval config values = value⁻¹ := by
  simp [Frontend.Term.eval, equal]

theorem div {config : Rule.Config} {values : Nat → ℝ} {left right : Frontend.Term}
    {leftValue rightValue : ℝ} (leftEq : left.eval config values = leftValue)
    (rightEq : right.eval config values = rightValue) :
    (Frontend.Term.div left right).eval config values = leftValue / rightValue := by
  simp [Frontend.Term.eval, leftEq, rightEq]

theorem regularize {config : Rule.Config} {values : Nat → ℝ} {input : Frontend.Term}
    {value : ℝ} (equal : input.eval config values = value) :
    (Frontend.Term.regularize input).eval config values = value := by
  simpa [Frontend.Term.eval] using equal

theorem contains {config : Rule.Config} {values : Nat → ℝ} {term : Frontend.Term}
    {interval : Hex.Interval} {value : ℝ}
    (member : interval.Contains (term.eval config values))
    (equal : term.eval config values = value) : interval.Contains value := by
  rwa [equal] at member

end Eval

theorem memRaw {limit : EndpointLimit} {raw : Raw} {x : ℝ}
    (success : BuildResult.isReady (ofRawWithin limit raw) = true)
    (member : raw.Contains x) :
    (BuildResult.getValue (ofRawWithin limit raw) success).Contains x := by
  have view := view_ofRawWithin_ready (BuildResult.eq_ready _ success)
  change (BuildResult.getValue (ofRawWithin limit raw) success).view.Contains x
  rw [view]
  exact (contains_normalize raw x).2 member

theorem lowerClosedInt {value : Int} {x : ℝ} (h : (value : ℝ) ≤ x) :
    (Lower.finite (.ofInt value) false).Contains x := by
  change (((value : Dyadic).toRat : Rat) : ℝ) ≤ x
  simpa using h

theorem lowerOpenInt {value : Int} {x : ℝ} (h : (value : ℝ) < x) :
    (Lower.finite (.ofInt value) true).Contains x := by
  change (((value : Dyadic).toRat : Rat) : ℝ) < x
  simpa using h

theorem upperClosedInt {value : Int} {x : ℝ} (h : x ≤ (value : ℝ)) :
    (Upper.finite (.ofInt value) false).Contains x := by
  change x ≤ (((value : Dyadic).toRat : Rat) : ℝ)
  simpa using h

theorem upperOpenInt {value : Int} {x : ℝ} (h : x < (value : ℝ)) :
    (Upper.finite (.ofInt value) true).Contains x := by
  change x < (((value : Dyadic).toRat : Rat) : ℝ)
  simpa using h

theorem lowerOfMem {interval : Hex.Interval} {x : ℝ} {lower : Lower}
    {upper : Upper} (shape : interval.view = .bounds lower upper)
    (member : interval.Contains x) : lower.Contains x := by
  change interval.view.Contains x at member
  rw [shape] at member
  exact member.1

theorem upperOfMem {interval : Hex.Interval} {x : ℝ} {lower : Lower}
    {upper : Upper} (shape : interval.view = .bounds lower upper)
    (member : interval.Contains x) : upper.Contains x := by
  change interval.view.Contains x at member
  rw [shape] at member
  exact member.2

theorem intCastLeDyadic {value : Int} {endpoint : Dyadic}
    (h : (value : Rat) ≤ endpoint.toRat) :
    (value : ℝ) ≤ toReal endpoint := by
  change (((value : Rat) : ℝ) ≤ (endpoint.toRat : ℝ))
  exact_mod_cast h

theorem intCastLtDyadic {value : Int} {endpoint : Dyadic}
    (h : (value : Rat) < endpoint.toRat) :
    (value : ℝ) < toReal endpoint := by
  change (((value : Rat) : ℝ) < (endpoint.toRat : ℝ))
  exact_mod_cast h

theorem dyadicLeIntCast {endpoint : Dyadic} {value : Int}
    (h : endpoint.toRat ≤ (value : Rat)) :
    toReal endpoint ≤ (value : ℝ) := by
  change ((endpoint.toRat : ℝ) ≤ ((value : Rat) : ℝ))
  exact_mod_cast h

theorem dyadicLtIntCast {endpoint : Dyadic} {value : Int}
    (h : endpoint.toRat < (value : Rat)) :
    toReal endpoint < (value : ℝ) := by
  change ((endpoint.toRat : ℝ) < ((value : Rat) : ℝ))
  exact_mod_cast h

theorem toRealEqIntCast {endpoint : Dyadic} {value : Int}
    (h : endpoint.toRat = (value : Rat)) :
    toReal endpoint = (value : ℝ) := by
  change ((endpoint.toRat : ℝ) = ((value : Rat) : ℝ))
  exact_mod_cast h

theorem lowerClosedFromClosed {endpoint : Dyadic} {value : Int} {x : ℝ}
    (order : (value : ℝ) ≤ toReal endpoint)
    (bound : (Lower.finite endpoint false).Contains x) : (value : ℝ) ≤ x :=
  order.trans bound

theorem lowerClosedFromOpen {endpoint : Dyadic} {value : Int} {x : ℝ}
    (order : (value : ℝ) ≤ toReal endpoint)
    (bound : (Lower.finite endpoint true).Contains x) : (value : ℝ) ≤ x :=
  order.trans bound.le

theorem lowerOpenFromClosed {endpoint : Dyadic} {value : Int} {x : ℝ}
    (order : (value : ℝ) < toReal endpoint)
    (bound : (Lower.finite endpoint false).Contains x) : (value : ℝ) < x :=
  order.trans_le bound

theorem lowerOpenFromOpen {endpoint : Dyadic} {value : Int} {x : ℝ}
    (order : (value : ℝ) ≤ toReal endpoint)
    (bound : (Lower.finite endpoint true).Contains x) : (value : ℝ) < x :=
  order.trans_lt bound

theorem upperClosedFromClosed {endpoint : Dyadic} {value : Int} {x : ℝ}
    (order : toReal endpoint ≤ (value : ℝ))
    (bound : (Upper.finite endpoint false).Contains x) : x ≤ (value : ℝ) :=
  bound.trans order

theorem upperClosedFromOpen {endpoint : Dyadic} {value : Int} {x : ℝ}
    (order : toReal endpoint ≤ (value : ℝ))
    (bound : (Upper.finite endpoint true).Contains x) : x ≤ (value : ℝ) :=
  bound.le.trans order

theorem upperOpenFromClosed {endpoint : Dyadic} {value : Int} {x : ℝ}
    (order : toReal endpoint < (value : ℝ))
    (bound : (Upper.finite endpoint false).Contains x) : x < (value : ℝ) :=
  bound.trans_lt order

theorem upperOpenFromOpen {endpoint : Dyadic} {value : Int} {x : ℝ}
    (order : toReal endpoint ≤ (value : ℝ))
    (bound : (Upper.finite endpoint true).Contains x) : x < (value : ℝ) :=
  bound.trans_le order

theorem equalityOfMem {interval : Hex.Interval} {endpoint : Dyadic}
    {value : Int} {x : ℝ}
    (shape : interval.view =
      .bounds (.finite endpoint false) (.finite endpoint false))
    (member : interval.Contains x)
    (endpointEq : toReal endpoint = (value : ℝ)) : x = (value : ℝ) := by
  have bounds := And.intro
    (lowerOfMem shape member) (upperOfMem shape member)
  exact (le_antisymm bounds.2 bounds.1).trans endpointEq

theorem castLowerLe {actual x : ℝ} {value : Int}
    (endpoint : actual = (value : ℝ)) :
    (actual ≤ x ↔ (value : ℝ) ≤ x) := by rw [endpoint]

theorem castLowerLt {actual x : ℝ} {value : Int}
    (endpoint : actual = (value : ℝ)) :
    (actual < x ↔ (value : ℝ) < x) := by rw [endpoint]

theorem castUpperLe {actual x : ℝ} {value : Int}
    (endpoint : actual = (value : ℝ)) :
    (x ≤ actual ↔ x ≤ (value : ℝ)) := by rw [endpoint]

theorem castUpperLt {actual x : ℝ} {value : Int}
    (endpoint : actual = (value : ℝ)) :
    (x < actual ↔ x < (value : ℝ)) := by rw [endpoint]

theorem castEquality {actual x : ℝ} {value : Int}
    (endpoint : actual = (value : ℝ)) :
    (x = actual ↔ x = (value : ℝ)) := by rw [endpoint]

theorem lowerOfEqRight {actual x : ℝ} (equality : x = actual) : actual ≤ x :=
  equality.ge

theorem upperOfEqRight {actual x : ℝ} (equality : x = actual) : x ≤ actual :=
  equality.le

theorem lowerOfEqLeft {actual x : ℝ} (equality : actual = x) : actual ≤ x :=
  equality.le

theorem upperOfEqLeft {actual x : ℝ} (equality : actual = x) : x ≤ actual :=
  equality.ge

/-! ## Supported plain-data quotation -/

namespace Quote

meta def dyadicExpr (value : Dyadic) : MetaM Expr := do
  let rational := value.toRat
  let base ← mkAppM ``Dyadic.ofInt #[mkIntLit rational.num]
  if rational.den = 1 then return base
  mkAppM ``HShiftRight.hShiftRight
    #[base, mkIntLit (Int.ofNat rational.den.log2)]

meta def lowerExpr : Lower → MetaM Expr
  | .unbounded => pure (mkConst ``Lower.unbounded)
  | .finite value strict => do
      mkAppM ``Lower.finite #[← dyadicExpr value, toExpr strict]

meta def upperExpr : Upper → MetaM Expr
  | .unbounded => pure (mkConst ``Upper.unbounded)
  | .finite value strict => do
      mkAppM ``Upper.finite #[← dyadicExpr value, toExpr strict]

meta def rawExpr : Raw → MetaM Expr
  | .empty => pure (mkConst ``Raw.empty)
  | .bounds lower upper => do
      mkAppM ``Raw.bounds #[← lowerExpr lower, ← upperExpr upper]

meta def endpointExpr (limit : EndpointLimit) : MetaM Expr :=
  mkAppM ``EndpointLimit.mk
    #[mkNatLit limit.maxEndpointHeight, mkNatLit limit.maxAlignmentShift]

meta def precisionLimitsExpr (limits : Arithmetic.PrecisionLimits) : MetaM Expr := do
  mkAppM ``Arithmetic.PrecisionLimits.mk
    #[← endpointExpr limits.endpoint, mkNatLit limits.maxPrecisionMagnitude,
      mkNatLit limits.maxPrecisionBits, mkNatLit limits.maxTemporaryBits]

meta def trueProof : MetaM Expr :=
  mkAppM ``Eq.refl #[mkConst ``Bool.true]

/-- Reconstruct a sealed canonical interval through its checked public raw
constructor. The caller supplies the same endpoint envelope used by replay. -/
meta def intervalExpr (limit : EndpointLimit) (interval : Hex.Interval) : MetaM Expr := do
  let raw ← rawExpr interval.view
  let build ← mkAppM ``ofRawWithin #[← endpointExpr limit, raw]
  let proof ← trueProof
  let encoded ← mkAppM ``BuildResult.getValue #[build, proof]
  match ofRawWithin limit interval.view with
  | .ready rebuilt =>
      unless rebuilt == interval do
        throwError "interval quotation changed a canonical interval"
      pure encoded
  | .resourceLimit _ =>
      throwError "interval quotation exceeded the endpoint envelope"

meta def listExpr (type : Expr) (items : List Expr) : MetaM Expr := do
  let nil := mkApp (mkConst ``List.nil [.zero]) type
  return items.foldr (fun item tail =>
    mkAppN (mkConst ``List.cons [.zero]) #[type, item, tail]) nil

meta def arrayExpr (type : Expr) (items : List Expr) : MetaM Expr := do
  mkAppM ``Array.mk #[← listExpr type items]

meta def proofLimitsExpr (limits : Proof.Limits) : MetaM Expr := do
  mkAppM ``Proof.Limits.mk
    #[mkNatLit limits.maxPackages, mkNatLit limits.maxSchemas,
      mkNatLit limits.maxBodyCells, mkNatLit limits.maxDependencies,
      mkNatLit limits.maxChronology]

meta def reifyLimitsExpr (limits : Frontend.Limits) : MetaM Expr := do
  mkAppM ``Frontend.Limits.mk
    #[mkNatLit limits.maxSources, mkNatLit limits.maxOperations,
      mkNatLit limits.maxNodes, mkNatLit limits.maxDepth]

meta def frontendConfigExpr (config : Frontend.Config) : MetaM Expr := do
  mkAppM ``Frontend.Config.mk
    #[← Rule.Runtime.Quote.configExpr config.rule,
      ← reifyLimitsExpr config.reify, ← proofLimitsExpr config.proof]

meta def termExpr : Frontend.Term → MetaM Expr
  | .source index => mkAppM ``Frontend.Term.source #[mkNatLit index]
  | .constant => pure (mkConst ``Frontend.Term.constant)
  | .neg input => do mkAppM ``Frontend.Term.neg #[← termExpr input]
  | .add left right => do
      mkAppM ``Frontend.Term.add #[← termExpr left, ← termExpr right]
  | .sub left right => do
      mkAppM ``Frontend.Term.sub #[← termExpr left, ← termExpr right]
  | .mul left right => do
      mkAppM ``Frontend.Term.mul #[← termExpr left, ← termExpr right]
  | .pow input => do mkAppM ``Frontend.Term.pow #[← termExpr input]
  | .abs input => do mkAppM ``Frontend.Term.abs #[← termExpr input]
  | .min left right => do
      mkAppM ``Frontend.Term.min #[← termExpr left, ← termExpr right]
  | .max left right => do
      mkAppM ``Frontend.Term.max #[← termExpr left, ← termExpr right]
  | .inv input => do mkAppM ``Frontend.Term.inv #[← termExpr input]
  | .div left right => do
      mkAppM ``Frontend.Term.div #[← termExpr left, ← termExpr right]
  | .regularize input => do mkAppM ``Frontend.Term.regularize #[← termExpr input]

meta def resultExpr (config : Frontend.Config) (sourceCount : Nat)
    (term : Frontend.Term) : MetaM Expr := do
  let checked ← mkAppM ``Frontend.reifyWithin
    #[← frontendConfigExpr config, mkNatLit sourceCount, ← termExpr term]
  let option ← mkAppM ``Except.toOption #[checked]
  let ready ← mkAppM ``Option.isSome #[option]
  let success ← mkDecideProof (← mkAppM ``Eq #[ready, toExpr true])
  let result ← mkAppM ``checkedResult #[checked, success]
  mkAppM ``Frontend.Result.mk
    #[← mkAppM ``Frontend.Result.program #[result],
      ← mkAppM ``Frontend.Result.target #[result], ← termExpr term,
      ← mkAppM ``Frontend.Result.entries #[result],
      ← mkAppM ``Frontend.Result.sourceCount #[result]]

end Quote

/-! ## Recursive bound derivation -/

meta def defaultConfig : Frontend.Config :=
  { rule :=
      { endpoint := { maxEndpointHeight := 256, maxAlignmentShift := 256 }
        powerWork := { maxExponent := 64 }
        exponent := 2
        precisionLimits :=
          { endpoint := { maxEndpointHeight := 256, maxAlignmentShift := 256 }
            maxPrecisionMagnitude := 64, maxPrecisionBits := 64
            maxTemporaryBits := 512 }
        -- The default working grid is `2⁻¹⁶`; integer-grid regularization loses
        -- elementary reciprocal facts such as `2⁻¹ + 2⁻¹ = 1`.
        precision := 16
        constant := 0 }
    reify := { maxSources := 32, maxOperations := 13, maxNodes := 256, maxDepth := 32 }
    proof :=
      { maxPackages := 1, maxSchemas := 12, maxBodyCells := 1
        maxDependencies := 2, maxChronology := 256 } }

structure RuntimeLimits where
  executable : Executable.Limits
  runtime : Runtime.Limits
  search : Search.Limits
  result : Search.Result.Limits
  envelope : Search.Envelope
  controller : Runtime.Controller.Limits
  adapter : RuntimeProof.Limits
  emit : RuntimeEmit.Limits

meta def runtimeLimits (config : Frontend.Config) : RuntimeLimits :=
  let chronology := config.proof.maxChronology
  let nodes := config.reify.maxNodes
  let structural := 64 + 8 * nodes + 16 * chronology
  let state : State.Limits :=
    { maxOperations := config.reify.maxOperations, maxNodes := nodes,
      maxRules := 12, maxRegistryEntries := nodes + 32, maxReplayFormats := 12,
      maxArity := 2, maxScopeNodes := 0, maxApplications := nodes,
      maxQueueEntries := nodes, maxActions := chronology,
      maxMatcherVisits := 0, matcherBatchSize := 0,
      maxAcceptedFacts := chronology, maxRetainedSuggestions := 0, maxEffort := 0,
      maxObservationValue := nodes, maxDiagnosticValue := nodes,
      maxOutcomeCandidates := 1, maxOutcomeSuggestions := 0,
      maxProposalItems := 1, maxInstances := 0, maxGeneration := 0,
      maxNodeDepth := config.reify.maxDepth, maxEqualities := 0,
      splitEndpointLimit := config.rule.endpoint }
  let executable : Executable.Limits :=
    { state, maxPackages := 1, maxMetadataBytes := 64, maxMetadataWork := 64,
      maxCacheBytes := chronology, maxCacheWork := chronology,
      maxResultBytes := 1, maxResultWork := 1, maxQuotes := 1,
      maxQuoteCells := 1, maxAtom := 12, maxSchema := 1 }
  let runtime : Runtime.Limits := { executable, maxEvents := 1 }
  let search : Search.Limits :=
    { maxSteps := chronology + 1, maxSplits := 0, maxLeaves := 1, maxFrontier := 1,
      maxDepth := 0, maxScopes := 1, leafFuel := chronology + 1 }
  let result : Search.Result.Limits :=
    { search, runtime, maxNodes := 1, maxBodyCells := chronology,
      maxBytes := structural, maxWork := structural, maxCode := 16 }
  let policy : Policy.Limits :=
    { maxOffers := nodes, maxBytes := structural,
      maxPairs := nodes * nodes, maxWork := structural, maxScore := 0 }
  let trace : Trace.Limit :=
    { maxEvents := 0, maxBytes := 0, maxWork := 0, maxCode := 16 }
  let envelope : Search.Envelope := { state, policy, trace, search }
  let controller : Runtime.Controller.Limits := { maxChoices := chronology, result }
  let tree : Proof.TreeLimits :=
    { maxNodes := 1, maxDepth := 0, maxBodyCells := chronology,
      maxWork := structural }
  let adapter : RuntimeProof.Limits :=
    { result := result, proof := config.proof, tree := tree,
      maxTransitions := chronology, maxEvents := chronology,
      maxStructuralCells := structural }
  let emit : RuntimeEmit.Limits :=
    { proof := config.proof, maxSchemas := 12, maxChronology := chronology,
      maxExpressionCells := structural * 1024 }
  { executable, runtime, search, result, envelope, controller, adapter, emit }

meta def runtimeMeasure : Search.Result.Measure Hex.Interval Rule.Runtime.Cause
    (List Nat) Proof.Key :=
  let unit : Search.Result.Cost := { bytes := 1, work := 1 }
  { node := unit
    branch := fun branch =>
      { bytes := branch.program.nodes.size + branch.history.size,
        work := branch.program.nodes.size + branch.history.size }
    fact := fun _ => unit, action := fun _ => unit, plan := fun _ => unit,
    schema := fun _ => unit, body := fun _ => unit, code := fun _ => unit }

meta def runtimePolicy : Policy.Interface Hex.Interval (List Nat) ApplicationId RuleKey :=
  { choose := fun plan view => match plan with
    | [] => .stop []
    | wanted :: rest => match view.offers.find? fun offer => offer.id.index == wanted with
      | none => .stop plan
      | some offer => .select offer rest }

structure ParseState where
  sources : Array Expr := #[]
  terms : Array (Frontend.Term × Expr) := #[]

meta def ParseState.source (state : ParseState) (expression : Expr) : Nat × ParseState :=
  match state.sources.toList.findIdx? (· == expression) with
  | some index => (index, state)
  | none => (state.sources.size, { state with sources := state.sources.push expression })

meta def ParseState.record (state : ParseState) (term : Frontend.Term)
    (expression : Expr) : ParseState :=
  if state.terms.toList.any fun entry => entry.1 == term then state
  else { state with terms := state.terms.push (term, expression) }

/-- Retain both the exact arithmetic row and the package-configured outward
regularization row denoting the same real expression. Consequently every
computed arithmetic layer consumes two frontend term-depth levels. -/
meta def ParseState.computed (state : ParseState) (term : Frontend.Term)
    (expression : Expr) : Frontend.Term × ParseState :=
  let state := state.record term expression
  let result := .regularize term
  (result, state.record result expression)

meta def ParseState.expression? (state : ParseState) (term : Frontend.Term) : Option Expr :=
  (state.terms.toList.find? fun entry => entry.1 == term).map (·.2)

/-- Recognize only a literal natural or the numeral payload of `OfNat.ofNat`.
In particular, do not scan arbitrary application arguments: scientific decimal
syntax carries unrelated natural fields and is not an integer cut. -/
meta def natLiteral? (expression : Expr) : Option Nat :=
  match expression with
  | .lit (.natVal value) => some value
  | _ =>
      if expression.getAppFn.constName? != some ``OfNat.ofNat then none else
      let arguments := expression.getAppArgs
      if h : 2 ≤ arguments.size then
        match arguments[arguments.size - 2] with
        | .lit (.natVal value) => some value
        | _ => none
      else none

meta def intLiteral? (expression : Expr) : Option Int :=
  if expression.getAppFn.constName? == some ``Neg.neg then
    let arguments := expression.getAppArgs
    if let some argument := arguments.back? then
      (natLiteral? argument).map fun value => -(Int.ofNat value)
    else none
  else
    (natLiteral? expression).map Int.ofNat

meta def binaryArguments? (expression : Expr) (name : Name) : Option (Expr × Expr) := do
  if expression.getAppFn.constName? != some name then none else
  let arguments := expression.getAppArgs
  if arguments.size < 2 then none else
  some (arguments[arguments.size - 2]!, arguments[arguments.size - 1]!)

meta def unaryArgument? (expression : Expr) (name : Name) : Option Expr := do
  if expression.getAppFn.constName? != some name then none else
  expression.getAppArgs.back?

meta def ensureReal (expression : Expr) : MetaM Unit := do
  let type ← inferType expression
  unless ← isDefEq type (mkConst ``Real) do
    throwError "interval: expected a real expression, got {type}"

meta def parseTermAux (config : Frontend.Config) (expression : Expr)
    (state : ParseState) : Nat → MetaM (Frontend.Term × ParseState)
  | 0 => throwError "interval: expression exceeded the reification depth limit"
  | fuel + 1 => do
    ensureReal expression
    if let some value := intLiteral? expression then
      if Dyadic.ofInt value == config.rule.constant then
        return state.computed .constant expression
      else
        throwError "interval: this real literal is not the configured constant"
    if let some input := unaryArgument? expression ``Neg.neg then
      let (term, state) ← parseTermAux config input state fuel
      let result := .neg term
      return state.computed result expression
    if let some (left, right) := binaryArguments? expression ``HAdd.hAdd then
      let (leftTerm, state) ← parseTermAux config left state fuel
      let (rightTerm, state) ← parseTermAux config right state fuel
      let result := .add leftTerm rightTerm
      return state.computed result expression
    if let some (left, right) := binaryArguments? expression ``HSub.hSub then
      let (leftTerm, state) ← parseTermAux config left state fuel
      let (rightTerm, state) ← parseTermAux config right state fuel
      let result := .sub leftTerm rightTerm
      return state.computed result expression
    if let some (left, right) := binaryArguments? expression ``HMul.hMul then
      let (leftTerm, state) ← parseTermAux config left state fuel
      let (rightTerm, state) ← parseTermAux config right state fuel
      let result := .mul leftTerm rightTerm
      return state.computed result expression
    if let some (left, right) := binaryArguments? expression ``HDiv.hDiv then
      let (leftTerm, state) ← parseTermAux config left state fuel
      let (rightTerm, state) ← parseTermAux config right state fuel
      let result := .div leftTerm rightTerm
      return state.computed result expression
    if let some input := unaryArgument? expression ``Inv.inv then
      let (term, state) ← parseTermAux config input state fuel
      let result := .inv term
      return state.computed result expression
    if let some (input, exponent) := binaryArguments? expression ``HPow.hPow then
      let some value := natLiteral? exponent
        | throwError "interval: power exponent is not a natural literal"
      unless value == config.rule.exponent do
        throwError "interval: expected configured power {config.rule.exponent}, got {value}"
      let (term, state) ← parseTermAux config input state fuel
      let result := .pow term
      return state.computed result expression
    if let some input := unaryArgument? expression ``abs then
      let (term, state) ← parseTermAux config input state fuel
      let result := .abs term
      return state.computed result expression
    if let some (left, right) := binaryArguments? expression ``min then
      let (leftTerm, state) ← parseTermAux config left state fuel
      let (rightTerm, state) ← parseTermAux config right state fuel
      let result := .min leftTerm rightTerm
      return state.computed result expression
    if let some (left, right) := binaryArguments? expression ``max then
      let (leftTerm, state) ← parseTermAux config left state fuel
      let (rightTerm, state) ← parseTermAux config right state fuel
      let result := .max leftTerm rightTerm
      return state.computed result expression
    if expression.isFVar then
      let (index, state) := state.source expression
      let result := .source index
      return (result, state.record result expression)
    throwError "interval: unsupported real expression {expression}"

meta def parseTerm (config : Frontend.Config) (expression : Expr)
    (state : ParseState := {}) : MetaM (Frontend.Term × ParseState) :=
  parseTermAux config expression state (config.reify.maxDepth + 1)

structure Cut where
  value : Int
  endpoint : Expr
  strict : Bool
  proof : Expr

structure SourceCuts where
  lower : Option Cut := none
  upper : Option Cut := none

meta def strongerLower (current : Option Cut) (candidate : Cut) : Option Cut :=
  match current with
  | none => some candidate
  | some old =>
      if old.value < candidate.value ||
          (old.value = candidate.value && !old.strict && candidate.strict) then
        some candidate
      else current

meta def strongerUpper (current : Option Cut) (candidate : Cut) : Option Cut :=
  match current with
  | none => some candidate
  | some old =>
      if candidate.value < old.value ||
          (old.value = candidate.value && !old.strict && candidate.strict) then
        some candidate
      else current

meta def collectCuts (source : Expr) : MetaM SourceCuts := do
  let context ← getLCtx
  let mut cuts : SourceCuts := {}
  for declaration in context do
    unless declaration.isImplementationDetail do
      let proposition ← instantiateMVars declaration.type
      let proof := mkFVar declaration.fvarId
      let strict := proposition.getAppFn.constName? == some ``LT.lt
      if strict || proposition.getAppFn.constName? == some ``LE.le then
        let arguments := proposition.getAppArgs
        if arguments.size ≥ 2 then
          let left := arguments[arguments.size - 2]!
          let right := arguments[arguments.size - 1]!
          if right == source then
            if let some value := intLiteral? left then
              let candidate : Cut := ⟨value, left, strict, proof⟩
              cuts := { cuts with lower := strongerLower cuts.lower candidate }
          else if left == source then
            if let some value := intLiteral? right then
              let candidate : Cut := ⟨value, right, strict, proof⟩
              cuts := { cuts with upper := strongerUpper cuts.upper candidate }
      else if proposition.getAppFn.constName? == some ``Eq then
        let arguments := proposition.getAppArgs
        if arguments.size ≥ 2 then
          let left := arguments[arguments.size - 2]!
          let right := arguments[arguments.size - 1]!
          if left == source then
            if let some value := intLiteral? right then
              let lowerProof ← mkAppM ``lowerOfEqRight #[proof]
              let upperProof ← mkAppM ``upperOfEqRight #[proof]
              cuts := { cuts with
                lower := strongerLower cuts.lower ⟨value, right, false, lowerProof⟩
                upper := strongerUpper cuts.upper ⟨value, right, false, upperProof⟩ }
          else if right == source then
            if let some value := intLiteral? left then
              let lowerProof ← mkAppM ``lowerOfEqLeft #[proof]
              let upperProof ← mkAppM ``upperOfEqLeft #[proof]
              cuts := { cuts with
                lower := strongerLower cuts.lower ⟨value, left, false, lowerProof⟩
                upper := strongerUpper cuts.upper ⟨value, left, false, upperProof⟩ }
  pure cuts

structure Bound where
  expression : Expr
  interval : Hex.Interval
  intervalExpr : Expr
  proof : Expr
  reified : Frontend.Result
  chronology : Nat

meta def rawOfCuts (cuts : SourceCuts) : Raw :=
  .bounds
    ((cuts.lower.map (fun cut => Lower.finite (.ofInt cut.value) cut.strict)).getD
      Lower.unbounded)
    ((cuts.upper.map (fun cut => Upper.finite (.ofInt cut.value) cut.strict)).getD
      Upper.unbounded)

meta def realIntCast (value : Int) : MetaM Expr :=
  mkAppOptM ``Int.cast
    #[some (mkConst ``Real), none, some (mkIntLit value)]

meta def normNumProof (proposition : Expr) : MetaM Expr := do
  let result ← Mathlib.Meta.NormNum.eval proposition
  unless result.expr.isConstOf ``True do
    throwError "interval: failed to normalize an integer endpoint"
  let proof ← mkOfEqTrue (← result.getProof)
  let emitter : Proof.Emitter Expr := { emit := pure }
  Proof.emitChecked emitter proof proposition

meta def endpointProof (endpoint : Expr) (value : Int) : MetaM Expr := do
  let proposition ← mkAppM ``Eq #[endpoint, ← realIntCast value]
  normNumProof proposition

meta def convertSourceCut (expression : Expr) (cut : Cut) (lower : Bool) : MetaM Expr := do
  let endpoint ← endpointProof cut.endpoint cut.value
  let theoremName := match lower, cut.strict with
    | true, false => ``castLowerLe
    | true, true => ``castLowerLt
    | false, false => ``castUpperLe
    | false, true => ``castUpperLt
  let equivalence ← mkAppOptM theoremName
    #[some cut.endpoint, some expression, some (mkIntLit cut.value), some endpoint]
  mkAppM ``Iff.mp #[equivalence, cut.proof]

meta def sourceProof (config : Frontend.Config) (expression : Expr)
    (cuts : SourceCuts) : MetaM (Hex.Interval × Expr × Expr) := do
  let raw := rawOfCuts cuts
  let build := ofRawWithin config.rule.endpoint raw
  let .ready interval := build
    | throwError "interval: source cut exceeded the endpoint resource envelope"
  let endpoint ← Quote.endpointExpr config.rule.endpoint
  let rawTerm ← Quote.rawExpr raw
  let buildTerm ← mkAppM ``ofRawWithin #[endpoint, rawTerm]
  let success ← Quote.trueProof
  let intervalTerm ← mkAppM ``BuildResult.getValue #[buildTerm, success]
  let lowerProof ← match cuts.lower with
    | none => pure (mkConst ``True.intro)
    | some cut =>
        let cutProof ← convertSourceCut expression cut true
        mkAppOptM (if cut.strict then ``lowerOpenInt else ``lowerClosedInt)
          #[some (mkIntLit cut.value), some expression, some cutProof]
  let upperProof ← match cuts.upper with
    | none => pure (mkConst ``True.intro)
    | some cut =>
        let cutProof ← convertSourceCut expression cut false
        mkAppOptM (if cut.strict then ``upperOpenInt else ``upperClosedInt)
          #[some (mkIntLit cut.value), some expression, some cutProof]
  let member ← mkAppM ``And.intro #[lowerProof, upperProof]
  let proof ← mkAppOptM ``memRaw
    #[some endpoint, some rawTerm, some expression, some success, some member]
  let expected ← mkAppM ``Hex.Interval.Contains #[intervalTerm, expression]
  let emitter : Proof.Emitter Expr := { emit := pure }
  let proof ← Proof.emitChecked emitter proof expected
  pure (interval, intervalTerm, proof)

meta def evalProof (config : Frontend.Config) (parsed : ParseState)
    (term : Frontend.Term) : MetaM Expr := do
  let some expression := parsed.expression? term
    | throwError "interval: reified term has no Lean expression"
  let valuesList ← Quote.listExpr (mkConst ``Real) parsed.sources.toList
  let values ← mkAppM ``Frontend.valuesAt #[valuesList]
  let ruleConfig ← Rule.Runtime.Quote.configExpr config.rule
  let quotedTerm ← Quote.termExpr term
  let evaluated ← mkAppM ``Frontend.Term.eval #[ruleConfig, values, quotedTerm]
  let expected ← mkAppM ``Eq #[evaluated, expression]
  let candidate ← match term with
    | .source index => do
        let some source := parsed.sources[index]?
          | throwError "interval: source evaluation escaped the source table"
        let lookup := mkApp values (mkNatLit index)
        let lookupExpected ← mkAppM ``Eq #[lookup, source]
        let reflexive ← mkAppM ``Eq.refl #[source]
        let emitter : Proof.Emitter Expr := { emit := pure }
        let lookupProof ← Proof.emitChecked emitter reflexive lookupExpected
        mkAppOptM ``Eval.source
          #[some ruleConfig, some values, some (mkNatLit index), some source,
            some lookupProof]
    | .constant => do
        let some value := intLiteral? expression
          | throwError "interval: configured constant is not an integer literal"
        let quotedConstant ← Rule.Runtime.Quote.dyadicExpr config.rule.constant
        let rationalEq ← mkDecideProof (← mkAppM ``Eq
          #[toExpr config.rule.constant.toRat, toExpr (value : Rat)])
        let castEqual ← mkAppOptM ``toRealEqIntCast
          #[some quotedConstant, some (mkIntLit value), some rationalEq]
        let realCast ← realIntCast value
        let literalEqual ← normNumProof (← mkAppM ``Eq #[realCast, expression])
        let equal ← mkAppM ``Eq.trans #[castEqual, literalEqual]
        mkAppOptM ``Eval.constantMk
          #[some (← Rule.Runtime.Quote.endpointExpr config.rule.endpoint),
            some (← Rule.Runtime.Quote.powLimitsExpr config.rule.powerWork),
            some (mkNatLit config.rule.exponent),
            some (← Rule.Runtime.Quote.precisionLimitsExpr config.rule.precisionLimits),
            some (mkIntLit config.rule.precision), some quotedConstant,
            some (← Rule.Runtime.Quote.emptyMeaningsExpr), some values, some expression,
            some equal]
    | .neg input => do
        let some inputValue := parsed.expression? input
          | throwError "interval: negated term has no Lean expression"
        mkAppOptM ``Eval.neg
          #[some ruleConfig, some values, some (← Quote.termExpr input),
            some inputValue, some (← evalProof config parsed input)]
    | .add left right => do
        let some leftValue := parsed.expression? left
          | throwError "interval: left addend has no Lean expression"
        let some rightValue := parsed.expression? right
          | throwError "interval: right addend has no Lean expression"
        mkAppOptM ``Eval.add
          #[some ruleConfig, some values, some (← Quote.termExpr left),
            some (← Quote.termExpr right), some leftValue, some rightValue,
            some (← evalProof config parsed left), some (← evalProof config parsed right)]
    | .sub left right => do
        let some leftValue := parsed.expression? left
          | throwError "interval: minuend has no Lean expression"
        let some rightValue := parsed.expression? right
          | throwError "interval: subtrahend has no Lean expression"
        mkAppOptM ``Eval.sub
          #[some ruleConfig, some values, some (← Quote.termExpr left),
            some (← Quote.termExpr right), some leftValue, some rightValue,
            some (← evalProof config parsed left), some (← evalProof config parsed right)]
    | .mul left right => do
        let some leftValue := parsed.expression? left
          | throwError "interval: left factor has no Lean expression"
        let some rightValue := parsed.expression? right
          | throwError "interval: right factor has no Lean expression"
        mkAppOptM ``Eval.mul
          #[some ruleConfig, some values, some (← Quote.termExpr left),
            some (← Quote.termExpr right), some leftValue, some rightValue,
            some (← evalProof config parsed left), some (← evalProof config parsed right)]
    | .pow input => do
        let some inputValue := parsed.expression? input
          | throwError "interval: powered term has no Lean expression"
        mkAppOptM ``Eval.pow
          #[some ruleConfig, some values, some (← Quote.termExpr input),
            some inputValue, some (← evalProof config parsed input)]
    | .abs input => do
        let some inputValue := parsed.expression? input
          | throwError "interval: absolute-value term has no Lean expression"
        mkAppOptM ``Eval.abs
          #[some ruleConfig, some values, some (← Quote.termExpr input),
            some inputValue, some (← evalProof config parsed input)]
    | .min left right => do
        let some leftValue := parsed.expression? left
          | throwError "interval: left minimum input has no Lean expression"
        let some rightValue := parsed.expression? right
          | throwError "interval: right minimum input has no Lean expression"
        mkAppOptM ``Eval.min
          #[some ruleConfig, some values, some (← Quote.termExpr left),
            some (← Quote.termExpr right), some leftValue, some rightValue,
            some (← evalProof config parsed left), some (← evalProof config parsed right)]
    | .max left right => do
        let some leftValue := parsed.expression? left
          | throwError "interval: left maximum input has no Lean expression"
        let some rightValue := parsed.expression? right
          | throwError "interval: right maximum input has no Lean expression"
        mkAppOptM ``Eval.max
          #[some ruleConfig, some values, some (← Quote.termExpr left),
            some (← Quote.termExpr right), some leftValue, some rightValue,
            some (← evalProof config parsed left), some (← evalProof config parsed right)]
    | .inv input => do
        let some inputValue := parsed.expression? input
          | throwError "interval: reciprocal term has no Lean expression"
        mkAppOptM ``Eval.inv
          #[some ruleConfig, some values, some (← Quote.termExpr input),
            some inputValue, some (← evalProof config parsed input)]
    | .div left right => do
        let some leftValue := parsed.expression? left
          | throwError "interval: dividend has no Lean expression"
        let some rightValue := parsed.expression? right
          | throwError "interval: divisor has no Lean expression"
        mkAppOptM ``Eval.div
          #[some ruleConfig, some values, some (← Quote.termExpr left),
            some (← Quote.termExpr right), some leftValue, some rightValue,
            some (← evalProof config parsed left), some (← evalProof config parsed right)]
    | .regularize input => do
        let some inputValue := parsed.expression? input
          | throwError "interval: regularized term has no Lean expression"
        mkAppOptM ``Eval.regularize
          #[some ruleConfig, some values, some (← Quote.termExpr input),
            some inputValue, some (← evalProof config parsed input)]
  let emitter : Proof.Emitter Expr := { emit := pure }
  Proof.emitChecked emitter candidate expected

meta def runtimeKey : RuntimeProof.Key := { name := "interval-tactic", version := 1 }

meta def checkedValue (checked : Expr) : MetaM (Expr × Expr) := do
  let option ← mkAppM ``Except.toOption #[checked]
  let ready ← mkAppM ``Option.isSome #[option]
  let success ← mkDecideProof (← mkAppM ``Eq #[ready, toExpr true])
  pure (option, success)

structure RuntimeResult (config : Rule.Config) where
  checked : RuntimeEmit.Checked Hex.Interval (Rule.semantics config)
    Rule.Runtime.Cause (List Nat)
  output : Hex.Interval
  chronology : Nat

private meta def liftRuntimeExcept {ε α : Type} : Except ε α → Except ε (ULift.{1, 0} α)
  | .error error => .error error
  | .ok value => .ok ⟨value⟩

/-- Resolve the first policy-pending application through the exact sealed
runtime registry. Handler applicability is only a Boolean in the executable
contract, so its discarded package-specific cost cannot be reconstructed here
without running the arithmetic proposal a second time. -/
private meta def pendingRule?
    {ruleConfig : Rule.Config} (registry : Rule.Runtime.EmitRegistry ruleConfig)
    (remaining : List Nat) :
    Option RuleKey := do
  let index ← remaining.head?
  let application ← registry.runtime.assembly.applications[index]?
  let registration ←
    registry.runtime.assembly.registry.registrations[application.rule.index]?
  pure registration.key

private meta def stoppedMessage
    {ruleConfig : Rule.Config} (registry : Rule.Runtime.EmitRegistry ruleConfig) (live : Nat)
    (remaining : List Nat) : String :=
  let residual := if live == 1 then "1 live offer remains" else s!"{live} live offers remain"
  match pendingRule? registry remaining with
  | some rule =>
      s!"rule {rule.name} declined its application under the configured resource envelope; " ++
        residual
  | none =>
      s!"controller stopped with {live} live offers and {remaining.length} pending actions"

/-! Execute and settle the exact typed runtime chronology. Keeping this phase
in `Except` permits its sealed `Type 1` handles to remain outside `MetaM`. -/
meta def prepareRuntime (config : Frontend.Config) (reified : Frontend.Result)
    (sourceFacts : Array Hex.Interval) : Except String (RuntimeResult config.rule) := do
  let limits := runtimeLimits config
  let registry ← Rule.Runtime.buildEmitWithin limits.executable limits.emit runtimeKey
      config.rule reified.program |>.mapError fun error =>
        s!"runtime registry failed: {repr error}"
  let facts := reified.facts sourceFacts
  let branch := (← liftRuntimeExcept <|
    (State.Branch.startWithin limits.executable.state reified.program facts
      |>.mapError fun error => s!"runtime branch failed: {repr error}")).down
  let runtime ← Runtime.State.startWithin limits.runtime registry.runtime.assembly branch
    |>.mapError fun error => s!"runtime start failed: {repr error}"
  let scope : Policy.ScopeId := { index := 0 }
  let tree := (← liftRuntimeExcept <|
    (Search.Result.startWithin limits.result runtimeMeasure scope branch
      |>.mapError fun error => s!"retained tree start failed: {repr error}")).down
  let initialController ← Runtime.Controller.State.startWithin limits.controller
      limits.envelope runtimeMeasure runtime tree
    |>.mapError fun error => s!"controller start failed: {repr error}"
  let plan := List.range registry.runtime.assembly.applications.size
  let controller ← match Runtime.Controller.runWithin limits.controller limits.envelope
      runtimeMeasure runtimePolicy plan initialController with
    | .ok (.stopped 0 controller []) => pure controller
    | .ok (.stopped live _ remaining) => throw (stoppedMessage registry live remaining)
    | .error error => throw s!"controller run failed: {repr error}"
  let some version := controller.runtime.branch.versions[reified.target.index]?
    | throw "target version escaped the runtime branch"
  let seen : SeenVersion := { node := reified.target, version }
  let some outputInterval := controller.runtime.branch.factAt? seen
    | throw "target fact escaped the runtime branch"
  let input := (← liftRuntimeExcept <|
    (Frontend.inputWithin config scope reified sourceFacts outputInterval
      |>.mapError fun error => s!"input construction failed: {repr error}")).down
  let active ← RuntimeEmit.Active.startWithin registry input controller
    |>.mapError fun error => s!"emitter start failed: {repr error}"
  let lineage ← RuntimeEmit.Active.targetWithin limits.result runtimeMeasure active seen
    |>.mapError fun error => s!"target settlement failed: {repr error}"
  let checked ← RuntimeEmit.Lineage.quoteWithin limits.adapter runtimeMeasure lineage
    |>.mapError fun error => s!"retained quotation failed: {repr error}"
  pure { checked, output := outputInterval, chronology := plan.length }

/-! Emit the checked runtime result and close its exact quoted input against
the caller's source proofs. -/
meta def emitBoundWith (config : Frontend.Config) (expression : Expr)
    (term : Frontend.Term) (parsed : ParseState) (reified : Frontend.Result)
    (sourceIntervals sourceProofs : Array Expr) (runtime : RuntimeResult config.rule) :
    MetaM Bound := do
  let limits := runtimeLimits config
  let emitted : RuntimeEmit.Emitted ←
    match ← RuntimeEmit.Checked.emitResultWithin limits.emit runtime.checked with
    | .ok emitted => pure emitted
    | .error error => throwError "interval: proof emission failed: {repr error}"

  let configExpr ← Quote.frontendConfigExpr config
  let resultExpr ← Quote.resultExpr config parsed.sources.size term
  let valuesListExpr ← Quote.listExpr (mkConst ``Real) parsed.sources.toList
  let valuesExpr ← mkAppM ``Frontend.valuesAt #[valuesListExpr]
  let sourceFactsExpr ← Quote.arrayExpr (mkConst ``Hex.Interval) sourceIntervals.toList
  let modelCheck ← mkAppM ``Frontend.modelWithin #[configExpr, valuesExpr, resultExpr]
  let (_, modelSuccess) ← checkedValue modelCheck
  let model ← mkAppM ``Frontend.modelOfCheck #[modelCheck, modelSuccess]
  let inputProgram ← mkAppM ``Proof.Input.program #[emitted.input]
  let resultProgram ← mkAppM ``Frontend.Result.program #[resultExpr]
  let programEq ← mkDecideProof (← mkAppM ``Eq #[inputProgram, resultProgram])
  let inputTarget ← mkAppM ``Proof.Input.target #[emitted.input]
  let inputTargetNode ← mkAppM ``Proof.NodeFact.node #[inputTarget]
  let resultTarget ← mkAppM ``Frontend.Result.target #[resultExpr]
  let targetEq ← mkDecideProof (← mkAppM ``Eq #[inputTargetNode, resultTarget])
  let sourceSizeExpr ← mkAppM ``Array.size #[sourceFactsExpr]
  let resultSourceCount ← mkAppM ``Frontend.Result.sourceCount #[resultExpr]
  let sourceSize ← mkDecideProof (← mkAppM ``Eq #[sourceSizeExpr, resultSourceCount])
  let inputFacts ← mkAppM ``Proof.Input.facts #[emitted.input]
  let resultFacts ← mkAppM ``Frontend.Result.facts #[resultExpr, sourceFactsExpr]
  let factsEq ← mkDecideProof (← mkAppM ``Eq #[inputFacts, resultFacts])
  let mut holds := mkConst ``Sources.nil
  for proof in sourceProofs.toList.reverse do
    holds ← mkAppM ``Sources.cons #[proof, holds]
  let sourceHolds ← mkAppM ``Frontend.SourcesContain.ofForall₂ #[holds]
  let candidate ← mkAppM ``Frontend.closeSources
    #[configExpr, resultExpr, valuesExpr, model, emitted.input, emitted.evidence,
      programEq, targetEq, sourceFactsExpr, sourceSize, factsEq, sourceHolds]
  let candidate ← mkAppM ``Eval.contains #[candidate, ← evalProof config parsed term]
  let canonicalExpr ← Quote.intervalExpr config.rule.endpoint runtime.output
  let canonicalExpected ← mkAppM ``Hex.Interval.Contains #[canonicalExpr, expression]
  let emitter : Proof.Emitter Expr := { emit := pure }
  let canonicalProof ← Proof.emitChecked emitter candidate canonicalExpected
  pure
    { expression, interval := runtime.output, intervalExpr := canonicalExpr
      proof := canonicalProof, reified, chronology := runtime.chronology }

meta def deriveBound (config : Frontend.Config) (expression : Expr) : MetaM Bound := do
  let expression ← instantiateMVars expression
  let (term, parsed) ← parseTerm config expression
  let reified ←
    match Frontend.reifyWithin config parsed.sources.size term with
    | .ok result => pure result
    | .error error => throwError "interval: reification failed: {repr error}"
  let mut sourceFacts : Array Hex.Interval := #[]
  let mut sourceIntervals : Array Expr := #[]
  let mut sourceProofs : Array Expr := #[]
  for index in [0:parsed.sources.size] do
    let some source := parsed.sources[index]?
      | throwError "interval: source index escaped the parsed source table"
    let some _ := reified.sourceNode? index
      | throwError "interval: selected source is absent from the target graph"
    let cuts ← collectCuts source
    let (interval, intervalExpr, proof) ← sourceProof config source cuts
    sourceFacts := sourceFacts.push interval
    sourceIntervals := sourceIntervals.push intervalExpr
    sourceProofs := sourceProofs.push proof
  match prepareRuntime config reified sourceFacts with
  | .error error => throwError "interval: {error}"
  | .ok runtime =>
      emitBoundWith config expression term parsed reified sourceIntervals sourceProofs runtime

inductive GoalKind where
  | lower (value : Int) (endpoint : Expr) (strict : Bool)
  | upper (value : Int) (endpoint : Expr) (strict : Bool)
  | equality (value : Int) (endpoint : Expr) (flipped : Bool)

structure Claim where
  expression : Expr
  kind : GoalKind

meta def parseClaim (target : Expr) : MetaM Claim := do
  let target ← instantiateMVars target
  let function := target.getAppFn.constName?
  if function == some ``LE.le || function == some ``LT.lt then
    let strict := function == some ``LT.lt
    let arguments := target.getAppArgs
    if arguments.size < 2 then
      throwError "interval: malformed comparison target"
    let left := arguments[arguments.size - 2]!
    let right := arguments[arguments.size - 1]!
    if let some value := intLiteral? left then
      ensureReal right
      return { expression := right, kind := .lower value left strict }
    if let some value := intLiteral? right then
      ensureReal left
      return { expression := left, kind := .upper value right strict }
    throwError "interval: comparison target needs an integer endpoint"
  if function == some ``Eq then
    let arguments := target.getAppArgs
    if arguments.size < 2 then throwError "interval: malformed equality target"
    let left := arguments[arguments.size - 2]!
    let right := arguments[arguments.size - 1]!
    if let some value := intLiteral? right then
      ensureReal left
      return { expression := left, kind := .equality value right false }
    if let some value := intLiteral? left then
      ensureReal right
      return { expression := right, kind := .equality value left true }
    throwError "interval: equality target needs an integer endpoint"
  throwError "interval: expected a real inequality, equality, or conjunction"

meta def ratIntCast (value : Int) : MetaM Expr :=
  mkAppOptM ``Int.cast #[some (mkConst ``Rat), none, some (mkIntLit value)]

meta def ratOrderProof (leftValue rightValue : Rat) (left right : Expr)
    (strict : Bool) : MetaM Expr := do
  unless (if strict then decide (leftValue < rightValue) else decide (leftValue ≤ rightValue)) do
    throwError "interval: derived endpoint does not prove the requested target"
  let proposition ← mkAppM (if strict then ``LT.lt else ``LE.le)
    #[left, right]
  mkDecideProof proposition

meta def closeClaim (config : Frontend.Config) (bound : Bound) (claim : Claim)
    (expected : Expr) : MetaM Expr := do
  let raw := bound.interval.view
  let .bounds lower upper := raw
    | throwError "interval: derived interval is empty"
  let rawExpr ← Quote.rawExpr raw
  let result ← mkAppM ``ofRawWithin
    #[← Quote.endpointExpr config.rule.endpoint, rawExpr]
  let success ← Quote.trueProof
  let checked ← mkAppM ``BuildResult.eq_ready #[result, success]
  let shape ← mkAppM ``view_ofRawWithin_ready #[checked]
  let candidate ← match claim.kind with
    | .lower value targetEndpoint strict =>
        let .finite endpoint endpointStrict := lower
          | throwError "interval: derived result has no finite lower bound"
        let actual ← mkAppM ``lowerOfMem #[shape, bound.proof]
        let neededStrict := strict && !endpointStrict
        let endpointExpr ← Quote.dyadicExpr endpoint
        let orderRat ← ratOrderProof value endpoint.toRat (← ratIntCast value)
          (← mkAppM ``Dyadic.toRat #[endpointExpr]) neededStrict
        let order ← mkAppOptM
          (if neededStrict then ``intCastLtDyadic else ``intCastLeDyadic)
          #[some (mkIntLit value), some endpointExpr, some orderRat]
        let theoremName :=
          if strict then
            if endpointStrict then ``lowerOpenFromOpen else ``lowerOpenFromClosed
          else if endpointStrict then ``lowerClosedFromOpen else ``lowerClosedFromClosed
        let integerProof ← mkAppM theoremName #[order, actual]
        let endpoint ← endpointProof targetEndpoint value
        let equivalence ← mkAppOptM (if strict then ``castLowerLt else ``castLowerLe)
          #[some targetEndpoint, some claim.expression, some (mkIntLit value), some endpoint]
        mkAppM ``Iff.mpr #[equivalence, integerProof]
    | .upper value targetEndpoint strict =>
        let .finite endpoint endpointStrict := upper
          | throwError "interval: derived result has no finite upper bound"
        let actual ← mkAppM ``upperOfMem #[shape, bound.proof]
        let neededStrict := strict && !endpointStrict
        let endpointExpr ← Quote.dyadicExpr endpoint
        let orderRat ← ratOrderProof endpoint.toRat value
          (← mkAppM ``Dyadic.toRat #[endpointExpr]) (← ratIntCast value) neededStrict
        let order ← mkAppOptM
          (if neededStrict then ``dyadicLtIntCast else ``dyadicLeIntCast)
          #[some endpointExpr, some (mkIntLit value), some orderRat]
        let theoremName :=
          if strict then
            if endpointStrict then ``upperOpenFromOpen else ``upperOpenFromClosed
          else if endpointStrict then ``upperClosedFromOpen else ``upperClosedFromClosed
        let integerProof ← mkAppM theoremName #[order, actual]
        let endpoint ← endpointProof targetEndpoint value
        let equivalence ← mkAppOptM (if strict then ``castUpperLt else ``castUpperLe)
          #[some targetEndpoint, some claim.expression, some (mkIntLit value), some endpoint]
        mkAppM ``Iff.mpr #[equivalence, integerProof]
    | .equality value targetEndpoint flipped =>
        match lower, upper with
        | .finite left false, .finite right false =>
            unless left == right do
              throwError "interval: derived interval is not a singleton"
            unless left.toRat == (value : Rat) do
              throwError "interval: derived endpoint does not prove the requested target"
            let equalityRat ← do
              let proposition ← mkAppM ``Eq #[toExpr left.toRat, toExpr (value : Rat)]
              mkDecideProof proposition
            let endpointEq ← mkAppOptM ``toRealEqIntCast
              #[some (← Quote.dyadicExpr left), some (mkIntLit value), some equalityRat]
            let integerProof ← mkAppM ``equalityOfMem #[shape, bound.proof, endpointEq]
            let targetEq ← endpointProof targetEndpoint value
            let equivalence ← mkAppOptM ``castEquality
              #[some targetEndpoint, some claim.expression, some (mkIntLit value), some targetEq]
            let proof ← mkAppM ``Iff.mpr #[equivalence, integerProof]
            if flipped then mkAppM ``Eq.symm #[proof] else pure proof
        | _, _ => throwError "interval: derived interval is not a closed singleton"
  let emitter : Proof.Emitter Expr := { emit := pure }
  Proof.emitChecked emitter candidate expected

meta def proveTargetAux (config : Frontend.Config) (target : Expr) (fuel : Nat) : MetaM Expr := do
  match fuel with
  | 0 => throwError "interval: conjunction depth exceeds the resource envelope"
  | fuel + 1 =>
      let target ← instantiateMVars target
      if target.getAppFn.constName? == some ``And then
        let arguments := target.getAppArgs
        if arguments.size < 2 then throwError "interval: malformed conjunction target"
        let left := arguments[arguments.size - 2]!
        let right := arguments[arguments.size - 1]!
        let leftProof ← proveTargetAux config left fuel
        let rightProof ← proveTargetAux config right fuel
        let candidate ← mkAppM ``And.intro #[leftProof, rightProof]
        let emitter : Proof.Emitter Expr := { emit := pure }
        return ← Proof.emitChecked emitter candidate target
      let claim ← parseClaim target
      let bound ← deriveBound config claim.expression
      closeClaim config bound claim target
termination_by fuel

meta def proveTarget (config : Frontend.Config) (target : Expr) : MetaM Expr :=
  proveTargetAux config target config.reify.maxDepth

syntax (name := intervalTac) "interval" : tactic
syntax (name := intervalQueryTac) "interval?" : tactic
syntax (name := intervalBoundTac) "interval_bound " term : tactic

meta def describeRaw : Raw → String
  | .empty => "∅"
  | .bounds lower upper =>
      let left := match lower with
        | .unbounded => "(-∞"
        | .finite endpoint strict =>
            (if strict then "(" else "[") ++ toString endpoint.toRat
      let right := match upper with
        | .unbounded => "+∞)"
        | .finite endpoint strict =>
            toString endpoint.toRat ++ (if strict then ")" else "]")
      left ++ ", " ++ right

meta def describeSelectedCuts : Raw → String
  | .empty => "no selected cut (empty result)"
  | .bounds lower upper =>
      let lowerCut := match lower with
        | .unbounded => none
        | .finite endpoint strict =>
            some <| toString endpoint.toRat ++ (if strict then " < e" else " ≤ e")
      let upperCut := match upper with
        | .unbounded => none
        | .finite endpoint strict =>
            some <| (if strict then "e < " else "e ≤ ") ++ toString endpoint.toRat
      match lowerCut, upperCut with
      | some left, some right => "selected cuts: " ++ left ++ " and " ++ right
      | some left, none => "selected lower cut: " ++ left
      | none, some right => "selected upper cut: " ++ right
      | none, none => "no finite selected cut"

@[tactic intervalTac] meta def evalInterval : Lean.Elab.Tactic.Tactic := fun stx => do
  match stx with
  | `(tactic| interval) =>
      let goal ← Lean.Elab.Tactic.getMainGoal
      goal.withContext do
        let saved ← saveState
        try
          let proof ← proveTarget defaultConfig (← goal.getType)
          goal.assign proof
        catch error =>
          saved.restore
          throw error
      Lean.Elab.Tactic.replaceMainGoal []
  | _ => throwUnsupportedSyntax

@[tactic intervalQueryTac] meta def evalIntervalQuery : Lean.Elab.Tactic.Tactic := fun stx => do
  match stx with
  | `(tactic| interval?) =>
      evalInterval (← `(tactic| interval))
      logInfo m!"interval? using nodes={defaultConfig.reify.maxNodes}, term-depth={defaultConfig.reify.maxDepth} (about {defaultConfig.reify.maxDepth / 2} arithmetic levels after automatic regularization), chronology={defaultConfig.proof.maxChronology}, precision={defaultConfig.rule.precision}"
  | _ => throwUnsupportedSyntax

@[tactic intervalBoundTac] meta def evalIntervalBound : Lean.Elab.Tactic.Tactic := fun stx => do
  match stx with
  | `(tactic| interval_bound $expression) =>
      let goal ← Lean.Elab.Tactic.getMainGoal
      goal.withContext do
        let report ← withoutModifyingState do
          let value ← Lean.Elab.Term.elabTerm expression (some (mkConst ``Real))
          let bound ← deriveBound defaultConfig value
          pure m!"interval_bound: {describeRaw bound.interval.view}; {describeSelectedCuts bound.interval.view}, where e = {expression}; proved by a {bound.reified.program.nodes.size}-node recipe with {bound.chronology} replay events"
        logInfo report
  | _ => throwUnsupportedSyntax

end Hex.Interval.Tactic
