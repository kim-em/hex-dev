/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexIntervalMathlib.Frontend
public meta import HexIntervalMathlib.Frontend
public import Mathlib.Lean.Elab.Tactic.Basic
public meta import Mathlib.Tactic.NormNum

@[expose] public section

/-!
# Supported arithmetic tactic frontend

This module is the first supported Meta client of `Frontend`, `Rule`, and
`Proof`. Runtime replay authenticates the exact plain chronology. The emitted
ordinary theorem is independently reconstructed from the same arithmetic
recipe and crosses `Proof.emitChecked`, so neither replay data nor a successful
runtime check is reflected into proof syntax.

The current production subset is forward arithmetic over real local variables,
the configured constant, natural power, precision, reciprocal, and division.
Every computed arithmetic row is followed by the package's authenticated
outward regularization row. The bare tactic uses precision `16`, hence the
dyadic grid `2⁻¹⁶`; programmatic callers may supply another admitted precision.
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

def Arithmetic.Result.isReady (result : Arithmetic.Result) : Bool :=
  match result with
  | .ready _ => true
  | .resourceLimit _ => false

def Arithmetic.Result.getValue (result : Arithmetic.Result)
    (success : Arithmetic.Result.isReady result = true) : Hex.Interval :=
  match result with
  | .ready interval => interval
  | .resourceLimit _ => False.elim (by simp [Arithmetic.Result.isReady] at success)

theorem Arithmetic.Result.eq_ready (result : Arithmetic.Result)
    (success : Arithmetic.Result.isReady result = true) :
    result = .ready (Arithmetic.Result.getValue result success) := by
  cases result with
  | ready _ => rfl
  | resourceLimit _ =>
      simp [Hex.Interval.Tactic.Arithmetic.Result.isReady] at success

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

theorem contains_of_eq {left right : Hex.Interval} {x : ℝ}
    (equal : left = right) (member : left.Contains x) : right.Contains x := by
  simpa [equal] using member

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

theorem neg_mem_negWithin {limit : EndpointLimit} {input result : Hex.Interval}
    {x : ℝ} (checked : negWithin limit input = .ready result)
    (member : input.Contains x) : result.Contains (-x) := by
  exact (contains_negWithin checked (-x)).2 (by simpa using member)

theorem zero_mem {limit : EndpointLimit} {result : Hex.Interval}
    (checked : singletonWithin limit (.ofInt 0) = .ready result) :
    result.Contains (0 : ℝ) := by
  rw [← toReal_zero]
  exact Rule.constant_mem checked

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

variable {Fact : Type}

meta def listExpr (type : Expr) (items : List Expr) : Expr :=
  items.foldr
    (fun item tail => mkApp3 (mkConst ``List.cons [Level.zero]) type item tail)
    (mkApp (mkConst ``List.nil [Level.zero]) type)

meta def arrayExpr (type : Expr) (items : List Expr) : MetaM Expr :=
  mkAppM ``Array.mk #[listExpr type items]

meta def natOptionExpr : Option Nat → Expr
  | none => mkApp (mkConst ``Option.none [Level.zero]) (mkConst ``Nat)
  | some value => mkApp2 (mkConst ``Option.some [Level.zero])
      (mkConst ``Nat) (mkNatLit value)

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

meta def domainExpr (domain : DomainId) : MetaM Expr :=
  mkAppM ``DomainId.mk #[mkNatLit domain.index]

meta def nodeIdExpr (node : NodeId) : MetaM Expr :=
  mkAppM ``NodeId.mk #[mkNatLit node.index]

meta def opIdExpr (operation : OpId) : MetaM Expr :=
  mkAppM ``OpId.mk #[mkNatLit operation.index]

meta def opKeyExpr (key : OpKey) : MetaM Expr :=
  mkAppM ``OpKey.mk #[toExpr key.name, mkNatLit key.version]

meta def operationExpr (operation : Operation) : MetaM Expr := do
  mkAppM ``Operation.mk
    #[← opKeyExpr operation.key,
      listExpr (mkConst ``DomainId) (← operation.inputs.mapM domainExpr),
      ← domainExpr operation.output]

meta def nodeExpr (node : Node) : MetaM Expr := do
  mkAppM ``Node.mk
    #[← domainExpr node.domain, ← opIdExpr node.op,
      listExpr (mkConst ``NodeId) (← node.args.mapM nodeIdExpr)]

meta def programExpr (program : Program) : MetaM Expr := do
  mkAppM ``Program.mk
    #[← arrayExpr (mkConst ``Operation) (← program.operations.toList.mapM operationExpr),
      ← arrayExpr (mkConst ``Node) (← program.nodes.toList.mapM nodeExpr)]

meta def scopeExpr (scope : Policy.ScopeId) : MetaM Expr :=
  mkAppM ``Policy.ScopeId.mk #[mkNatLit scope.index]

meta def seenExpr (seen : SeenVersion) : MetaM Expr := do
  mkAppM ``SeenVersion.mk #[← nodeIdExpr seen.node, mkNatLit seen.version]

meta def ruleKeyExpr (key : RuleKey) : MetaM Expr :=
  mkAppM ``RuleKey.mk #[toExpr key.name, mkNatLit key.schema]

meta def ruleIdExpr (rule : RuleId) : MetaM Expr :=
  mkAppM ``RuleId.mk #[mkNatLit rule.index]

meta def applicationExpr (application : ApplicationId) : MetaM Expr :=
  mkAppM ``ApplicationId.mk #[mkNatLit application.index]

meta def equalityExpr (equality : EqualityId) : MetaM Expr :=
  mkAppM ``EqualityId.mk #[mkNatLit equality.index]

meta def structuralKeyExpr : StructuralKey → MetaM Expr
  | .node node => do mkAppM ``StructuralKey.node #[← nodeIdExpr node]
  | .equality equality => do
      mkAppM ``StructuralKey.equality #[← equalityExpr equality]
  | .application application => do
      mkAppM ``StructuralKey.application #[← applicationExpr application]

meta def structuralInputExpr (input : StructuralInput) : MetaM Expr := do
  mkAppM ``StructuralInput.mk
    #[← structuralKeyExpr input.key, mkNatLit input.generation]

meta def actionKindExpr : ActionKind → Expr
  | .forward => mkConst ``ActionKind.forward
  | .backward => mkConst ``ActionKind.backward
  | .improve => mkConst ``ActionKind.improve
  | .shave => mkConst ``ActionKind.shave
  | .instantiate => mkConst ``ActionKind.instantiate
  | .rewrite => mkConst ``ActionKind.rewrite
  | .regularize => mkConst ``ActionKind.regularize
  | .split => mkConst ``ActionKind.split

meta def actionExpr (action : Action) : MetaM Expr := do
  mkAppM ``Action.mk
    #[mkNatLit action.serial, mkNatLit action.programVersion,
      ← applicationExpr action.application, ← ruleIdExpr action.rule,
      ← ruleKeyExpr action.key, ← nodeIdExpr action.node,
      actionKindExpr action.kind, mkNatLit action.effort,
      mkNatLit action.generation,
      listExpr (mkConst ``SeenVersion) (← action.inputs.mapM seenExpr),
      listExpr (mkConst ``NodeId) (← action.writes.mapM nodeIdExpr),
      listExpr (mkConst ``StructuralInput)
        (← action.structuralInputs.mapM structuralInputExpr),
      natOptionExpr action.matcherEpoch]

meta def roleExpr : Proof.Role → Expr
  | .fact => mkConst ``Proof.Role.fact
  | .equality => mkConst ``Proof.Role.equality
  | .instance => mkConst ``Proof.Role.instance
  | .refute => mkConst ``Proof.Role.refute

meta def keyExpr (key : Proof.Key) : MetaM Expr := do
  mkAppM ``Proof.Key.mk
    #[← ruleKeyExpr key.rule, roleExpr key.role, mkNatLit key.bodySchema]

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

meta def nodeFactExpr (factExpr : Fact → MetaM Expr) (fact : Proof.NodeFact Fact) :
    MetaM Expr := do
  mkAppM ``Proof.NodeFact.mk #[← nodeIdExpr fact.node, ← factExpr fact.fact]

meta def inputExpr (factType : Expr) (factExpr : Fact → MetaM Expr)
    (input : Proof.Input Fact) : MetaM Expr := do
  mkAppM ``Proof.Input.mk
    #[← scopeExpr input.scope, ← programExpr input.program,
      ← arrayExpr factType (← input.facts.toList.mapM factExpr),
      ← nodeFactExpr factExpr input.target]

meta def factStepExpr (_factType : Expr) (factExpr : Fact → MetaM Expr)
    (step : Proof.FactStep Fact) : MetaM Expr := do
  mkAppM ``Proof.FactStep.mk
    #[← scopeExpr step.scope, mkNatLit step.programVersion,
      ← actionExpr step.action, ← nodeIdExpr step.node,
      ← seenExpr step.previous, mkNatLit step.version,
      ← factExpr step.proposed, ← factExpr step.installed,
      listExpr (mkConst ``SeenVersion) (← step.assumptions.mapM seenExpr),
      ← keyExpr step.schema,
      listExpr (mkConst ``Nat) (step.body.map mkNatLit)]

meta def equalityStepExpr (step : Proof.EqualityStep) : MetaM Expr := do
  mkAppM ``Proof.EqualityStep.mk
    #[← scopeExpr step.scope, mkNatLit step.programVersion,
      ← actionExpr step.action, ← equalityExpr step.equality,
      ← nodeIdExpr step.left, ← nodeIdExpr step.right,
      listExpr (mkConst ``SeenVersion) (← step.assumptions.mapM seenExpr),
      ← keyExpr step.schema,
      listExpr (mkConst ``Nat) (step.body.map mkNatLit)]

meta def transportStepExpr (factExpr : Fact → MetaM Expr)
    (step : Proof.TransportStep Fact) : MetaM Expr := do
  mkAppM ``Proof.TransportStep.mk
    #[← scopeExpr step.scope, mkNatLit step.programVersion,
      ← nodeIdExpr step.node, ← seenExpr step.previous,
      mkNatLit step.version, ← equalityExpr step.equality,
      ← seenExpr step.source, ← factExpr step.installed]

meta def instanceStepExpr (step : Proof.InstanceStep) : MetaM Expr := do
  mkAppM ``Proof.InstanceStep.mk
    #[← scopeExpr step.scope, mkNatLit step.beforeVersion,
      mkNatLit step.afterVersion, ← actionExpr step.action,
      ← programExpr step.after,
      listExpr (mkConst ``NodeId) (← step.newNodes.mapM nodeIdExpr),
      ← keyExpr step.schema,
      listExpr (mkConst ``Nat) (step.body.map mkNatLit)]

meta def eventExpr (factType : Expr) (factExpr : Fact → MetaM Expr) :
    Proof.Event Fact → MetaM Expr
  | .fact step => do
      mkAppM ``Proof.Event.fact #[← factStepExpr factType factExpr step]
  | .equality step => do
      mkAppM ``Proof.Event.equality #[factType, ← equalityStepExpr step]
  | .transport step => do
      mkAppM ``Proof.Event.transport #[← transportStepExpr factExpr step]
  | .instance step => do
      mkAppM ``Proof.Event.instance #[factType, ← instanceStepExpr step]

meta def eventsExpr (factType : Expr) (factExpr : Fact → MetaM Expr)
    (events : List (Proof.Event Fact)) : MetaM Expr := do
  pure <| listExpr (mkApp (mkConst ``Proof.Event [Level.zero]) factType)
    (← events.mapM (eventExpr factType factExpr))

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
regularization row denoting the same real expression. -/
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

structure Derived where
  expression : Expr
  interval : Hex.Interval
  intervalExpr : Expr
  proof : Expr
  node : NodeId
  seen : SeenVersion

structure Bound where
  expression : Expr
  interval : Hex.Interval
  intervalExpr : Expr
  proof : Expr
  reified : Frontend.Result
  input : Proof.Input Hex.Interval
  events : List (Proof.Event Hex.Interval)

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

meta def getDerived (derived : Array Derived) (node : NodeId) : MetaM Derived :=
  match derived[node.index]? with
  | some value => pure value
  | none => throwError "interval: arithmetic dependency escaped the derived table"

meta def buildValueExpr (result : Expr) : MetaM (Expr × Expr) := do
  let ready ← mkAppM ``BuildResult.isReady #[result]
  let success ← mkDecideProof (← mkAppM ``Eq #[ready, toExpr true])
  let value ← mkAppM ``BuildResult.getValue #[result, success]
  let checked ← mkAppM ``BuildResult.eq_ready #[result, success]
  pure (value, checked)

meta def arithmeticValueExpr (result : Expr) : MetaM (Expr × Expr) := do
  let ready ← mkAppM ``Arithmetic.Result.isReady #[result]
  let success ← mkDecideProof (← mkAppM ``Eq #[ready, toExpr true])
  let value ← mkAppM ``Arithmetic.Result.getValue #[result, success]
  let checked ← mkAppM ``Arithmetic.Result.eq_ready #[result, success]
  pure (value, checked)

meta def actionFor (serial ruleIndex : Nat) (key : RuleKey) (node : NodeId)
    (inputs : List SeenVersion) : Action :=
  { serial, programVersion := 0, application := { index := serial }
    rule := { index := ruleIndex }, key, node, kind := .forward, effort := 0
    inputs, writes := [node] }

structure OperationResult where
  interval : Hex.Interval
  intervalExpr : Expr
  proof : Expr
  ruleIndex : Nat
  key : RuleKey
  tag : Nat

meta def deriveOperation (config : Frontend.Config) (term : Frontend.Term)
    (expression : Expr) (arguments : List Derived) : MetaM OperationResult := do
  let endpoint ← Quote.endpointExpr config.rule.endpoint
  let finishBuild (runtime : BuildResult) (resultTerm : Expr) (theoremName : Name)
      (ruleIndex tag : Nat) (key : RuleKey) : MetaM OperationResult := do
    let interval ← match runtime with
      | .ready interval => pure interval
      | .resourceLimit cost =>
          throwError "interval: {key.name} resource refusal: {repr cost}"
    let (intervalExpr, checked) ← buildValueExpr resultTerm
    let proof ← mkAppM theoremName (#[checked] ++ arguments.toArray.map (·.proof))
    let expected ← mkAppM ``Hex.Interval.Contains #[intervalExpr, expression]
    let emitter : Proof.Emitter Expr := { emit := pure }
    let proof ← Proof.emitChecked emitter proof expected
    pure { interval, intervalExpr, proof, ruleIndex, key, tag }
  let finishArithmetic (runtime : Arithmetic.Result) (resultTerm : Expr)
      (theoremName : Name) (ruleIndex tag : Nat) (key : RuleKey) :
      MetaM OperationResult := do
    let interval ← match runtime with
      | .ready interval => pure interval
      | .resourceLimit cost =>
          throwError "interval: {key.name} resource refusal: {repr cost}"
    let (intervalExpr, checked) ← arithmeticValueExpr resultTerm
    let proof ← mkAppM theoremName (#[checked] ++ arguments.toArray.map (·.proof))
    let expected ← mkAppM ``Hex.Interval.Contains #[intervalExpr, expression]
    let emitter : Proof.Emitter Expr := { emit := pure }
    let proof ← Proof.emitChecked emitter proof expected
    pure { interval, intervalExpr, proof, ruleIndex, key, tag }
  match term, arguments with
  | .constant, [] =>
      unless config.rule.constant == .ofInt 0 do
        throwError "interval: the production tactic currently quotes only zero"
      let runtime := singletonWithin config.rule.endpoint config.rule.constant
      let resultTerm ← mkAppM ``singletonWithin
        #[endpoint, ← Quote.dyadicExpr config.rule.constant]
      let interval ← match runtime with
        | .ready interval => pure interval
        | .resourceLimit cost =>
            throwError "interval: {Rule.constantKey.name} resource refusal: {repr cost}"
      let (intervalExpr, checked) ← buildValueExpr resultTerm
      let proof ← mkAppM ``zero_mem #[checked]
      let expected ← mkAppM ``Hex.Interval.Contains #[intervalExpr, expression]
      let emitter : Proof.Emitter Expr := { emit := pure }
      let proof ← Proof.emitChecked emitter proof expected
      return ⟨interval, intervalExpr, proof, 8, Rule.constantKey, 9⟩
  | .neg _, [input] =>
      let runtime := negWithin config.rule.endpoint input.interval
      let resultTerm ← mkAppM ``negWithin #[endpoint, input.intervalExpr]
      finishBuild runtime resultTerm ``neg_mem_negWithin 0 1 Rule.negKey
  | .add _ _, [left, right] =>
      let runtime := addWithin config.rule.endpoint left.interval right.interval
      let resultTerm ← mkAppM ``addWithin #[endpoint, left.intervalExpr, right.intervalExpr]
      finishBuild runtime resultTerm ``add_mem_addWithin 1 2 Rule.addKey
  | .sub _ _, [left, right] =>
      let runtime := subWithin config.rule.endpoint left.interval right.interval
      let resultTerm ← mkAppM ``subWithin #[endpoint, left.intervalExpr, right.intervalExpr]
      finishBuild runtime resultTerm ``sub_mem_subWithin 2 3 Rule.subKey
  | .mul _ _, [left, right] =>
      let runtime := mulWithin config.rule.endpoint left.interval right.interval
      let resultTerm ← mkAppM ``mulWithin #[endpoint, left.intervalExpr, right.intervalExpr]
      finishArithmetic runtime resultTerm ``mul_mem_mulWithin 3 4 Rule.mulKey
  | .pow _, [input] =>
      let runtime := powWithin config.rule.endpoint config.rule.powerWork
        input.interval config.rule.exponent
      let work ← mkAppM ``Arithmetic.PowLimits.mk
        #[mkNatLit config.rule.powerWork.maxExponent]
      let resultTerm ← mkAppM ``powWithin
        #[endpoint, work, input.intervalExpr, mkNatLit config.rule.exponent]
      finishArithmetic runtime resultTerm ``pow_mem_powWithin 4 5 Rule.powKey
  | .abs _, [input] =>
      let runtime := absWithin config.rule.endpoint input.interval
      let resultTerm ← mkAppM ``absWithin #[endpoint, input.intervalExpr]
      finishBuild runtime resultTerm ``abs_mem_absWithin 5 6 Rule.absKey
  | .min _ _, [left, right] =>
      let runtime := minWithin config.rule.endpoint left.interval right.interval
      let resultTerm ← mkAppM ``minWithin #[endpoint, left.intervalExpr, right.intervalExpr]
      finishBuild runtime resultTerm ``min_mem_minWithin 6 7 Rule.minKey
  | .max _ _, [left, right] =>
      let runtime := maxWithin config.rule.endpoint left.interval right.interval
      let resultTerm ← mkAppM ``maxWithin #[endpoint, left.intervalExpr, right.intervalExpr]
      finishBuild runtime resultTerm ``max_mem_maxWithin 7 8 Rule.maxKey
  | .inv _, [input] =>
      let runtime := invWithin config.rule.precisionLimits config.rule.precision input.interval
      let resultTerm ← mkAppM ``invWithin
        #[← Quote.precisionLimitsExpr config.rule.precisionLimits,
          mkIntLit config.rule.precision, input.intervalExpr]
      finishArithmetic runtime resultTerm ``inv_mem_invWithin 9 10 Rule.invKey
  | .div _ _, [left, right] =>
      let runtime := divWithin config.rule.precisionLimits config.rule.precision
        left.interval right.interval
      let resultTerm ← mkAppM ``divWithin
        #[← Quote.precisionLimitsExpr config.rule.precisionLimits,
          mkIntLit config.rule.precision, left.intervalExpr, right.intervalExpr]
      finishArithmetic runtime resultTerm ``div_mem_divWithin 10 11 Rule.divKey
  | .regularize _, [input] =>
      let runtime := regularizeWithin config.rule.precisionLimits config.rule.precision
        input.interval
      let resultTerm ← mkAppM ``regularizeWithin
        #[← Quote.precisionLimitsExpr config.rule.precisionLimits,
          mkIntLit config.rule.precision, input.intervalExpr]
      finishArithmetic runtime resultTerm ``mem_regularizeWithin 11 12 Rule.regularizeKey
  | _, _ => throwError "interval: malformed reified operation"

/-- Derive one exact forward interval and its ordinary membership proof.
Runtime chronology is authenticated by supported replay before the independently
emitted proof is returned. -/
meta def deriveBound (config : Frontend.Config) (expression : Expr) : MetaM Bound := do
  let expression ← instantiateMVars expression
  let (term, parsed) ← parseTerm config expression
  let reified ←
    match Frontend.reifyWithin config parsed.sources.size term with
    | .ok result => pure result
    | .error error => throwError "interval: reification failed: {repr error}"
  let mut sourceValues : Array Derived := #[]
  let mut sourceFacts : Array Hex.Interval := #[]
  for index in [0:parsed.sources.size] do
    let some source := parsed.sources[index]?
      | throwError "interval: source index escaped the parsed source table"
    let some node := reified.sourceNode? index
      | throwError "interval: selected source is absent from the target graph"
    let cuts ← collectCuts source
    let (interval, intervalExpr, proof) ← sourceProof config source cuts
    sourceFacts := sourceFacts.push interval
    sourceValues := sourceValues.push
      { expression := source, interval, intervalExpr, proof, node
        seen := { node, version := 0 } }
  let mut derived : Array Derived := #[]
  let mut events : List (Proof.Event Hex.Interval) := []
  let scope : Policy.ScopeId := { index := 0 }
  let mut serial := 0
  for entry in reified.entries do
    unless entry.node.index == derived.size do
      throwError "interval: reifier entry table is not in node order"
    let some nodeExpression := parsed.expression? entry.term
      | throwError "interval: reified term has no Lean expression"
    match entry.term with
    | .source index =>
        let some source := sourceValues[index]?
          | throwError "interval: source node escaped the source proof table"
        unless source.node == entry.node do
          throwError "interval: source node differs from its reified address"
        derived := derived.push source
    | _ =>
        let some instruction := reified.program.node? entry.node
          | throwError "interval: reified node escaped its program"
        let mut arguments : List Derived := []
        for argument in instruction.args do
          arguments := arguments.concat (← getDerived derived argument)
        let result ← deriveOperation config entry.term nodeExpression arguments
        let inputs := arguments.map (·.seen)
        let action := actionFor serial result.ruleIndex result.key entry.node inputs
        let step : Proof.FactStep Hex.Interval :=
          { scope, programVersion := 0, action, node := entry.node
            previous := { node := entry.node, version := 0 }
            version := 1, proposed := result.interval, installed := result.interval
            assumptions := inputs, schema := Rule.schemaKey result.key
            body := [result.tag] }
        events := events.concat (.fact step)
        derived := derived.push
          { expression := nodeExpression, interval := result.interval
            intervalExpr := result.intervalExpr, proof := result.proof
            node := entry.node, seen := { node := entry.node, version := 1 } }
        serial := serial + 1
  let output ← getDerived derived reified.target
  let input ←
    match Frontend.inputWithin config scope reified sourceFacts output.interval with
    | .ok input => pure input
    | .error error => throwError "interval: input construction failed: {repr error}"
  match Frontend.replay config input events 0 reified.program output.seen with
  | .error error => throwError "interval: supported replay rejected the recipe: {repr error}"
  | .ok _ => pure ()
  let canonicalExpr ← Quote.intervalExpr config.rule.endpoint output.interval
  let canonicalExpected ← mkAppM ``Hex.Interval.Contains #[canonicalExpr, expression]
  let intervalEq ← mkDecideProof (← mkAppM ``Eq #[output.intervalExpr, canonicalExpr])
  let candidate ← mkAppM ``contains_of_eq #[intervalEq, output.proof]
  let emitter : Proof.Emitter Expr := { emit := pure }
  let canonicalProof ← Proof.emitChecked emitter candidate canonicalExpected
  pure
    { expression, interval := output.interval, intervalExpr := canonicalExpr
      proof := canonicalProof, reified, input, events }

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
      logInfo m!"interval? using nodes={defaultConfig.reify.maxNodes}, depth={defaultConfig.reify.maxDepth}, chronology={defaultConfig.proof.maxChronology}, precision={defaultConfig.rule.precision}"
  | _ => throwUnsupportedSyntax

@[tactic intervalBoundTac] meta def evalIntervalBound : Lean.Elab.Tactic.Tactic := fun stx => do
  match stx with
  | `(tactic| interval_bound $expression) =>
      let goal ← Lean.Elab.Tactic.getMainGoal
      goal.withContext do
        let report ← withoutModifyingState do
          let value ← Lean.Elab.Term.elabTerm expression (some (mkConst ``Real))
          let bound ← deriveBound defaultConfig value
          pure m!"interval_bound: {describeRaw bound.interval.view}; proved by a {bound.reified.program.nodes.size}-node recipe with {bound.events.length} replay events; use `have : _ := by interval` to materialize a selected cut"
        logInfo report
  | _ => throwUnsupportedSyntax

end Hex.Interval.Tactic
