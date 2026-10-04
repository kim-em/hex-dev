/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public meta import HexRCF.Tactic
public meta import HexRCF.RealCoefficients.Reify
public meta import HexRCF.RealCoefficients.AlgebraicBounds
public import HexRCF.RealCoefficients.Registration
public meta import Mathlib.Tactic.Linarith
public meta import Mathlib.Tactic.NormNum.RealSqrt

public meta section

/-! Finite supplied-bound proof construction. This path uses containment only,
not a partial order as a field instance. It makes no completeness claim. Search
executes caller approximations; checking examines frozen bounds and ordinary
proofs, and does not call approximation or root search. -/

namespace Hex.RCF.RealCoefficients.Finite

open Lean Meta Qq Hex.OrderedFn.Oracle

/-- A frozen callback result and its checked identity/containment. Replay binds
it to the exact declaration, subject, version and positive request. -/
structure Observation where
  declaration : Name
  subject : Expr
  version : Nat
  request : Rat
  bounds : Bounds
  identity : Expr
  containment : Expr

structure Enclosure where
  source : Expr
  bounds : Bounds
  literal : Expr
  proof : Expr
  observations : Array Observation := #[]

structure Prepared where
  source : Reify.Source
  registry : Array (Name × Expr)
  request : Rat
  coefficients : Array Enclosure
  guards : Array (Expr × Expr)
  guardBounds : Array Enclosure

/-- The proposed proof is ordinary Lean evidence. All source guard proofs are
checked separately, even if the conclusion's proof does not use them. -/
structure Certificate where
  prepared : Prepared
  proof : Expr

private def ratExpr (q : Rat) : MetaM Expr :=
  mkAppM ``mkRat #[mkIntLit q.num, mkNatLit q.den]

private def boundsExpr (b : Bounds) : MetaM Expr := do
  let lower ← ratExpr b.lower
  let upper ← ratExpr b.upper
  let ordered ← mkDecideProof (← mkAppM ``LE.le #[lower, upper])
  mkAppM ``Bounds.mk #[lower, upper, ordered]

private unsafe def evalBoundsUnsafe (e : Expr) : MetaM Bounds :=
  evalExpr Bounds (mkConst ``Bounds) e

@[implemented_by evalBoundsUnsafe]
private opaque evalBounds (e : Expr) : MetaM Bounds

private unsafe def evalNatUnsafe (e : Expr) : MetaM Nat :=
  evalExpr Nat (mkConst ``Nat) e

@[implemented_by evalNatUnsafe]
private opaque evalNat (e : Expr) : MetaM Nat

private def transaction (action : MetaM α) : MetaM α := do
  let saved ← saveState
  let (result, _) ← tryFinally' action fun result => do
    match result with
    | some _ => modify fun state => { state with
        mctx := saved.meta.mctx, postponed := saved.meta.postponed,
        zetaDeltaFVarIds := saved.meta.zetaDeltaFVarIds }
    | none => saved.restore
  return result

/-- Check and close proof auxiliaries while retaining their transitive ordinary
axiom dependencies. Disable the auxiliary cache: another proof of the same type
must not validate this candidate. -/
private def ordinary (proof : Expr) (expected : Expr) : MetaM Expr := do
  let proof ← instantiateMVars proof
  if proof.hasMVar then throwError "rcf: unresolved finite evidence"
  unless ← withNewMCtxDepth (isDefEq (← inferType proof) expected) do
    throwError "rcf: finite evidence proves the wrong proposition"
  Hex.RCF.checkAxioms `Hex.RCF.RealCoefficients.Finite proof
  if (← getEnv).hasUnsafe proof then throwError "rcf: unsafe finite evidence"
  withOptions (fun opts => debug.skipKernelTC.set (Elab.async.set opts false) false) do
    mkAuxTheorem expected proof (zetaDelta := true) (cache := false)

private def checked (source : Expr) (bounds : Bounds) (proof : Expr)
    (observations : Array Observation := #[]) (computed : Option Expr := none) :
    MetaM Enclosure := do
  let literal ← boundsExpr bounds
  let expected ← mkAppM ``Contains #[literal, source]
  let actual := computed.getD literal
  -- Native arithmetic proposes the endpoints; explicit equality reduction
  -- checks them. Do not rely on elaborator definitional equality of fractions.
  let identity ← mkDecideProof (← mkAppM ``Eq #[actual, literal])
  let predicate ← withLocalDeclD `bounds (mkConst ``Bounds) fun b => do
    mkLambdaFVars #[b] (← mkAppM ``Contains #[b, source])
  let transported ← mkAppM ``Eq.mp
    #[← mkAppM ``congrArg #[predicate, identity], proof]
  return ⟨source, bounds, literal, ← ordinary transported expected, observations⟩

private def runStrict (goal : MVarId) (code : Syntax) : MetaM (List MVarId) := do
  instantiateMVarDeclMVars goal
  let action : Elab.TermElabM (List MVarId) :=
    Elab.Term.withSynthesize do
      Elab.Tactic.run goal <| Elab.Tactic.withoutRecover
        (Elab.Tactic.evalTactic code *> Elab.Tactic.pruneSolvedGoals)
  action.run' {} {}

private def rational (source : Expr) : MetaM Enclosure := do
  let source : Q(ℝ) := source
  let ⟨value, _, _, _⟩ ← Mathlib.Meta.NormNum.deriveRat source (_inst := q(inferInstance))
  let bounds := Bounds.singleton value
  let literal ← boundsExpr bounds
  let expected ← mkAppM ``Contains #[literal, source]
  let goal ← mkFreshExprMVar expected
  let rest ← runStrict goal.mvarId!
    (← `(tactic| norm_num [Contains, Bounds.mk, mkRat]))
  unless rest.isEmpty do throwError "rcf: could not quote rational containment"
  checked source bounds (← instantiateMVars goal)

-- One preparation fixes the registry and request. Exact source keys preserve
-- subject/embedding identity; the local cache never enters a certificate.
private abbrev Cache := IO.Ref (ExprMap Enclosure)

mutual
private partial def enclose (cache : Cache) (entries : Array (Name × Expr)) (request : Rat)
    (source : Expr) : MetaM Enclosure := do
  if let some evidence := (← cache.get)[source]? then return evidence
  let evidence ← encloseCore cache entries request source
  cache.modify (·.insert source evidence)
  return evidence

private partial def encloseCore (cache : Cache) (entries : Array (Name × Expr)) (request : Rat)
    (source : Expr) : MetaM Enclosure := do
  -- Whole-subject matching precedes arithmetic and rational normalization.
  for (name, subject) in entries do
    if ← Registration.sameSubject source subject then
      let registration := mkConst name
      let δ ← ratExpr request
      let positive ← mkDecideProof (← mkAppM ``LT.lt #[← ratExpr 0, δ])
      let computation ← mkAppM ``Registration.approximation #[registration, δ]
      let bounds ← evalBounds computation
      let literal ← boundsExpr bounds
      let identity ← mkDecideProof (← mkAppM ``Eq #[computation, literal])
      let identity ← ordinary identity (← mkAppM ``Eq #[computation, literal])
      let containment ← mkAppM ``Registration.containment #[registration, δ, positive]
      let transported ← mkAppM ``Eq.mp
        #[← mkAppM ``congrArg #[← withLocalDeclD `bounds (mkConst ``Bounds) fun b => do
          mkLambdaFVars #[b] (← mkAppM ``Contains #[b, source]), identity], containment]
      let containment ← ordinary transported (← mkAppM ``Contains #[literal, source])
      let version ← evalNat (← mkAppM ``Registration.version #[registration])
      return ← checked source bounds containment
        #[{ declaration := name, subject := source, version, request, bounds, identity, containment }]
  let e := source.consumeMData
  let (op, args) := e.getAppFnArgs
  let realPower ← if op == ``HPow.hPow && args.size == 6 then
      pure ((← inferType args[5]!).isConstOf ``Real) else pure false
  if e.isAppOfArity ``RealAlgebraicNumber.toReal 1 ||
      e.isAppOfArity ``Real.sqrt 1 || e.isAppOfArity ``Real.rpow 2 || realPower then
    if (← (Hex.RCF.Reify.recognizeCoefficient source).run).isOk then
      return ← rational source
    let (bounds, proof) ← AlgebraicBounds.enclose source request
    return ← checked source bounds proof
  if [``HAdd.hAdd, ``HSub.hSub, ``HMul.hMul, ``HDiv.hDiv].contains op && args.size == 6 then
    let left ← enclose cache entries request args[4]!
    let right ← enclose cache entries request args[5]!
    if op == ``HSub.hSub then
      if ← Registration.sameSubject left.source right.source then
        let zero ← rational q((0 : ℝ))
        let proof ← mkAppM ``Eq.mp #[← mkAppM ``congrArg
          #[← withLocalDeclD `value q(ℝ) fun x => do
            mkLambdaFVars #[x] (← mkAppM ``Contains #[zero.literal, x]),
            ← mkEqSymm (← mkAppM ``sub_self #[left.source])], zero.proof]
        return ← checked source zero.bounds proof (left.observations ++ right.observations)
      let operand : Q(ℝ) := right.source
      let negative ← checked q(-$operand) right.bounds.neg
        (← mkAppM ``Contains.neg #[right.proof]) right.observations
        (some (← mkAppM ``Bounds.neg #[right.literal]))
      let x : Q(ℝ) := left.source
      let y : Q(ℝ) := right.source
      let sum ← checked q($x + -$y) (left.bounds.add negative.bounds)
        (← mkAppM ``Contains.add #[left.proof, negative.proof]) #[]
        (some (← mkAppM ``Bounds.add #[left.literal, negative.literal]))
      let equality ← mkAppM ``Eq.symm #[← mkAppM ``sub_eq_add_neg #[x, y]]
      let literal ← boundsExpr (left.bounds.add negative.bounds)
      let predicate ← withLocalDeclD `value q(ℝ) fun value => do
        mkLambdaFVars #[value] (← mkAppM ``Contains #[literal, value])
      let transported ← mkAppM ``Eq.mp
        #[← mkAppM ``congrArg #[predicate, equality], sum.proof]
      return ← checked source (left.bounds.add negative.bounds) transported (left.observations ++ right.observations)
    if op == ``HAdd.hAdd then
      return ← checked source (left.bounds.add right.bounds)
        (← mkAppM ``Contains.add #[left.proof, right.proof]) (left.observations ++ right.observations)
        (some (← mkAppM ``Bounds.add #[left.literal, right.literal]))
    if op == ``HMul.hMul then
      return ← checked source (left.bounds.mul right.bounds)
        (← mkAppM ``Contains.mul #[left.proof, right.proof]) (left.observations ++ right.observations)
        (some (← mkAppM ``Bounds.mul #[left.literal, right.literal]))
    let some bounds := left.bounds.div? right.bounds |
      throwError "rcf: supplied bounds do not separate a divisor from zero"
    let divided ← mkAppM ``Contains.div
      #[left.proof, right.proof, ← mkDecideProof
        (← mkAppM ``Eq #[← mkAppM ``Bounds.div? #[left.literal, right.literal],
          ← mkAppM ``Option.some #[← boundsExpr bounds]])]
    return ← checked source bounds (← mkAppM ``And.left #[divided]) (left.observations ++ right.observations)
  if op == ``Neg.neg && args.size == 3 then
    let child ← enclose cache entries request args[2]!
    return ← checked source child.bounds.neg (← mkAppM ``Contains.neg #[child.proof]) child.observations
      (some (← mkAppM ``Bounds.neg #[child.literal]))
  if op == ``Inv.inv && args.size == 3 then
    let x : Q(ℝ) := args[2]!
    let quotient ← enclose cache entries request q((1 : ℝ) / $x)
    let predicate ← withLocalDeclD `value q(ℝ) fun value => do
      mkLambdaFVars #[value] (← mkAppM ``Contains #[quotient.literal, value])
    let proof ← mkAppM ``Eq.mp #[← mkAppM ``congrArg
      #[predicate, ← mkAppM ``one_div #[x]], quotient.proof]
    return ← checked source quotient.bounds proof quotient.observations
  if op == ``HPow.hPow && args.size == 6 then
    let some exponent ← getNatValue? args[5]! |
      throwError "rcf: supplied bounds support natural coefficient powers"
    let base ← enclose cache entries request args[4]!
    let mut result := { (← rational q((1 : ℝ))) with observations := base.observations }
    for _ in [:exponent] do
      let x : Q(ℝ) := base.source
      let y : Q(ℝ) := result.source
      result ← checked q($x * $y) (base.bounds.mul result.bounds)
        (← mkAppM ``Contains.mul #[base.proof, result.proof]) base.observations
        (some (← mkAppM ``Bounds.mul #[base.literal, result.literal]))
    let equality ← mkFreshExprMVar (← mkAppM ``Eq #[result.source, source])
    let rest ← runStrict equality.mvarId! (← `(tactic| ring))
    unless rest.isEmpty do throwError "rcf: failed to reconstruct coefficient power"
    let predicate ← withLocalDeclD `value q(ℝ) fun x => do
      mkLambdaFVars #[x] (← mkAppM ``Contains #[result.literal, x])
    let proof ← mkAppM ``Eq.mp #[← mkAppM ``congrArg
      #[predicate, ← instantiateMVars equality], result.proof]
    return ← checked source result.bounds proof result.observations
  rational source
end

/-- Freeze supplied bounds and discharge every source guard before proof search.
An exact zero is invalid; a nonseparating bound is unresolved. -/
private def prepareCore (target : Expr) (request : Rat := 1 / 16)
    (source? : Option Reify.Source := none) : MetaM Prepared := do
  unless 0 < request do throwError "rcf: bound request must be positive"
  let candidates ← Registration.candidates
  let source ← match source? with
    | some source => pure source
    | none => match ← Reify.prepare target {} (candidates.map Prod.snd) with
      | .ok source => pure source
      | .error error => throwError "rcf: {Hex.RealFormula.Reify.Error.toMessageData error}"
  let entries ← Registration.used candidates (source.coefficients ++ source.divisors)
  let cache ← IO.mkRef ({} : ExprMap Enclosure)
  let mut guards := #[]
  let mut guardBounds := #[]
  for divisor in source.divisors do
    let evidence ← enclose cache entries request divisor
    if evidence.bounds.lower == 0 && evidence.bounds.upper == 0 then
      throwError "rcf: original closed divisor is zero"
    unless evidence.bounds.separated do
      throwError "rcf: original closed divisor remains unresolved in supplied bounds"
    let separated ← mkDecideProof (← mkAppM ``Eq
      #[← mkAppM ``Bounds.separated #[evidence.literal], mkConst ``Bool.true])
    let nonzero ← mkAppM ``Contains.ne_zero #[evidence.proof, separated]
    guardBounds := guardBounds.push evidence
    guards := guards.push (divisor, ← ordinary nonzero (← mkAppM ``Ne #[divisor, q((0 : ℝ))]))
  let coefficients ← source.coefficients.mapM (enclose cache entries request)
  let registry ← entries.mapM fun (name, _) => do
    return (name, mkNatLit (← evalNat (← mkAppM ``Registration.version #[mkConst name])))
  return { source, registry, request, coefficients, guards, guardBounds }

/-- Prepare transactionally, preserving caller metavariables on success and
restoring the complete saved state on every failure or interruption. -/
def prepare (target : Expr) (request : Rat := 1 / 16) : MetaM Prepared :=
  transaction (prepareCore target request)

private partial def prove (target : Expr) (witness : Expr) : MetaM Expr := do
  let goal ← mkFreshExprMVar target
  if target.isForall then
    let (_, body) ← goal.mvarId!.intro1
    let proof ← body.withContext <| prove (← body.getType) witness
    body.assign proof
  else if target.isAppOfArity ``And 2 then
    let args := target.getAppArgs
    goal.mvarId!.assign (← mkAppM ``And.intro #[← prove args[0]! witness, ← prove args[1]! witness])
  else if target.isAppOfArity ``Exists 2 then
    let body := target.getAppArgs[1]!
    let proof ← prove (mkApp body witness).headBeta witness
    goal.mvarId!.assign (← mkAppOptM ``Exists.intro
      #[some (← inferType witness), some body, some witness, some proof])
  else
    let rest ← runStrict goal.mvarId!
      (← `(tactic| norm_num [mkRat, div_eq_mul_inv] at * <;> nlinarith))
    unless rest.isEmpty do throwError "rcf: supplied bounds did not establish the goal"
  return ← instantiateMVars goal

/-- Propose an ordinary proof from frozen containment facts. Nonlinear proof
search is bounded by Lean's execution limits and may fail without a verdict.
It neither calls root search nor assumes an ordered field of registered values. -/
private def buildCore (prepared : Prepared) : MetaM Certificate := do
  -- Preserve only source variables and the hypotheses used by its checked
  -- alias equivalence. Unrelated caller hypotheses cannot settle the search.
  let roots := #[prepared.source.original, prepared.source.proof,
    prepared.source.formula, prepared.source.valuation]
  let used ← (roots.foldl (fun used e => Lean.collectFVars used e) {}).addDependencies
  let vars := (← getLCtx).getFVarIds.map mkFVar
  let (lctx, instances, _) ← removeUnused vars used
  withLCtx lctx instances do
    let facts ← prepared.coefficients.flatMapM fun e => do
      return #[← mkAppM ``And.left #[e.proof], ← mkAppM ``And.right #[e.proof]]
    let rec withFacts (i : Nat) (parameters : Array Expr) : MetaM Expr := do
      if h : i < facts.size then
        withLocalDeclD (Name.mkSimple s!"bound{i}") (← inferType facts[i]) fun p =>
          withFacts (i + 1) (parameters.push p)
      else
        let witness := prepared.coefficients[0]?.map (·.source) |>.getD q((0 : ℝ))
        let proof ← prove prepared.source.original witness
        return mkAppN (← mkLambdaFVars parameters proof) facts
    termination_by facts.size - i
    let originalProof ← withFacts 0 #[]
    return ⟨prepared, ← mkAppM ``Iff.mpr #[prepared.source.proof, originalProof]⟩

/-- Construct a finite proof transactionally from checked preparation data. -/
def build (prepared : Prepared) : MetaM Certificate := transaction (buildCore prepared)

private def checkEnclosure (entries : Array (Name × Expr)) (request : Rat)
    (evidence : Enclosure) : MetaM Unit := do
  let literal ← boundsExpr evidence.bounds
  unless ← withNewMCtxDepth (isDefEq evidence.literal literal) do
    throwError "rcf: enclosure has a different bounds literal"
  let expected ← Registration.used entries #[evidence.source]
  let observed := evidence.observations.map (·.declaration) |>.qsort Name.lt |>.eraseReps
  unless expected.map Prod.fst == observed do
    throwError "rcf: enclosure omits or transplants provider observations"
  for observation in evidence.observations do
    unless observation.request == request do
      throwError "rcf: enclosure has a different provider precision request"
    let some (_, subject) := entries.find? (fun entry => entry.1 == observation.declaration) |
      throwError "rcf: enclosure uses an unregistered provider"
    unless ← Registration.sameSubject subject observation.subject do
      throwError "rcf: enclosure has a different provider subject"
    let registration := mkConst observation.declaration
    unless ← withNewMCtxDepth <| withTransparency .default <|
        isDefEq (mkNatLit observation.version)
          (← mkAppM ``Registration.version #[registration]) do
      throwError "rcf: enclosure has a stale provider version"
    let literal ← boundsExpr observation.bounds
    let computation ← mkAppM ``Registration.approximation #[registration, ← ratExpr request]
    let _ ← ordinary observation.identity (← mkAppM ``Eq #[computation, literal])
    let _ ← ordinary observation.containment
      (← mkAppM ``Contains #[literal, observation.subject])
  let _ ← ordinary evidence.proof
    (← mkAppM ``Contains #[literal, evidence.source])

/-- Check exact source/registry/guard bindings and every proof. Frozen enclosure
proofs suffice: replay does not evaluate any approximation procedure. -/
private def checkCore (source : Reify.Source) (certificate : Certificate)
    (request : Rat) : MetaM Expr := do
  let prepared := certificate.prepared
  unless prepared.request == request && 0 < request do
    throwError "rcf: finite certificate has a different precision request"
  unless source.original == prepared.source.original && source.formula == prepared.source.formula &&
      source.valuation == prepared.source.valuation && source.coefficients == prepared.source.coefficients &&
      source.divisors == prepared.source.divisors do
    throwError "rcf: finite certificate has a different source binding"
  let entries ← Registration.used (← Registration.candidates)
    (source.coefficients ++ source.divisors)
  unless entries.map Prod.fst == prepared.registry.map Prod.fst do
    throwError "rcf: finite certificate has a stale registry"
  for (name, version) in prepared.registry do
    unless ← withNewMCtxDepth <| withTransparency .default <|
        isDefEq version (← mkAppM ``Registration.version #[mkConst name]) do
      throwError "rcf: finite certificate has a stale provider version"
  unless prepared.coefficients.size == source.coefficients.size && prepared.guards.size == source.divisors.size && prepared.guardBounds.size == source.divisors.size do
    throwError "rcf: finite certificate omits source evidence"
  for (coefficient, evidence) in source.coefficients.zip prepared.coefficients do
    unless evidence.source == coefficient do
      throwError "rcf: finite certificate swaps coefficient subjects"
    checkEnclosure entries request evidence
  for (expected, (divisor, proof)) in source.divisors.zip prepared.guards do
    unless divisor == expected do throwError "rcf: finite certificate swaps divisor subjects"
    let _ ← ordinary proof (← mkAppM ``Ne #[divisor, q((0 : ℝ))])
  for (divisor, evidence) in source.divisors.zip prepared.guardBounds do
    unless divisor == evidence.source do throwError "rcf: finite certificate swaps guard enclosures"
    checkEnclosure entries request evidence
  let schema ← mkAppM ``Hex.RealFormula.Prenex.toProp #[source.formula, source.valuation]
  let proof ← ordinary certificate.proof schema
  ordinary (← mkAppM ``Iff.mp #[source.proof, proof]) source.original

/-- Replay frozen evidence with the expected source and precision request.
Approximation search is not repeated. Failure restores all caller state. -/
def check (source : Reify.Source) (certificate : Certificate)
    (request : Rat := 1 / 16) : MetaM Expr := transaction (checkCore source certificate request)

def handle : Hex.RCF.Handler := fun target => do
  let entries ← Registration.candidates
  let source ← match ← Reify.prepare target {} (entries.map Prod.snd) with
    | .ok source => pure source
    | .error (.unsupported _ _) => return .declined
    | .error error => return .failed (Hex.RealFormula.Reify.Error.toMessageData error)
  let mut status : Bool × Option Expr := (false, none)
  for coefficient in source.coefficients ++ source.divisors do
    let (_, next) ← (Meta.transformWithCache (m := StateRefT (Bool × Option Expr) MetaM)
      coefficient {} (pre := fun e => do
        for (_, subject) in entries do
          if ← Registration.sameSubject e subject then
            modify fun (_, missing) => (true, missing)
            return .done e
        if e.isConstOf ``Real.pi || e.isAppOfArity ``Real.exp 1 then
          modify fun (used, _) => (used, some e)
          return .done e
        return .continue) (skipInstances := true)).run status
    status := next
  if let some missing := status.2 then
    return .failed m!"rcf: missing rcf_constant registration for {missing}"
  unless status.1 do return .declined
  let prepared ← transaction (prepareCore target (1 / 16) (some source))
  let certificate ← build prepared
  return .proved (← check prepared.source certificate)

end Hex.RCF.RealCoefficients.Finite

namespace Hex.RCF.RealCoefficients.Tactic

/-- Lexical registry order places this after the existing exact `handle`.
Registering an algebraic alias must not replace its exact cell solver. -/
@[rcf_handler] def supplied : Hex.RCF.Handler := Finite.handle

end Hex.RCF.RealCoefficients.Tactic
