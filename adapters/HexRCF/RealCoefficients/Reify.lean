/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public meta import HexRealFormulaMathlib.Reify
public meta import HexRCF.Reify
public meta import HexRCF.RealCoefficients.Interpret
public import HexRealAlgebraicMathlib.Basic
public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

public meta section

/-!
# Closed-coefficient source schemas

This frontend produces an equivalence with a shared real formula at a fixed
valuation. It does not authenticate coefficient providers or discharge divisor
guards, and does not register a solver. Consumers must validate every retained
guard before using a coefficient environment or a decision certificate.
-/

namespace Hex.RCF.RealCoefficients.Reify

open Lean Meta Qq

/-- A shared schema specialized at the exact source coefficients. Guards are
original divisor expressions after checked alias substitution (with rational
divisors cast to ℝ), retained before normalization. This is pending frontend data, not an authenticated
coefficient environment or an accepted solver certificate. -/
structure Source where
  /-- Fully instantiated original goal, before division preprocessing or
  coefficient abstraction. -/
  original : Expr
  /-- Closed real coefficient expressions in first-occurrence order. -/
  coefficients : Array Expr
  /-- Original divisors after checked alias substitution; each must separately
  be proved nonzero. Repeated source occurrences may share the same obligation. -/
  divisors : Array Expr
  /-- Shared `Prenex coefficients.size` syntax. -/
  formula : Expr
  /-- The fixed valuation assigning each coordinate its source coefficient. -/
  valuation : Expr
  /-- Ordinary-kernel proof of `Prenex.toProp formula valuation ↔ original`. -/
  proof : Expr
  /-- Shared reflection usage, including source admission and proof assembly. -/
  usage : Hex.Reflect.BudgetUsage

private abbrev FrontendM := Hex.RealFormula.Reify.ReifyM

private def reject (e : Expr) (message : String) : FrontendM α :=
  throwThe Hex.RealFormula.Reify.Error (.unsupported e message)

private def isClosed (e : Expr) : Bool :=
  !e.hasFVar && !e.hasMVar && !e.hasLooseBVars

private def isReal (e : Expr) : MetaM Bool := do
  isDefEq (← inferType e) (mkConst ``Real)

/-- Closed scalar syntax is recognized independently of ring simplification.
In particular zero multiplication does not discard a divisor. -/
private abbrev ScanM := StateRefT (Array Expr) FrontendM

/-- Casts do not hide rational division obligations. Non-field division
inside a cast is outside the coefficient grammar. Shared `arithmetic` validation
subsequently rejects lambdas/lets and other syntax this literal traversal does
not interpret; both checks are required before a cast can be admitted. -/
private partial def castGuards (e : Expr) : ScanM Unit := do
  let (op, args) := e.getAppFnArgs
  let divisor := if op == ``HDiv.hDiv && args.size == 6 then some args[5]!
    else if op == ``Inv.inv && args.size == 3 then some args[2]! else none
  if let some d := divisor then
    unless (← inferType d).isConstOf ``Rat do
      reject e "division inside a literal cast must be rational"
    let d : Q(ℚ) := d
    modify (·.push q(($d : ℝ)))
  for a in args do castGuards a

private partial def scalar (source : Expr) : ScanM Unit := do
  let e := source.consumeMData
  unless isClosed e do reject e "coefficient must be closed"
  if e.isAppOfArity ``Hex.RealAlgebraicNumber.toReal 1 then return ()
  if e.isConstOf ``Real.pi then return ()
  if e.isAppOfArity ``Real.exp 1 then
    let argument := e.appArg!.consumeMData
    unless argument.isAppOfArity ``OfNat.ofNat 3 &&
        getRawNatValue? argument.getAppArgs[1]! == some 1 do
      reject e "only Real.exp 1 is a named exponential coefficient"
    unless ← isDefEq argument q((1 : ℝ)) do
      reject e "nonstandard numeral instance in exponential coefficient"
    return ()
  let args := e.getAppArgs
  let op := e.getAppFn.constName?
  if e.isAppOfArity ``Real.sqrt 1 then
    Hex.RealFormula.Reify.charge .exponent 2
    return ← scalar e.appArg!
  if e.isAppOfArity ``Real.rpow 2 then
    scalar args[0]!
    scalar args[1]!
    let _ ← Coefficients.rootDegree args[1]!
    return ()
  if [``HAdd.hAdd, ``HSub.hSub, ``HMul.hMul, ``HDiv.hDiv].any (op == some ·) &&
      args.size == 6 then
    unless (← isReal args[4]!) && (← isReal args[5]!) do
      reject e "coefficient arithmetic operands must have type Real"
    let a : Q(ℝ) := args[4]!
    let b : Q(ℝ) := args[5]!
    let canonical := if op == some ``HAdd.hAdd then q($a + $b)
      else if op == some ``HSub.hSub then q($a - $b)
      else if op == some ``HMul.hMul then q($a * $b) else q($a / $b)
    unless ← isDefEq e canonical do reject e "nonstandard real arithmetic instance"
    scalar args[4]!
    scalar args[5]!
    if op == some ``HDiv.hDiv then modify (·.push args[5]!)
    return ()
  if [``Neg.neg, ``Inv.inv].any (op == some ·) && args.size == 3 then
    unless ← isReal args[2]! do reject e "coefficient operand must have type Real"
    let a : Q(ℝ) := args[2]!
    let canonical := if op == some ``Neg.neg then q(-$a) else q($a⁻¹)
    unless ← isDefEq e canonical do reject e "nonstandard real unary operation"
    scalar args[2]!
    if op == some ``Inv.inv then modify (·.push args[2]!)
    return ()
  if e.isAppOfArity ``HPow.hPow 6 then
    if (← inferType args[5]!).isConstOf ``Real then
      let a : Q(ℝ) := args[4]!
      let p : Q(ℝ) := args[5]!
      unless ← isDefEq e q($a ^ $p) do reject e "nonstandard real power instance"
      scalar args[4]!
      scalar args[5]!
      let _ ← Coefficients.rootDegree args[5]!
      return ()
    unless (← inferType args[5]!).isConstOf ``Nat do
      reject e "coefficient exponent must be a natural literal or positive reciprocal root degree"
    let some exponent ← getNatValue? args[5]!
      | reject e "coefficient exponents must be natural literals"
    Hex.RealFormula.Reify.charge .exponent exponent
    unless ← isReal args[4]! do reject e "coefficient base must have type Real"
    let a : Q(ℝ) := args[4]!
    let n : Q(ℕ) := args[5]!
    unless ← isDefEq e q($a ^ $n) do reject e "nonstandard real power instance"
    return ← scalar args[4]!
  if [``OfNat.ofNat, ``Nat.cast, ``Int.cast, ``Rat.cast, ``RatCast.ratCast,
      ``OfScientific.ofScientific].any (op == some ·) then
    castGuards e
    let _ ← Hex.RealFormula.Reify.arithmetic #[] e
    return ()
  reject e "unsupported closed coefficient syntax"

private def checkInterval (source : Expr) : FrontendM Unit := do
  if let (``Membership.mem, #[_, _, _, set, _]) := source.getAppFnArgs then
    let (kind, args) := set.getAppFnArgs
    unless kind == ``Set.Ioc && args.size == 4 do
      reject source "only literal-dyadic Set.Ioc domains are supported"
    for endpoint in #[args[2]!, args[3]!] do
      unless isClosed endpoint do reject endpoint "interval endpoints must be literal dyadic rationals"
      let _ ← Hex.RealFormula.Reify.arithmetic #[] endpoint
      let eQ : Q(ℝ) := endpoint
      let ⟨q, _, _, _⟩ ← Mathlib.Meta.NormNum.deriveRat eQ (_inst := q(inferInstance))
      unless q.den == 2 ^ q.den.log2 do
        reject endpoint "interval endpoints must be literal dyadic rationals"

/-- Domain syntax is validated before substituting coefficient aliases. -/
private def checkDomains (source : Expr) : FrontendM Unit := do
  let _ ← Meta.transformWithCache source {} (pre := fun e => do
    checkInterval e
    return .continue) (skipInstances := true)

private def preflight (source : Expr) : FrontendM (Array Expr) := do
  let (_, divisors) ← (Meta.transformWithCache (m := StateRefT (Array Expr) FrontendM) source {} (pre := fun e => do
    if ← isReal e then
      if isClosed e then
        scalar e
        return .done e
      let (op, args) := e.getAppFnArgs
      if op == ``HDiv.hDiv && args.size == 6 then
        unless (← isReal args[4]!) && (← isReal args[5]!) do
          reject e "division operands must have type Real"
        let a : Q(ℝ) := args[4]!
        let b : Q(ℝ) := args[5]!
        unless ← isDefEq e q($a / $b) do reject e "nonstandard real division instance"
        unless isClosed args[5]! do reject e "division depending on the quantified variable"
        modify (·.push args[5]!)
      if op == ``Inv.inv then reject e "inversion depending on the quantified variable"
    return .continue) (skipInstances := true)).run #[]
  return divisors

private def normalize (source : Expr) : MetaM Expr :=
  Prod.fst <$> Meta.transformWithCache source {} (pre := fun e => do
    if isClosed e && (← isReal e) then return .done e
    if e.isAppOfArity ``HDiv.hDiv 6 && (← isReal e) then
      let args := e.getAppArgs
      let a : Q(ℝ) := args[4]!
      let b : Q(ℝ) := args[5]!
      return .continue (some q($a * $b⁻¹))
    return .continue) (skipInstances := true)

private def collect (source : Expr) : MetaM (Array Expr) := do
  let (_, (values, _)) ← (Meta.transformWithCache (m := StateRefT (Array Expr × ExprSet) MetaM) source {} (pre := fun e => do
    if isClosed e && (← isReal e) then
      let (values, seen) ← get
      unless seen.contains e do set (values.push e, seen.insert e)
      return .done e
    return .continue) (skipInstances := true)).run (#[], ({} : ExprSet))
  return values

private def withParameters (values : Array Expr) (i : Nat) (parameters : Array Expr)
    (k : Array Expr → MetaM α) : MetaM α := do
  if h : i < values.size then
    withLocalDeclD (Name.mkSimple s!"c{i}") (mkConst ``Real) fun p =>
      withParameters values (i + 1) (parameters.push p) k
  else k parameters
termination_by values.size - i

/-- Substitute only explicit checked real aliases, retaining the exact syntax
of their closed values and a proof back to the original proposition. -/
private def closeSource (source : Expr) : FrontendM (Expr × Expr) := do
  if source.hasMVar || source.hasLooseBVars then
    reject source "source sentence has unresolved metavariables"
  let mut closed := source
  let mut proof ← mkEqRefl source
  for id in (collectFVars {} source).fvarIds do
    let symbol := mkFVar id
    let some binding ← Hex.RCF.Reify.closeCoefficient? symbol
      | reject symbol "source parameter needs an explicit equality to a closed real value"
    let abstraction := mkLambda `coefficient .default (mkConst ``Real) (closed.abstract #[symbol])
    proof ← mkEqTrans proof (← mkAppM ``congrArg #[abstraction, binding.proof])
    closed := closed.replaceFVar symbol binding.value
  unless isClosed closed do reject source "source sentence has free parameters"
  checkWithKernel proof
  return (closed, proof)

private def prepareCore (original : Expr) (config : Hex.RealFormula.Reify.Config) : FrontendM Source := do
  let cap := (← get).budget.remaining.sourceNodes
  Hex.RealFormula.Reify.charge .sourceNodes (Hex.Reflect.sourceNodeCount original (cap + 1))
  checkDomains original
  let (source, aliasProof) ← closeSource original
  match source.consumeMData with
  | .forallE _ domain _ _ =>
      unless ← isDefEq domain (mkConst ``Real) do reject source "expected one real quantifier"
  | e =>
      unless e.isAppOfArity ``Exists 2 do reject source "expected one real quantifier"
  let cap := (← get).budget.remaining.sourceNodes
  Hex.RealFormula.Reify.charge .sourceNodes (Hex.Reflect.sourceNodeCount source (cap + 1))
  let divisors ← preflight source
  let normalized ← normalize source
  let coefficients ← collect normalized
  let state ← get
  let outcome ← liftM <| withParameters coefficients 0 #[] fun parameters =>
    ((do
      let replacements := (coefficients.zip parameters).foldl
        (fun m (e, p) => m.insert e p) ({} : ExprMap Expr)
      let abstracted := normalized.replace fun e => replacements[e]?
      let budget := { (← get).budget.remaining with
        exponent := config.ring.budget.exponent
        coefficientBits := config.ring.budget.coefficientBits }
      let result ← Hex.RealFormula.Reify.reify abstracted parameters #[]
        { config with ring := { config.ring with budget } }
      let result ← match result with
        | .error diagnostic => throwThe Hex.RealFormula.Reify.Error diagnostic.reason
        | .ok result => pure result
      for dimension in [Hex.Reflect.BudgetDimension.sourceNodes, .atoms, .reflectedNodes,
          .exponent, .terms, .coefficientBits, .proofNodes] do
        Hex.RealFormula.Reify.charge dimension (result.usage.get dimension)
      unless result.binders.size == 1 && result.prefixMap.size == 1 do
        reject source "expected exactly one real quantifier"
      let valuation ← Hex.RealFormula.Reify.valuation coefficients
      let specialized := mkApp result.proof valuation
      let normalizedProofType ← mkAppM ``Iff #[mkApp result.source valuation, source]
      let goal ← mkFreshExprMVar normalizedProofType
      let goals ← Lean.Elab.runTactic' goal.mvarId! (← `(tactic| (dsimp [Hex.RealFormula.append]; simp only [div_eq_mul_inv])))
      unless goals.isEmpty do
        throwThe Hex.RealFormula.Reify.Error (.internal "failed to reconstruct the original source")
      let sourceProof ← mkAppM ``Iff.trans #[specialized, ← instantiateMVars goal]
      let aliasIff ← mkAppM ``Iff.of_eq #[← mkEqSymm aliasProof]
      let proof ← instantiateMVars (← mkAppM ``Iff.trans #[sourceProof, aliasIff])
      let formula ← instantiateMVars result.formula
      let expected ← mkAppM ``Iff
        #[← mkAppM ``Hex.RealFormula.Prenex.toProp #[formula, valuation], original]
      unless ← isDefEq (← inferType proof) expected do
        throwThe Hex.RealFormula.Reify.Error (.internal "source specialization proof has the wrong target")
      if parameters.any (fun p => proof.containsFVar p.fvarId!) then
        throwThe Hex.RealFormula.Reify.Error (.internal "temporary coefficient escaped into proof")
      Hex.RealFormula.Reify.accountProof proof
      return {
        original, coefficients, divisors, formula
        valuation := ← instantiateMVars valuation
        proof, usage := (← get).budget.consumed } : FrontendM Source).run state).run
  match outcome with
  | .error e => throwThe Hex.RealFormula.Reify.Error e
  | .ok (result, state) =>
      -- Check after the temporary parameter scope has closed. Caller aliases
      -- remain legitimate hypotheses; generated coefficient locals do not.
      checkWithKernel result.proof
      set state
      return result

/-- Build a source schema for closed rational, real algebraic and π/e coefficient expressions.
Retain all original divisor obligations, including those beneath cancellation
and zero multiplication. This is frontend preparation only: guard discharge,
authenticated coefficient interpretation and decision replay are still required.
No optional tactic handler is installed by this module. Callers must synthesize
and instantiate source metavariables first (as the base tactic does).

Additive budgets bound cumulative charged work: original, alias-substituted and
shared-reifier source views are charged separately, as are the shared proof and
the final composed proof. They are not just bounds on the initial input size.
Exponent and coefficient-bit limits retain the shared maximum-limit semantics.

Unsupported syntax and
budget limits return structured errors. Unexpected elaboration/kernel errors and
Lean runtime failures remain terminal exceptions, with state restored; callers
must not reclassify them as solver declines. -/
def prepare (source : Expr) (config : Hex.RealFormula.Reify.Config := {}) : MetaM (Except Hex.RealFormula.Reify.Error Source) := do
  let saved ← saveState
  let (result, _) ← tryFinally'
    (do
      let outcome ← ((prepareCore source config).run
        { config, budget := .ofBudget config.ring.budget }).run
      return outcome.map Prod.fst)
    (fun result => do
      match result with
      | some (.ok _) =>
          modify fun state => { state with
            mctx := saved.meta.mctx
            postponed := saved.meta.postponed
            zetaDeltaFVarIds := saved.meta.zetaDeltaFVarIds }
      | _ => saved.restore)
  return result

end Hex.RCF.RealCoefficients.Reify
