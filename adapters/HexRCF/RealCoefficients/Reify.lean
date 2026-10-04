/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public meta import HexRealFormulaMathlib.Reify
public meta import HexRCF.Reify
public meta import HexRCF.Tactic
public meta import HexRCF.RealCoefficients.Registration
public meta import HexRCF.RealCoefficients.Interpret
public import HexRealAlgebraicMathlib.Basic
public import HexRCF.RealCoefficients.Conversion
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
original divisor expressions after checked alias substitution, interpreted in
ℝ for rational and supported real-algebraic carriers, before normalization.
This is pending frontend data, not an authenticated
coefficient environment or an accepted solver certificate. -/
structure Source where
  /-- Fully instantiated original goal, before division preprocessing or
  coefficient abstraction. -/
  original : Expr
  /-- Sentence after checked source lowering and division normalization. -/
  sentence : Expr
  /-- Ordinary-kernel equivalence between the lowered sentence and the source. -/
  sentenceProof : Expr
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
    unless isClosed d do reject e "division inside a literal cast must have a closed divisor"
    unless (← inferType d).isConstOf ``Rat do
      reject e "division inside a literal cast must be rational"
    let d : Q(ℚ) := d
    modify (·.push q(($d : ℝ)))
  for a in args do castGuards a

private partial def scalar (registered : Array Expr) (source : Expr) : ScanM Unit := do
  let e := source.consumeMData
  unless isClosed e do reject e "coefficient must be closed"
  if ← registered.anyM (fun value => liftM (Registration.sameSubject e value)) then
    -- A registered whole subject is admitted first, but its original field
    -- divisions are still source obligations, even inside analytic syntax.
    let _ ← Meta.transformWithCache e {} (pre := fun part => do
      let (op, args) := part.getAppFnArgs
      let divisor := if op == ``HDiv.hDiv && args.size == 6 then some args[5]!
        else if op == ``Inv.inv && args.size == 3 then some args[2]! else none
      if let some d := divisor then
        unless isClosed d do
          reject part "division inside a registered subject must have a closed divisor"
        if ← isReal d then modify (·.push d)
        else if (← inferType d).isConstOf ``Rat then
          let d : Q(ℚ) := d
          modify (·.push q(($d : ℝ)))
        else reject part "division inside a registered subject must be real or rational"
      return .continue) (skipInstances := true)
    return ()
  if e.isAppOfArity ``Hex.RealAlgebraicNumber.toReal 1 then
    -- Retain visible rational payload guards in both checked-constructor
    -- branches, including an unused fallback. Conversion does not erase them.
    let _ ← Meta.transformWithCache e.appArg! {} (pre := fun part => do
      if ← isProof part then return .done part
      if let some divisor ← Conversion.divisor? part then
        unless isClosed divisor do
          reject part "division in a converted coefficient must have a closed divisor"
        modify (·.push divisor)
      else
        let (op, args) := part.getAppFnArgs
        let divisor := if op == ``HDiv.hDiv && args.size == 6 then some args[5]!
          else if op == ``Inv.inv && args.size == 3 then some args[2]! else none
        if let some d := divisor then
          unless isClosed d do
            reject part "division in a converted coefficient must have a closed divisor"
          if (← inferType d).isConstOf ``Rat then
            let d : Q(ℚ) := d
            modify (·.push q(($d : ℝ)))
          else
            let ty ← inferType d
            if ty.isAppOfArity ``Hex.QAdjoin 1 then
              let generator := ty.appArg!
              if generator.isAppOfArity ``Hex.RealAlgebraicNumber.toAlgebraic 1 ||
                  generator.isAppOfArity ``Hex.AlgebraicNumber.ofReal 1 then
                let value ← mkAppM ``Coefficients.ofField #[generator.appArg!, d]
                modify (·.push (← mkAppM ``Hex.RealAlgebraicNumber.toReal #[value]))
              else reject part "division in a converted field requires a real generator"
            else reject part "division in a converted coefficient has an unsupported carrier"
        if op == ``HPow.hPow && args.size == 6 then
          if (← inferType args[5]!).isConstOf ``Int then
            reject part "integer powers in converted coefficients are unsupported"
        if [``Hex.RealAlgebraicNumber.intPow, ``Hex.AlgebraicNumber.intPow,
            ``Hex.PolyQuot.intPow].contains op then
          reject part "integer powers in converted coefficients are unsupported"
        if [``Hex.AlgebraicNumber.div, ``Hex.AlgebraicNumber.inv,
            ``Hex.PolyQuot.div, ``Hex.PolyQuot.inv].contains op then
          reject part "raw carrier division in converted coefficients is unsupported"
      if part.isAppOfArity ``Hex.RealAlgebraicNumber.ofRat 1 ||
          part.isAppOfArity ``Hex.AlgebraicNumber.ofRat 1 then
        let value : Q(ℚ) := part.appArg!
        castGuards value
        let _ ← Hex.RealFormula.Reify.arithmetic #[] q(($value : ℝ))
        return .done part
      return .continue) (skipInstances := true)
    return ()
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
    return ← scalar registered e.appArg!
  if e.isAppOfArity ``Real.rpow 2 then
    scalar registered args[0]!
    scalar registered args[1]!
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
    scalar registered args[4]!
    scalar registered args[5]!
    if op == some ``HDiv.hDiv then modify (·.push args[5]!)
    return ()
  if [``Neg.neg, ``Inv.inv].any (op == some ·) && args.size == 3 then
    unless ← isReal args[2]! do reject e "coefficient operand must have type Real"
    let a : Q(ℝ) := args[2]!
    let canonical := if op == some ``Neg.neg then q(-$a) else q($a⁻¹)
    unless ← isDefEq e canonical do reject e "nonstandard real unary operation"
    scalar registered args[2]!
    if op == some ``Inv.inv then modify (·.push args[2]!)
    return ()
  if e.isAppOfArity ``HPow.hPow 6 then
    if (← inferType args[5]!).isConstOf ``Real then
      unless ← isReal args[4]! do reject e "coefficient base must have type Real"
      let a : Q(ℝ) := args[4]!
      let p : Q(ℝ) := args[5]!
      unless ← isDefEq e q($a ^ $p) do reject e "nonstandard real power instance"
      scalar registered args[4]!
      scalar registered args[5]!
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
    return ← scalar registered args[4]!
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

private def preflight (registered : Array Expr) (source : Expr) : FrontendM (Array Expr) := do
  let (_, divisors) ← (Meta.transformWithCache (m := StateRefT (Array Expr) FrontendM) source {} (pre := fun e => do
    if ← isReal e then
      if isClosed e then
        scalar registered e
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

private partial def hasNamedSource (registered : Array Expr) (e : Expr) : MetaM Bool := do
  if (← registered.anyM (Registration.sameSubject e)) ||
      e.isAppOfArity ``Hex.RealAlgebraicNumber.toReal 1 ||
      e.isAppOfArity ``Real.sqrt 1 || e.isAppOfArity ``Real.rpow 2 ||
      e.isConstOf ``Real.pi || e.isAppOfArity ``Real.exp 1 then return true
  e.getAppArgs.anyM (hasNamedSource registered)

/-- Lower visible rational and checked algebraic constructors using their
proved interpretations, preserving exact registered whole subjects. -/
private partial def lowerCore (registered : Array Expr) (source : Expr) :
    StateRefT (Array Expr) MetaM Expr := do
  let (lowered, _) ← Meta.transformWithCache source {} (pre := fun e => do
    if ← registered.anyM (fun value => liftM (Registration.sameSubject e value)) then
      return .done e
    if ← isProof e then return .done e
    if let some (value, proof) ← Conversion.step? e then
      let expected ← mkAppM ``Eq #[e, value]
      unless ← isDefEq (← inferType proof) expected do
        throwError "rcf: source conversion has the wrong equality"
      let proof ← mkExpectedTypeHint proof expected
      modify (·.push proof)
      return .done (← lowerCore registered value)
    if isClosed e && e.isAppOfArity ``Hex.RealAlgebraicNumber.toReal 1 &&
        e.appArg!.isAppOfArity ``Hex.RealAlgebraicNumber.ofRat 1 then
      let value : Q(ℚ) := e.appArg!.appArg!
      return .done q(($value : ℝ))
    return .continue) (skipInstances := true)
  return lowered

/-- Lower visible constructor syntax, keeping registered whole subjects exact. -/
def lowerSources (registered : Array Expr) (source : Expr) : MetaM Expr :=
  Prod.fst <$> (lowerCore registered source).run #[]

private def addCasts (theorems : SimpTheorems := {}) : MetaM SimpTheorems := do
  let mut theorems := theorems
  for name in #[``Nat.cast_ofNat, ``Nat.cast_zero, ``Nat.cast_one, ``Int.cast_ofNat] do
    theorems ← theorems.addConst name
  return theorems

private def castGoals (goals : List MVarId) : MetaM (List MVarId) := do
  let context ← Simp.mkContext (simpTheorems := #[← addCasts])
    (congrTheorems := ← getSimpCongrTheorems)
  let mut remaining := []
  for id in goals do
    let (next, _) ← simpTarget id context
    if let some id := next then
      remaining := remaining ++
        (← Lean.Elab.runTactic' id (← `(tactic| try with_reducible rfl)))
  return remaining

private def lowerProof (source lowered : Expr) (proofs : Array Expr) : MetaM Expr := do
  if source == lowered then return ← mkEqRefl source
  let mut theorems : SimpTheorems := {}
  for proof in proofs do
    theorems ← theorems.add (.other (← mkFreshId)) #[] proof
  theorems ← addCasts (← theorems.addConst ``Hex.RealAlgebraicNumber.ofRat_toReal)
  let candidate ← mkFreshExprMVar (← mkEq source lowered)
  let context ← Simp.mkContext (simpTheorems := #[theorems])
    (congrTheorems := ← getSimpCongrTheorems)
  let (remaining, _) ← simpTarget candidate.mvarId! context
  if let some id := remaining then
    let goals ← Lean.Elab.runTactic' id (← `(tactic| try with_reducible rfl))
    unless goals.isEmpty do throwError "rcf: source lowering has no checked equality"
  return ← instantiateMVars candidate

/-- Exact checked constructor lowering, for proofs of original guards and aliases. -/
def lowerWithProof (registered : Array Expr) (source : Expr) : MetaM (Expr × Expr) := do
  let (lowered, proofs) ← (lowerCore registered source).run #[]
  return (lowered, ← lowerProof source lowered proofs)

/-- Replace variable-dependent division by multiplication with a closed
reciprocal. Original guards were collected before this conversion. -/
private def normalize (registered : Array Expr) (source : Expr) : MetaM Expr := do
  Prod.fst <$> Meta.transformWithCache source {} (pre := fun e => do
    if isClosed e && (← isReal e) then return .done e
    if e.isAppOfArity ``HDiv.hDiv 6 && (← isReal e) then
      let args := e.getAppArgs
      let a : Q(ℝ) := args[4]!
      let b : Q(ℝ) := args[5]!
      if ← hasNamedSource registered b then
        return .continue (some q($a * $b⁻¹))
      return .continue (some q($a * ((1 : ℝ) / $b)))
    return .continue) (skipInstances := true)

private def isNamedCoefficient (registered : Array Expr) (e : Expr) : MetaM Bool := do
  if e.isAppOfArity ``Hex.RealAlgebraicNumber.toReal 1 ||
      e.isAppOfArity ``Real.sqrt 1 || e.isAppOfArity ``Real.rpow 2 ||
      e.isConstOf ``Real.pi || e.isAppOfArity ``Real.exp 1 then return true
  if e.isAppOfArity ``Inv.inv 3 || e.isAppOfArity ``HDiv.hDiv 6 then
    return ← e.getAppArgs.anyM (hasNamedSource registered)
  if e.isAppOfArity ``HPow.hPow 6 then
    return (← inferType e.getAppArgs[5]!).isConstOf ``Real
  return false

/-- Abstract named algebraic inputs, leaving rational arithmetic to the
shared polynomial reifier. Thus `2 * sqrt 2` uses the same one-dimensional
field as `sqrt 2`, rather than creating another unrelated coefficient. -/
private def collect (registered : Array Expr) (source : Expr) : MetaM (Array Expr) := do
  let (_, (values, _)) ← (Meta.transformWithCache (m := StateRefT (Array Expr × ExprSet) MetaM) source {} (pre := fun e => do
    if isClosed e && (← isReal e) && ((← registered.anyM (fun value => liftM (Registration.sameSubject e value))) || (← isNamedCoefficient registered e)) then
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

private def prepareCore (registered : Array Expr) (original : Expr) (config : Hex.RealFormula.Reify.Config) : FrontendM Source := do
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
  let divisors ← preflight registered source
  let (rationalized, conversions) ← liftM ((lowerCore registered source).run #[])
  let lowering ← liftM (lowerProof source rationalized conversions)
  if rationalized != source then Hex.RealFormula.Reify.accountProof lowering
  if rationalized != source then
    -- A known zero guard is terminal before the shared reifier can turn its
    -- rational denominator into a syntax decline. Other guards remain for the
    -- consuming handler, including unresolved algebraic/registered signs.
    for divisor in divisors do
      let divisor : Q(ℝ) ← lowerSources registered divisor
      let outcome ← liftM (do
        let saved ← saveState
        try
          let recognized ← (do
            try
              let ⟨value, _, _, proof⟩ ← Mathlib.Meta.NormNum.deriveRat divisor
                (_inst := q(inferInstance))
              pure (some (value, ← instantiateMVars proof))
            catch _ => pure none : MetaM (Option (Rat × Expr)))
          if let some (_, proof) := recognized then checkWithKernel proof
          return recognized
        finally saved.restore : MetaM (Option (Rat × Expr)))
      if let some (value, proof) := outcome then
        Hex.RealFormula.Reify.accountProof proof
        if value == 0 then throwError "rcf: original closed divisor is zero"
  let normalized ← normalize registered rationalized
  let coefficients ← collect registered normalized
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
      let normalizedProofType ← mkAppM ``Iff #[mkApp result.source valuation, rationalized]
      let goal ← mkFreshExprMVar normalizedProofType
      let goals ← Lean.Elab.runTactic' goal.mvarId!
        (← `(tactic| (dsimp [Hex.RealFormula.append]; simp only
          [div_eq_mul_inv, one_mul, Hex.RealAlgebraicNumber.ofRat_toReal])))
      let remaining ← castGoals goals
      unless remaining.isEmpty do
        throwThe Hex.RealFormula.Reify.Error (.internal
          s!"failed to reconstruct the original source: {← ppExpr (← remaining[0]!.getType)}")
      let aliasIff ← mkAppM ``Iff.of_eq #[← mkEqSymm aliasProof]
      let loweringIff ← mkAppM ``Iff.of_eq #[← mkEqSymm lowering]
      let sourceIff ← mkAppM ``Iff.trans #[loweringIff, aliasIff]
      let reflectedProof ← instantiateMVars
        (← mkAppM ``Iff.trans #[← instantiateMVars goal, sourceIff])
      let sentence := normalized
      let sentenceMatch ← mkFreshExprMVar
        (← mkAppM ``Iff #[sentence, mkApp result.source valuation])
      let sourceGoals ← Lean.Elab.runTactic' sentenceMatch.mvarId!
        (← `(tactic| try dsimp [Hex.RealFormula.append]))
      let sourceGoals ← castGoals sourceGoals
      unless sourceGoals.isEmpty do
        throwThe Hex.RealFormula.Reify.Error (.internal
          "lowered sentence differs from the reflected source")
      let sentenceProof ← instantiateMVars
        (← mkAppM ``Iff.trans #[← instantiateMVars sentenceMatch, reflectedProof])
      let sentenceType ← mkAppM ``Iff #[sentence, original]
      unless ← isDefEq (← inferType sentenceProof) sentenceType do
        throwThe Hex.RealFormula.Reify.Error (.internal "lowered sentence equivalence has the wrong target")
      let proof ← instantiateMVars (← mkAppM ``Iff.trans #[specialized, reflectedProof])
      let formula ← instantiateMVars result.formula
      let expected ← mkAppM ``Iff
        #[← mkAppM ``Hex.RealFormula.Prenex.toProp #[formula, valuation], original]
      unless ← isDefEq (← inferType proof) expected do
        throwThe Hex.RealFormula.Reify.Error (.internal "source specialization proof has the wrong target")
      if parameters.any (fun p => proof.containsFVar p.fvarId! ||
          sentenceProof.containsFVar p.fvarId!) then
        throwThe Hex.RealFormula.Reify.Error (.internal "temporary coefficient escaped into proof")
      Hex.RealFormula.Reify.accountProof sentenceProof
      Hex.RealFormula.Reify.accountProof proof
      return {
        original, sentence, sentenceProof, coefficients, divisors, formula
        valuation := ← instantiateMVars valuation
        proof, usage := (← get).budget.consumed } : FrontendM Source).run state).run
  match outcome with
  | .error e => throwThe Hex.RealFormula.Reify.Error e
  | .ok (result, state) =>
      -- Check after the temporary parameter scope has closed. Caller aliases
      -- remain legitimate hypotheses; generated coefficient locals do not.
      checkWithKernel result.proof
      checkWithKernel result.sentenceProof
      set state
      return result

/-- Recover all original divisor obligations after checked alias substitution.
This reuses source preflight without coefficient lowering, schema construction
or root/sign production. Successful results preserve caller metavariables. -/
def guards (original : Expr) (config : Hex.RealFormula.Reify.Config := {}) :
    MetaM (Except Hex.RealFormula.Reify.Error (Array Expr)) := do
  let saved ← saveState
  let (result, _) ← tryFinally' (withNewMCtxDepth do
      let action : FrontendM (Array Expr) := do
        checkDomains original
        let (source, proof) ← closeSource original
        let _ ← liftM (Hex.RCF.checkProof `Hex.RCF.RealCoefficients.Reify.guards
          (← inferType proof) proof)
        preflight #[] source
      let outcome ← (action.run {config, budget := .ofBudget config.ring.budget}).run
      match outcome with
      | .error error => return .error error
      | .ok (divisors, _) => return .ok (← divisors.mapM instantiateMVars))
    (fun result => do
      match result with
      | some (.ok _) => modify fun state => {state with
          mctx := saved.meta.mctx, postponed := saved.meta.postponed,
          zetaDeltaFVarIds := saved.meta.zetaDeltaFVarIds}
      | _ => saved.restore)
  return result

/-- Build a source schema for closed rational, real algebraic, π/e and explicitly
supplied registered subjects. The latter are pending frontend coordinates;
their caller must authenticate containment and any original internal guards.
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
budget limits return structured errors. A known zero original divisor exposed
by checked constructor lowering raises a terminal input error before schema
construction. Unexpected elaboration/kernel errors and
Lean runtime failures remain terminal exceptions, with state restored; callers
must not reclassify them as solver declines. -/
def prepare (source : Expr) (config : Hex.RealFormula.Reify.Config := {})
    (registered : Array Expr := #[]) : MetaM (Except Hex.RealFormula.Reify.Error Source) := do
  profileitM Exception "rcf source preparation" (← getOptions) do
    let saved ← saveState
    let (result, _) ← tryFinally'
      (do
        let outcome ← ((prepareCore registered source config).run
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
