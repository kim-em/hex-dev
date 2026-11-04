/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public meta import HexRCF.RealCoefficients.Reify
public meta import HexRCF.RealCoefficients.Replay
public meta import HexRCF.RealCoefficients.FieldLiteral
public meta import HexRCF.RealCoefficients.FiniteLiteral
public meta import HexRCF.RealCoefficients.FieldCompile
public meta import HexRCF.RealCoefficients.FieldRuntime
public meta import HexRCF.Tactic

public meta section

/-! Authenticated fixed-field frontend data before goal certificate production. -/

namespace Hex.RCF.RealCoefficients.Coefficients
open Hex Lean Meta Qq

/-- Fixed-field coordinates in original coefficient order, with ordinary-kernel
source identities and all original divisor proofs. This is prepared frontend
input, not a verdict or a checked root/cell certificate. The native field
instance supports search; no expression quoting its proof is required. Expressions
remain in the source's local context. -/
structure Coordinates where
  source : Reify.Source
  polynomial : ZPoly
  square : DyadicSquare
  witness : atomWitness polynomial square
  precision : (mahlerPrec polynomial : Int) ≤ square.prec
  checked : ZPoly.CheckedIrreducible polynomial
  arity : Nat
  values : Fin arity → PolyQuot polynomial
    (SimpleRoot.ofSquare polynomial square witness precision)
  formula : RealFormula.QF (arity + 1)
  quantifier : RealFormula.Quantifier
  polynomialExpr : Expr
  rootExpr : Expr
  valuesExpr : Expr
  formulaExpr : Expr
  /-- Equality between interpreted coordinates and `source.valuation`. -/
  valuationProof : Expr
  /-- Proofs of nonvanishing for `source.divisors`, in the original order. -/
  divisorProofs : Array Expr
  /-- The same divisors as fixed-field coordinates, before cancellation. -/
  divisors : List (PolyQuot polynomial
    (SimpleRoot.ofSquare polynomial square witness precision))
  divisorExpressions : Array Expr
  /-- Coordinate interpretation equals the corresponding original divisor. -/
  divisorIdentities : Array Expr

/-- Legacy prepared input additionally retains a quoted global field proof.
Its public methods validate that proof independently of finite source evidence. -/
structure Environment extends Coordinates where
  irreducibleExpr : Expr

namespace Coordinates

private meta def closed (expression : Expr) : MetaM Expr := do
  let expression ← instantiateMVars expression
  if expression.hasMVar then throwError "rcf: prepared environment contains unresolved metavariables"
  Hex.RCF.checkExpr `Hex.RCF.RealCoefficients.Coefficients.Coordinates.input expression

/-- Instantiate all expression data before discarding temporary frontend state.
Unresolved data cannot be assigned while accepting an externally supplied proof. -/
meta def instantiate (prepared : Coordinates) : MetaM Coordinates := do
  let source := prepared.source
  let source := {source with
    original := ← closed source.original
    sentence := ← closed source.sentence
    sentenceProof := ← closed source.sentenceProof
    coefficients := ← source.coefficients.mapM closed
    divisors := ← source.divisors.mapM closed
    formula := ← closed source.formula
    valuation := ← closed source.valuation
    proof := ← closed source.proof}
  return {prepared with
    source
    polynomialExpr := ← closed prepared.polynomialExpr
    rootExpr := (← closed prepared.rootExpr).consumeMData
    valuesExpr := ← closed prepared.valuesExpr
    formulaExpr := ← closed prepared.formulaExpr
    valuationProof := ← closed prepared.valuationProof
    divisorProofs := ← prepared.divisorProofs.mapM closed
    divisorExpressions := ← prepared.divisorExpressions.mapM closed
    divisorIdentities := ← prepared.divisorIdentities.mapM closed}

private meta def restoreOnFailure (action : MetaM α) : MetaM α := do
  let saved ← saveState
  let (result, _) ← tryFinally' (withNewMCtxDepth <| withOptions (fun options =>
      debug.skipKernelTC.set (Elab.async.set options false) false) action)
    (fun result => do
      match result with
      | some _ => modify fun state => {state with
          mctx := saved.meta.mctx, postponed := saved.meta.postponed,
          zetaDeltaFVarIds := saved.meta.zetaDeltaFVarIds}
      | none => saved.restore)
  return result

/-- Bind runtime proposal inputs to their stored source expressions before a
native diagnostic verdict. Acceptance still requires the ordinary kernel. -/
private meta def checkBindings (prepared : Coordinates) : MetaM Unit := do
  unless (← FieldRuntime.evalZPoly prepared.polynomialExpr) == prepared.polynomial do
    throwError "rcf: invalid prepared polynomial binding"
  let root := prepared.rootExpr.consumeMData
  unless root.isAppOfArity ``SimpleRoot.ofSquare 4 do
    throwError "rcf: invalid prepared selected-root expression"
  let args := root.getAppArgs
  unless (← FieldRuntime.evalZPoly args[0]!) == prepared.polynomial &&
      (← FieldRuntime.evalSquare args[1]!) == prepared.square do
    throwError "rcf: invalid prepared selected-root binding"
  let source ← FieldRuntime.evalFormula prepared.arity prepared.source.formula
  unless source == .quant prepared.quantifier (.matrix prepared.formula) do
    throwError "rcf: invalid prepared sentence binding"
  let matrix ← mkAppM ``RealFormula.Prenex.matrix #[prepared.formulaExpr]
  unless (← FieldRuntime.evalFormula (prepared.arity + 1) matrix) ==
      .matrix prepared.formula do
    throwError "rcf: invalid prepared matrix binding"
  let polynomialType : Q(Type) := q(DensePoly Rat)
  let values ← withLetDecl `coordinates (← inferType prepared.valuesExpr) prepared.valuesExpr fun values => do
    let coordinates ← (List.finRange prepared.arity).mapM fun i => do
      let bound ← mkDecideProof (← mkLt (mkNatLit i.val) (mkNatLit prepared.arity))
      let index ← mkAppM ``Fin.mk #[mkNatLit i.val, bound]
      mkAppM ``PolyQuot.coeffs #[mkApp values index]
    mkLetFVars #[values] (← mkListLit polynomialType coordinates)
  unless (← FieldRuntime.evalRatPolys values) ==
      (List.finRange prepared.arity).map (fun i => (prepared.values i).coeffs) do
    throwError "rcf: invalid prepared coefficient binding"
  let divisors ← prepared.divisorExpressions.toList.mapM fun expression =>
    mkAppM ``PolyQuot.coeffs #[expression]
  unless (← FieldRuntime.evalRatPolys (← mkListLit polynomialType divisors)) ==
      prepared.divisors.map (·.coeffs) do
    throwError "rcf: invalid prepared divisor binding"

/-- Bind runtime input to its expressions and authenticate required source,
field, valuation and original-divisor proofs before any production shortcut. -/
meta def checkDomains (prepared : Coordinates)
    (owner : Name := `Hex.RCF.RealCoefficients.Coefficients.Coordinates) : MetaM Unit :=
    restoreOnFailure do
  let prepared ← prepared.instantiate
  prepared.checkBindings
  let .ok original ← Reify.guards prepared.source.original |
    throwError "rcf: prepared environment has an invalid original source"
  unless original.size == prepared.source.divisors.size do
    throwError "rcf: prepared coefficient environment omitted an original divisor"
  for i in [:original.size] do
    unless original[i]! == prepared.source.divisors[i]! do
      throwError "rcf: prepared divisor differs from the original source"
  unless prepared.divisorProofs.size == prepared.source.divisors.size &&
      prepared.divisors.length == prepared.source.divisors.size &&
      prepared.divisorExpressions.size == prepared.source.divisors.size &&
      prepared.divisorIdentities.size == prepared.source.divisors.size do
    throwError "rcf: prepared coefficient environment omitted an original divisor"
  let sentence ← mkAppM ``RealFormula.Prenex.toProp
    #[prepared.source.formula, prepared.source.valuation]
  let _ ← withoutModifyingEnv <| Hex.RCF.checkProof
    (owner ++ `source)
    (← mkAppM ``Iff #[sentence, prepared.source.original]) prepared.source.proof
  let rep ← mkAppM ``Field.literalRep prepared.rootExpr.getAppArgs
  let interpreted ← withLocalDeclD `i (mkApp (mkConst ``Fin) (mkNatLit prepared.arity)) fun i => do
    mkLambdaFVars #[i] (← mkAppM ``Field.value #[rep, mkApp prepared.valuesExpr i])
  let _ ← withoutModifyingEnv <| Hex.RCF.checkProof
    (owner ++ `valuation)
    (← mkEq interpreted prepared.source.valuation) prepared.valuationProof
  for i in [:prepared.source.divisors.size] do
    let divisor : Q(ℝ) := prepared.source.divisors[i]!
    let proof := prepared.divisorProofs[i]!
    let _ ← withoutModifyingEnv <| Hex.RCF.checkProof
      (owner ++ `guard) q($divisor ≠ 0) proof
    let identity := prepared.divisorIdentities[i]!
    let interpreted ← mkAppM ``Field.value #[rep, prepared.divisorExpressions[i]!]
    let _ ← withoutModifyingEnv <| Hex.RCF.checkProof
      (owner ++ `identity)
      (← mkEq interpreted divisor) identity

/-- Compose a checked fixed-field sentence proof with authenticated source
coefficients and the original-goal equivalence. Check the complete proof and
its original target, including every transitive axiom dependency. -/
private meta def compose (prepared : Coordinates) (fixed : Expr) : MetaM Expr := do
  let fixed ← closed fixed
  let prepared ← prepared.instantiate
  let source := prepared.source
  let congr ← withLocalDeclD `ρ (← inferType source.valuation) fun ρ => do
    let body ← mkAppM ``Hex.RealFormula.Prenex.toProp #[source.formula, ρ]
    mkAppM ``congrArg #[← mkLambdaFVars #[ρ] body, prepared.valuationProof]
  let specialized ← mkAppM ``Eq.mp #[congr, fixed]
  let proof ← mkAppM ``Iff.mp #[source.proof, specialized]
  Hex.RCF.checkProof `Hex.RCF.RealCoefficients.Coefficients.Coordinates.transport
    source.original proof

/-- Transport only after checking all original domain obligations. -/
meta def transport (prepared : Coordinates) (fixed : Expr) : MetaM Expr := restoreOnFailure do
  prepared.checkDomains
  prepared.compose fixed

/-- Reuse an original divisor proof while compiling the same closed source.
The equality between its stored coordinate and the proposed denominator is
checked in the final proof; no additional sign search or inverse law is used. -/
meta def nonzero (prepared : Coordinates)
    (value : FieldCompile.Result prepared.polynomial
      (SimpleRoot.ofSquare prepared.polynomial prepared.square prepared.witness prepared.precision)) :
    MetaM Expr := do
  for (divisor, i) in prepared.divisors.zipIdx do
    if divisor = value.value then
      let some expression := prepared.divisorExpressions[i]? |
        throwError "rcf: missing prepared divisor expression"
      let some identity := prepared.divisorIdentities[i]? |
        throwError "rcf: missing prepared divisor identity"
      let some guard := prepared.divisorProofs[i]? |
        throwError "rcf: missing prepared divisor proof"
      let some original := prepared.source.divisors[i]? |
        throwError "rcf: missing original divisor"
      let rep ← mkAppM ``Field.literalRep prepared.rootExpr.getAppArgs
      let equality ← mkDecideProof (← mkEq value.expression expression)
      let interpretation ← withLocalDeclD `a (← inferType expression) fun a => do
        mkLambdaFVars #[a] (← mkAppM ``Field.value #[rep,a])
      let same ← mkEqTrans (← mkAppM ``congrArg #[interpretation,equality]) identity
      let read : Q(ℝ) ← mkAppM ``Field.value #[rep,value.expression]
      let original : Q(ℝ) ← pure original
      let same : Q($read = $original) ← pure same
      let guard : Q($original ≠ 0) ← pure guard
      return q(fun h : $read = 0 => $guard (Eq.trans (Eq.symm $same) h))
  throwError "rcf: arithmetic denominator is absent from the original divisor inventory"

/-- Produce a finite real-cell proof and compose it with the authenticated
source. Native search uses the actual field; quotation uses finite guards.
Every original divisor is checked before production or a false verdict. -/
meta def prove (prepared : Coordinates) : MetaM Expr := restoreOnFailure do
  prepared.checkDomains
  let _ : ZPoly.CheckedIrreducible prepared.polynomial := prepared.checked
  let fixed ← FiniteLiteral.prove prepared.polynomialExpr prepared.rootExpr
    prepared.valuesExpr prepared.formulaExpr prepared.values prepared.formula
    prepared.quantifier prepared.divisors
  prepared.compose fixed

end Coordinates

namespace Environment

private meta def closed := Coordinates.closed
private meta def restoreOnFailure (action : MetaM α) : MetaM α :=
  Coordinates.restoreOnFailure action

/-- Instantiate inherited source data and the additional legacy proof. -/
meta def instantiate (prepared : Environment) : MetaM Environment := do
  let coordinates ← prepared.toCoordinates.instantiate
  return {
    toCoordinates := coordinates
    irreducibleExpr := ← closed prepared.irreducibleExpr
  }

/-- Preserve the legacy global certificate check alongside all source guards. -/
meta def checkDomains (prepared : Environment) : MetaM Unit := restoreOnFailure do
  let prepared ← prepared.instantiate
  prepared.toCoordinates.checkDomains `Hex.RCF.RealCoefficients.Coefficients.Environment
  let _ ← withoutModifyingEnv <| Hex.RCF.checkProof
    `Hex.RCF.RealCoefficients.Coefficients.Environment.irreducible
    (← mkAppM ``ZPoly.CheckedIrreducible #[prepared.polynomialExpr]) prepared.irreducibleExpr

private meta def compose (prepared : Environment) (fixed : Expr) : MetaM Expr :=
  prepared.toCoordinates.compose fixed

/-- Transport after validating the additional legacy proof and all guards. -/
meta def transport (prepared : Environment) (fixed : Expr) : MetaM Expr := restoreOnFailure do
  prepared.checkDomains
  prepared.compose fixed

/-- Use the existing bounded producer and literal quotation on prepared data.
The editable environment is revalidated before search; failures remain
terminal and do not change the selected coefficient field. -/
meta def prove (prepared : Environment) : MetaM Expr := restoreOnFailure do
  prepared.checkDomains
  let _ : ZPoly.CheckedIrreducible prepared.polynomial := prepared.checked
  let instType ← mkAppM ``ZPoly.CheckedIrreducible #[prepared.polynomialExpr]
  let fixed ← withLocalDecl `inst .instImplicit instType fun inst => do
    let result ← FieldLiteral.proveRefining prepared.polynomialExpr prepared.rootExpr
      prepared.valuesExpr prepared.formulaExpr prepared.values prepared.formula prepared.quantifier
    return mkApp (← mkLambdaFVars #[inst] result) prepared.irreducibleExpr
  prepared.compose fixed

/-- Exercise the public finite build/check interface on prepared source data.
The quoted proof contains frozen certificate literals and `Replay.check_sound`;
production and field/root searches are absent from the proof term. This explicit
API quotes its finite checker with one kernel decision and linear table lookup. -/
private meta def replayWith (prepared : Environment) (totalProduction : Bool) :
    MetaM Expr := restoreOnFailure do
  prepared.checkDomains
  let _ : ZPoly.CheckedIrreducible prepared.polynomial := prepared.checked
  if real : prepared.square.meetsRealAxis = true then
    let input : Replay.Input prepared.polynomial prepared.square prepared.witness
        prepared.precision Unit prepared.arity :=
      ⟨prepared.values, prepared.formula, prepared.quantifier, prepared.divisors, ()⟩
    let options ← getOptions
    Core.checkInterrupted
    let depth := FieldLiteral.rcf.algebraic.directDepth.get options
    let result := if totalProduction then Replay.buildTotal input real depth
      else Replay.build input real depth (FieldLiteral.rcf.algebraic.maxDoublings.get options)
        (FieldLiteral.rcf.algebraic.monicCore.get options)
    let cert ← match result with
      | .error .divisor => throwError "rcf: original prepared divisor is zero"
      | .error (.search .exhausted) =>
          throwError "rcf: prepared finite search exhausted; increase rcf.algebraic.maxDoublings"
      | .error (.search .invalidReplay) =>
          throwError "rcf: prepared finite production failed evidence replay"
      | .error (.replay error) =>
          throwError "rcf: prepared finite production failed replay: {repr error}"
      | .ok cert => pure cert
    Core.checkInterrupted
    match Replay.check input cert with
    | .ok false => throwError "rcf: the prepared finite sentence is false"
    | .error error => throwError "rcf: prepared finite replay failed: {repr error}"
    | .ok true => pure ()
    let instType ← mkAppM ``ZPoly.CheckedIrreducible #[prepared.polynomialExpr]
    let fixed ← withLocalDecl `inst .instImplicit instType fun inst => do
      let data ← FieldLiteral.resultExpr prepared.polynomialExpr prepared.rootExpr
        prepared.formulaExpr prepared.formula cert.data
      let elem ← mkAppM ``PolyQuot #[prepared.polynomialExpr, prepared.rootExpr]
      let divisors ← mkListLit elem prepared.divisorExpressions.toList
      let quantifier := mkConst (match prepared.quantifier with
        | .forallReal => ``RealFormula.Quantifier.forallReal
        | .existsReal => ``RealFormula.Quantifier.existsReal)
      let inputExpr ← mkAppM ``Replay.Input.mk #[prepared.valuesExpr, prepared.formulaExpr,
        quantifier, divisors, mkConst ``Unit.unit]
      let certificate ← mkAppM ``Replay.Certificate.mk #[inputExpr, data]
      let checked : Q(Except Replay.Error Bool) ← mkAppM ``Replay.check #[inputExpr, certificate]
      let candidate ← mkFreshExprMVar (q($checked = .ok true) : Q(Prop))
      let lemmas ← FieldLiteral.evidenceLemmas
      let remaining ← withOptions (fun opts =>
          debug.skipKernelTC.set (Elab.async.set opts false) false) do
        Lean.Elab.runTactic' candidate.mvarId! (← `(tactic|
          (simp only [Replay.check, Replay.Input.matches_self, Bool.not_true,
            Bool.false_eq_true, ite_false, Replay.Input.value,
            FieldBuild.Result.checkFinite, FieldBuild.Result.recorded,
            FieldBuild.Result.allValue, FieldBuild.Result.anyValue,
            $lemmas,*]; decide +kernel)))
      unless remaining.isEmpty do
        throwError "rcf: prepared finite replay did not prove its accepted verdict"
      let accepted ← instantiateMVars candidate
      let proof ← mkAppM ``Replay.check_sound #[inputExpr, certificate, accepted]
      return mkApp (← mkLambdaFVars #[inst] proof) prepared.irreducibleExpr
    prepared.compose fixed
  else throwError "rcf: prepared square does not select a real field"

/-- Quote a bounded finite certificate and transport it to the original goal.
False and exhausted verdicts remain terminal. -/
meta def proveReplay (prepared : Environment) : MetaM Expr := prepared.replayWith false

/-- Use the total exact-field producer after source/guard authentication, then
quote only its finite evidence and compose to the original goal. This explicit
API retains the tactic's bounded default and does not make source recognition
or common-field irreducibility quotation complete. -/
meta def proveTotalReplay (prepared : Environment) : MetaM Expr := prepared.replayWith true

end Environment
end Hex.RCF.RealCoefficients.Coefficients
