/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public meta import HexRCF.RealCoefficients.Tactic
public meta import HexRCF.RealCoefficients.SquareRoot
public meta import HexRCF.RealCoefficients.CommonPresentation
public meta import HexBerlekampZassenhaus.QuadraticNormRecover

public meta section

/-! Checked common-field proposals for independent radical coefficients. -/

namespace Hex.RCF.RealCoefficients.CommonTactic

open Hex Lean Meta Qq

private meta def naturalSquareRoot? (source : Expr) : MetaM (Option Nat) := do
  unless source.isAppOfArity ``Real.sqrt 1 do return none
  let base : Q(ℝ) := source.appArg!
  let result ← observing? do
    let ⟨value, _, _, _⟩ ← Mathlib.Meta.NormNum.deriveRat base
      (_inst := q(inferInstance))
    pure value
  let some value := result | return none
  unless value.den == 1 && 0 < value.num do return none
  let n := value.num.toNat
  let nExpr : Q(ℕ) := mkNatLit n
  unless ← isDefEq base q(($nExpr : ℝ)) do return none
  return some n

private partial def sourceAtoms (e : Expr) (seen : Array Expr) : Array Expr :=
  if e.isAppOfArity ``Real.sqrt 1 ||
      e.isAppOfArity ``RealAlgebraicNumber.toReal 1 then
    if seen.contains e then seen else seen.push e
  else
    match e with
    | .app fn arg => sourceAtoms arg (sourceAtoms fn seen)
    | .forallE _ type body _ | .lam _ type body _ =>
        sourceAtoms body (sourceAtoms type seen)
    | .letE _ type value body _ =>
        sourceAtoms body (sourceAtoms value (sourceAtoms type seen))
    | .mdata _ body | .proj _ _ body => sourceAtoms body seen
    | _ => seen

private inductive SourceKind where
  | radical (degree : Nat)
  | selected (args : Array Expr)
  deriving Inhabited

private structure SourcePlan where
  anchorReal : Expr
  anchorValue : RealAlgebraicNumber
  sourcePolynomial : ZPoly
  sourceSquare : DyadicSquare
  field : DensePoly Rat
  fieldExpr : Expr
  /-- `realPoly field` at the selected anchor equals the original scalar. -/
  sourceProof : Expr
  kind : SourceKind

private instance : Inhabited SourcePlan where
  default := ⟨default, RealAlgebraicNumber.ofRat 0,
    DensePoly.ofList [], ⟨0, 0, 0⟩,
    DensePoly.ofList [], default, default, .radical 1⟩

private meta def unfoldHead? (e : Expr) (predicate : Expr → Bool) : MetaM (Option Expr) := do
  let mut current := e
  for _ in [:8] do
    if predicate current then return some current
    let some next ← withTransparency .default (unfoldDefinition? current) |
      return none
    current := next
  return none

private meta def selectedArgs? (e : Expr) : MetaM (Option (Array Expr)) := do
  let some selected ← unfoldHead? e (·.isAppOfArity ``Selected.real 10) |
    return none
  return some selected.getAppArgs

private meta def fieldArgs? (e : Expr) : MetaM (Option (Bool × Expr × Expr)) := do
  let some field ← unfoldHead? e (fun x =>
      x.isAppOfArity ``Selected.field 11 ||
        x.isAppOfArity ``Coefficients.ofField 2) | return none
  if field.isAppOfArity ``Selected.field 11 then
    let args := field.getAppArgs
    let generator ← mkAppM ``Selected.real (args.extract 0 10)
    return some (true, generator, args[10]!)
  let args := field.getAppArgs
  return some (false, args[0]!, args[1]!)

private meta def coefficientProof (value expression : Expr) : MetaM Expr := do
  let goal ← mkAppM ``Eq #[value, expression]
  let candidate ← mkFreshExprMVar goal
  let remaining ← Lean.Elab.runTactic' candidate.mvarId! (← `(tactic| decide +kernel))
  unless remaining.isEmpty do
    throwError "rcf: source field coefficients differ from their literal encoding"
  return ← instantiateMVars candidate

private meta def sourcePlan? (source : Expr) : MetaM (Option SourcePlan) := do
  let identity : DensePoly Rat := DensePoly.ofList [0, 1]
  if let some degree ← naturalSquareRoot? source then
    let (_, _, anchorValue) ← FieldRuntime.coefficient source
    let fieldExpr ← FieldLiteral.ratPolyExpr identity
    let sourceProof ← mkAppM ``CommonPresentation.generator_eval #[source]
    return some ⟨source, anchorValue,
      anchorValue.toAlgebraic.p, anchorValue.toAlgebraic.rep.1.square,
      identity, fieldExpr, sourceProof,
      .radical degree⟩
  unless source.isAppOfArity ``RealAlgebraicNumber.toReal 1 do return none
  let argument := source.appArg!
  if let some args ← selectedArgs? argument then
    let anchorValue ← FieldRuntime.evalReal argument
    let anchorReal ← mkAppM ``RealAlgebraicNumber.toReal #[argument]
    let fieldExpr ← FieldLiteral.ratPolyExpr identity
    let sourceProof ← mkAppM ``CommonPresentation.generator_eval #[anchorReal]
    let sourceP ← FieldRuntime.evalZPoly args[0]!
    let sourceSquare ← FieldRuntime.evalSquare args[1]!
    return some ⟨anchorReal, anchorValue, sourceP, sourceSquare,
      identity, fieldExpr, sourceProof,
      .selected args⟩
  let some (isSelectedField, anchorExpr, fieldValue) ← fieldArgs? argument | return none
  let some args ← selectedArgs? anchorExpr | return none
  let anchorValue ← FieldRuntime.evalReal anchorExpr
  let anchorReal ← mkAppM ``RealAlgebraicNumber.toReal #[anchorExpr]
  let coeffs ← mkAppM ``PolyQuot.coeffs #[fieldValue]
  let field ← FieldRuntime.evalRatPoly coeffs
  let fieldExpr ← FieldLiteral.ratPolyExpr field
  -- `ofNormalized_p` exposes the generator polynomial as constructor data,
  -- so this reduces field arithmetic without replaying root isolation.
  let hcoeff ← coefficientProof coeffs fieldExpr
  let sourceProof ← if isSelectedField then
    mkAppM ``Selected.field_eval
      #[args[0]!, args[1]!, args[2]!, args[3]!, args[4]!,
        args[5]!, args[6]!, args[7]!, args[8]!, args[9]!,
        fieldValue, fieldExpr, hcoeff]
  else do
    let sourceValue ← mkAppM ``CommonPresentation.ofField_eval
      #[anchorExpr, fieldValue, fieldExpr, hcoeff]
    mkAppM ``Eq.symm #[sourceValue]
  let sourceP ← FieldRuntime.evalZPoly args[0]!
  let sourceSquare ← FieldRuntime.evalSquare args[1]!
  return some ⟨anchorReal, anchorValue, sourceP, sourceSquare,
    field, fieldExpr, sourceProof,
    .selected args⟩

private def oneQuantifier {n : Nat} (formula : RealFormula.Prenex n) :
    Option (RealFormula.Quantifier × RealFormula.QF (n + 1)) :=
  match formula with
  | .quant q (.matrix qf) => some (q, qf)
  | _ => none

private meta def prove (source : Reify.Source) (plans : Array SourcePlan) : MetaM Expr := do
  Tactic.checkGuards source
  let anchors := plans.map (·.anchorValue)
  let common := QAdjoin.common (anchors.map RealAlgebraicNumber.toAlgebraic)
  unless common.entries.size == anchors.size do
    throwError "rcf: common-field presentation failed"
  unless common.generator.isReal do
    throwError "rcf: common-field generator is not real"
  let p := common.generator.p
  let s := common.generator.rep.1.square
  if hw : atomWitness p s then
    if hp : (mahlerPrec p : Int) ≤ s.prec then
      let pExpr : Q(ZPoly) ← FieldLiteral.zpolyExpr p
      let sExpr : Q(DyadicSquare) ← FieldLiteral.squareExpr s
      let hwExpr ← mkDecideProof (q(atomWitness $pExpr $sExpr) : Q(Prop))
      let hpExpr ← mkDecideProof
        (q((mahlerPrec $pExpr : Int) ≤ ($sExpr).prec) : Q(Prop))
      let rootExpr ← mkAppM ``SimpleRoot.ofSquare #[pExpr, sExpr, hwExpr, hpExpr]
      let mut coordinates : Array (PolyQuot p (SimpleRoot.ofSquare p s hw hp)) := #[]
      for entry in common.entries do
        coordinates := coordinates.push (PolyQuot.ofSquare p s entry.coeffs hw hp)
      let n := coordinates.size
      let anchorCoordinates : Fin n → PolyQuot p (SimpleRoot.ofSquare p s hw hp) :=
        fun i => coordinates[i.val]
      let anchorExpr ← FieldLiteral.valuesExpr pExpr rootExpr anchorCoordinates
      let fields : Fin n → DensePoly Rat := fun i => plans[i.val]!.field
      let values : Fin n → PolyQuot p (SimpleRoot.ofSquare p s hw hp) :=
        fun i => CommonPresentation.evalAt (fields i) (anchorCoordinates i)
      let fieldEntries := plans.map (·.fieldExpr)
      let fieldTy ← inferType fieldEntries[0]!
      let fieldFn ← FieldLiteral.finiteExpr fieldTy fieldEntries fieldEntries[0]!
      let valuesExpr ← withLocalDeclD `i (mkApp (mkConst ``Fin) (mkNatLit n))
        fun i => do
          let body ← mkAppM ``CommonPresentation.evalAt
            #[mkApp fieldFn i, mkApp anchorExpr i]
          mkLambdaFVars #[i] body
      let sourcePolys := plans.map fun plan => ZPoly.toRatPoly plan.sourcePolynomial
      let sourceSquares := plans.map (·.sourceSquare)
      let mut sourcePExprs : Array Expr := #[]
      let mut sourceSquareExprs : Array Expr := #[]
      let mut sourceWitnesses : Array Expr := #[]
      let mut sourcePrecisions : Array Expr := #[]
      let mut selectedProofs : Array Expr := #[]
      for i in [:n] do
        let sourceP := plans[i]!.sourcePolynomial
        let some sourceSquare := sourceSquares[i]? |
          throwError "rcf: source square count differs from the coordinates"
        let sourceSquareExpr : Q(DyadicSquare) ← FieldLiteral.squareExpr sourceSquare
        let sourcePExpr : Q(ZPoly) ← match plans[i]!.kind with
          | .radical degree => do
              unless sourceP == SquareRoot.polynomial degree do
                throwError "rcf: source radical has a different defining polynomial"
              let nExpr : Q(ℕ) := mkNatLit degree
              pure q(SquareRoot.polynomial $nExpr)
          | .selected _ => FieldLiteral.zpolyExpr sourceP
        let sourceWitness ← mkDecideProof
          (q(atomWitness $sourcePExpr $sourceSquareExpr) : Q(Prop))
        let sourcePrecision ← mkDecideProof
          (q((mahlerPrec $sourcePExpr : Int) ≤ ($sourceSquareExpr).prec) : Q(Prop))
        let selected ← match plans[i]!.kind with
          | .radical degree => do
              let nExpr : Q(ℕ) := mkNatLit degree
              let hreal ← mkDecideProof
                (q(($sourceSquareExpr).meetsRealAxis = true) : Q(Prop))
              let hpositive ← Tactic.positiveLowerBound sourceSquareExpr
              mkAppM ``SquareRoot.selected
                #[nExpr, sourceSquareExpr, sourceWitness, sourcePrecision,
                  hreal, hpositive]
          | .selected args => do
              let sourceValue ← mkAppM ``Selected.real_toReal args
              mkAppM ``Eq.symm #[sourceValue]
        sourcePExprs := sourcePExprs.push sourcePExpr
        sourceSquareExprs := sourceSquareExprs.push sourceSquareExpr
        sourceWitnesses := sourceWitnesses.push sourceWitness
        sourcePrecisions := sourcePrecisions.push sourcePrecision
        selectedProofs := selectedProofs.push selected
      let sourcePFn ← FieldLiteral.finiteExpr (mkConst ``ZPoly) sourcePExprs sourcePExprs[0]!
      let sourceSquareFn ← FieldLiteral.finiteExpr (mkConst ``DyadicSquare)
        sourceSquareExprs sourceSquareExprs[0]!
      let sourcePolyFn ← withLocalDeclD `i (mkApp (mkConst ``Fin) (mkNatLit n))
        fun i => do
          let body ← mkAppM ``ZPoly.toRatPoly #[mkApp sourcePFn i]
          mkLambdaFVars #[i] body
      let mut extras := []
      for i in List.finRange n do
        let some square := sourceSquares[i.val]? |
          throwError "rcf: source square count differs from the coordinates"
        extras := extras ++ [CommonPresentation.discSlack square (anchorCoordinates i)]
      let formula ← FieldRuntime.evalFormula n source.formula
      let some (quantifier, qf) := oneQuantifier formula |
        throwError "rcf: expected one real quantifier over a matrix"
      let formulaWhnf ← whnf source.formula
      let matrixExpr ← whnf formulaWhnf.getAppArgs.back!
      let qfExpr := matrixExpr.getAppArgs.back!
      let some cert := QuadraticNormCertificate.certify? p |
        throwError "rcf: this common field of degree {p.natDegree} is not supported by the current checked irreducibility route"
      let certExpr : Q(QuadraticNormCertificate) ← FieldLiteral.quadraticCertExpr cert
      let hcert ← mkDecideProof
        (q(($certExpr).check $pExpr = true) : Q(Prop))
      let hdegree ← mkDecideProof (q(0 < ($pExpr).natDegree) : Q(Prop))
      let irred ← mkAppM ``Field.checkedIrreducibleQuadraticNorm
        #[pExpr, certExpr, hcert, hdegree]
      let instType ← mkAppM ``ZPoly.CheckedIrreducible #[pExpr]
      if hc : cert.check p = true then
        if hd : 0 < p.natDegree then
          letI : ZPoly.CheckedIrreducible p :=
            Field.checkedIrreducibleQuadraticNorm p cert hc hd
          withLocalDecl `inst .instImplicit instType fun inst => do
            let sourcePolyRuntime : Fin n → DensePoly Rat := fun i =>
              (sourcePolys[i.val]?).getD (DensePoly.ofList [])
            let sourceSquareRuntime : Fin n → DyadicSquare := fun i =>
              (sourceSquares[i.val]?).getD s
            let validate (data : FieldBuild.Result p s hw hp Unit (n + 1)) : MetaM Unit := do
              unless CommonPresentation.checkPresentation hw hp data.signs
                  sourcePolyRuntime sourceSquareRuntime anchorCoordinates do
                let equations := (List.finRange n).map fun i =>
                  CommonPresentation.checkEquation (sourcePolyRuntime i)
                    (anchorCoordinates i)
                let margins := (List.finRange n).map fun i =>
                  data.signs.lookup? (CommonPresentation.discSlack
                    (sourceSquareRuntime i) (anchorCoordinates i))
                throwError "rcf: common-field proposal rejected: equations {repr equations}, margins {repr margins}"
            let (fixedProof, certificate, data, verdictProof) ←
              FieldLiteral.proveWithCertificate
              pExpr rootExpr valuesExpr qfExpr values qf quantifier 8 extras validate
            let signTable ← mkAppM ``FieldBuild.Result.signs #[certificate]
            let signProofName := match quantifier with
              | .forallReal => ``FieldBuild.Result.checkForall_signTable
              | .existsReal => ``FieldBuild.Result.checkExists_signTable
            let signProof ← mkAppM signProofName
              #[certificate, valuesExpr, qfExpr, mkConst ``Unit.unit, verdictProof]
            let checked ← mkAppM ``CommonPresentation.checkPresentation
              #[hwExpr, hpExpr, signTable, sourcePolyFn, sourceSquareFn, anchorExpr]
            let checkedGoal ← mkAppM ``Eq #[checked, mkConst ``Bool.true]
            let checkedProof ← withLocalDeclD `htable (← inferType signProof) fun htable => do
              let checkedMVar ← mkFreshExprMVar checkedGoal
              let remaining ← Lean.Elab.runTactic' checkedMVar.mvarId!
                (← `(tactic|
                  (simp only [CommonPresentation.checkPresentation, Bool.and_eq_true];
                   constructor <;> first | assumption | decide +kernel)))
              unless remaining.isEmpty do
                throwError "rcf: common-field coordinate replay left {remaining.length} goals"
              let abstract ← mkLambdaFVars #[htable] (← instantiateMVars checkedMVar)
              return mkApp abstract signProof
            let sourceValues := source.valuation
            let finType := mkApp (mkConst ``Fin) (mkNatLit n)
            let anchorReals := plans.map (·.anchorReal)
            let anchorValues ← FieldLiteral.finiteExpr (mkConst ``Real)
              anchorReals anchorReals[0]!
            let hwGoal ← withLocalDeclD `i finType fun i => do
              let pAt := mkApp sourcePFn i
              let sAt := mkApp sourceSquareFn i
              mkForallFVars #[i] (← mkAppM ``atomWitness #[pAt, sAt])
            let hpGoal ← withLocalDeclD `i finType fun i => do
              let pAt : Q(ZPoly) := mkApp sourcePFn i
              let sAt : Q(DyadicSquare) := mkApp sourceSquareFn i
              let body : Q(Prop) := q((mahlerPrec $pAt : Int) ≤ ($sAt).prec)
              mkForallFVars #[i] body
            let hwProof ← FieldLiteral.proveFinCases hwGoal sourceWitnesses
            let hpProof ← FieldLiteral.proveFinCases hpGoal sourcePrecisions
            let hpolyProof ← withLocalDeclD `i finType fun i => do
              let pAt := mkApp sourcePFn i
              let body ← mkAppM ``ZPoly.toRatPoly #[pAt]
              let eq ← mkEqRefl body
              mkLambdaFVars #[i] eq
            let hselectedGoal ← withLocalDeclD `i finType fun i => do
              let pAt := mkApp sourcePFn i
              let sAt := mkApp sourceSquareFn i
              let hwAt := mkApp hwProof i
              let hpAt := mkApp hpProof i
              let rep ← mkAppM ``Field.literalRep #[pAt, sAt, hwAt, hpAt]
              let root ← mkAppM ``HexRootsMathlib.RefinedIsolation.root #[rep]
              let realPart ← mkAppM ``Complex.re #[root]
              let valueAt := mkApp anchorValues i
              let body ← mkAppM ``Eq #[realPart, valueAt]
              mkForallFVars #[i] body
            let hselectedProof ← FieldLiteral.proveFinCases hselectedGoal selectedProofs
            let hvalueGoal ← withLocalDeclD `i finType fun i => do
              let fieldAt := mkApp fieldFn i
              let anchorAt := mkApp anchorValues i
              let polynomial ← mkAppM ``LiteralSign.realPoly #[fieldAt]
              let evaluated ← mkAppM ``Polynomial.eval #[anchorAt, polynomial]
              let body ← mkAppM ``Eq #[evaluated, mkApp sourceValues i]
              mkForallFVars #[i] body
            let hvalueProof ← FieldLiteral.proveFinCases hvalueGoal
              (plans.map (·.sourceProof))
            let eqVal ← mkAppM ``CommonPresentation.checkPolynomials_sound
              #[hwExpr, hpExpr, signTable, sourcePolyFn, sourceSquareFn, anchorExpr,
                sourcePFn, hwProof, hpProof, hpolyProof, anchorValues,
                hselectedProof, fieldFn, sourceValues, hvalueProof, checkedProof]
            let congr ← withLocalDeclD `ρ (← inferType source.valuation) fun ρ => do
              let body ← mkAppM ``Hex.RealFormula.Prenex.toProp #[source.formula, ρ]
              mkAppM ``congrArg #[← mkLambdaFVars #[ρ] body, eqVal]
            let specialized ← mkAppM ``Eq.mp #[congr, fixedProof]
            let final ← mkAppM ``Iff.mp #[source.proof, specialized]
            let abstract ← mkLambdaFVars #[inst] final
            let applied := mkApp abstract irred
            return applied
        else throwError "rcf: common polynomial has zero degree"
      else throwError "rcf: quadratic-norm certificate failed"
    else throwError "rcf: common square has insufficient precision"
  else throwError "rcf: common square failed its root witness"

@[rcf_handler] meta def handle : Handler := fun target => do
  if (sourceAtoms target #[]).size < 2 then return .declined
  let .ok source ← Reify.prepare target | return .declined
  if source.coefficients.size < 2 then return .declined
  let mut plans : Array SourcePlan := #[]
  for coefficient in source.coefficients do
    let some plan ← sourcePlan? coefficient | return .declined
    plans := plans.push plan
  let proof ← prove source plans
  return .proved proof

end Hex.RCF.RealCoefficients.CommonTactic
