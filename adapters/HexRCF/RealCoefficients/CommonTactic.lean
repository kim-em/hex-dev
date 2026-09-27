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

private partial def squareRoots (e : Expr) (seen : Array Expr) : Array Expr :=
  let seen := if e.isAppOfArity ``Real.sqrt 1 && !seen.contains e then seen.push e else seen
  match e with
  | .app fn arg => squareRoots arg (squareRoots fn seen)
  | .forallE _ type body _ | .lam _ type body _ =>
      squareRoots body (squareRoots type seen)
  | .letE _ type value body _ =>
      squareRoots body (squareRoots value (squareRoots type seen))
  | .mdata _ body | .proj _ _ body => squareRoots body seen
  | _ => seen

private def oneQuantifier {n : Nat} (formula : RealFormula.Prenex n) :
    Option (RealFormula.Quantifier × RealFormula.QF (n + 1)) :=
  match formula with
  | .quant q (.matrix qf) => some (q, qf)
  | _ => none

private meta def prove (source : Reify.Source) (degrees : Array Nat) : MetaM Expr := do
  Tactic.checkGuards source
  let mut algebraicValues : Array RealAlgebraicNumber := #[]
  for coefficient in source.coefficients do
    let (_, _, value) ← FieldRuntime.coefficient coefficient
    algebraicValues := algebraicValues.push value
  let common := QAdjoin.common (algebraicValues.map RealAlgebraicNumber.toAlgebraic)
  unless common.entries.size == algebraicValues.size do
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
      let values : Fin n → PolyQuot p (SimpleRoot.ofSquare p s hw hp) :=
        fun i => coordinates[i.val]
      let valuesExpr ← FieldLiteral.valuesExpr pExpr rootExpr values
      let sourcePolys := algebraicValues.map fun v => ZPoly.toRatPoly v.toAlgebraic.p
      let sourceSquares := algebraicValues.map fun v => v.toAlgebraic.rep.1.square
      let mut sourcePExprs : Array Expr := #[]
      let mut sourceSquareExprs : Array Expr := #[]
      let mut sourceWitnesses : Array Expr := #[]
      let mut sourcePrecisions : Array Expr := #[]
      let mut selectedProofs : Array Expr := #[]
      for i in [:n] do
        let sourceP := algebraicValues[i]!.toAlgebraic.p
        let some sourceSquare := sourceSquares[i]? |
          throwError "rcf: source square count differs from the coordinates"
        let sourceSquareExpr : Q(DyadicSquare) ← FieldLiteral.squareExpr sourceSquare
        let nExpr : Q(ℕ) := mkNatLit degrees[i]!
        unless sourceP == SquareRoot.polynomial degrees[i]! do
          throwError "rcf: source radical has a different defining polynomial"
        let sourcePExpr : Q(ZPoly) := q(SquareRoot.polynomial $nExpr)
        let sourceWitness ← mkDecideProof
          (q(atomWitness $sourcePExpr $sourceSquareExpr) : Q(Prop))
        let sourcePrecision ← mkDecideProof
          (q((mahlerPrec $sourcePExpr : Int) ≤ ($sourceSquareExpr).prec) : Q(Prop))
        let hreal ← mkDecideProof
          (q(($sourceSquareExpr).meetsRealAxis = true) : Q(Prop))
        let hpositive ← Tactic.positiveLowerBound sourceSquareExpr
        let selected ← mkAppM ``SquareRoot.selected
          #[nExpr, sourceSquareExpr, sourceWitness, sourcePrecision, hreal, hpositive]
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
        extras := extras ++ [CommonPresentation.discSlack square (values i)]
      let formula ← FieldRuntime.evalFormula n source.formula
      let some (quantifier, qf) := oneQuantifier formula |
        throwError "rcf: expected one real quantifier over a matrix"
      let formulaWhnf ← whnf source.formula
      let matrixExpr ← whnf formulaWhnf.getAppArgs.back!
      let qfExpr := matrixExpr.getAppArgs.back!
      let some cert := QuadraticNormCertificate.certify? p |
        throwError "rcf: common polynomial has no checked quadratic-norm certificate"
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
                  sourcePolyRuntime sourceSquareRuntime values do
                let equations := (List.finRange n).map fun i =>
                  CommonPresentation.checkEquation (sourcePolyRuntime i) (values i)
                let margins := (List.finRange n).map fun i =>
                  data.signs.lookup? (CommonPresentation.discSlack
                    (sourceSquareRuntime i) (values i))
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
              #[hwExpr, hpExpr, signTable, sourcePolyFn, sourceSquareFn, valuesExpr]
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
              let valueAt := mkApp sourceValues i
              let body ← mkAppM ``Eq #[realPart, valueAt]
              mkForallFVars #[i] body
            let hselectedProof ← FieldLiteral.proveFinCases hselectedGoal selectedProofs
            let eqVal ← mkAppM ``CommonPresentation.checkPresentation_sound_of_selected
              #[hwExpr, hpExpr, signTable, sourcePolyFn, sourceSquareFn, valuesExpr,
                sourcePFn, hwProof, hpProof, hpolyProof, sourceValues,
                hselectedProof, checkedProof]
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
  let roots := squareRoots target #[]
  if roots.size < 2 then return .declined
  for root in roots do
    unless (← naturalSquareRoot? root).isSome do return .declined
  let .ok source ← Reify.prepare target | return .declined
  if source.coefficients.size < 2 then return .declined
  let mut degrees : Array Nat := #[]
  for coefficient in source.coefficients do
    let some n ← naturalSquareRoot? coefficient | return .declined
    degrees := degrees.push n
  let proof ← prove source degrees
  return .proved proof

end Hex.RCF.RealCoefficients.CommonTactic
