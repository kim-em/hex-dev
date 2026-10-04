/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public meta import HexRCF.RealCoefficients.Tactic
public meta import HexRCF.RealCoefficients.SquareRoot
public meta import HexRCF.RealCoefficients.RationalRoot
public meta import HexRCF.RealCoefficients.CommonPresentation
public meta import HexBerlekampZassenhaus.QuadraticNormRecover
public meta import HexBerlekampZassenhausMathlib.FactorTactic

public meta import HexRCF.RealCoefficients.FieldCompile
public meta import HexRCF.RealCoefficients.Preparation

public meta section

/-! Authenticate algebraic source leaves, then replay closed arithmetic and
original guards in their checked common field before goal certificate search. -/

namespace Hex.RCF.RealCoefficients.CommonTactic

open Hex Lean Meta Qq

/-- Quote a checked irreducibility proof for a literal common polynomial.
The runtime input selects finite evidence; the kernel checks that evidence
against the supplied expression before returning the class proof. -/
meta def certify (p : ZPoly) (pExpr : Q(ZPoly)) (degree : Expr) : MetaM Expr := do
  let candidate ← match QuadraticNormCertificate.certify? p with
    | some cert => do
        let certExpr : Q(QuadraticNormCertificate) ←
          FieldLiteral.quadraticCertExpr cert
        let hcert ← mkDecideProof
          (q(($certExpr).check $pExpr = true) : Q(Prop))
        mkAppM ``Field.checkedIrreducibleQuadraticNorm
          #[pExpr, certExpr, hcert, degree]
    | none => do
        match HexBerlekampZassenhaus.FactorTactic.searchWitness p with
        | some witness =>
            let witnessExpr : Q(ZPoly.IrredWitness) :=
              HexBerlekampZassenhaus.FactorTactic.reifyWitness witness
            unless ZPoly.checkIrredWitness p witness do
              throwError "rcf: computed irreducibility witness failed its check"
            let hwitness ← mkDecideProof
              (q(ZPoly.checkIrredWitness $pExpr $witnessExpr = true) : Q(Prop))
            mkAppM ``Field.checkedIrreducible
              #[pExpr, witnessExpr, hwitness, degree]
        | none =>
            let some certificate := certifyIrreducible? p |
              throwError "rcf: no checked irreducibility witness for this common field"
            unless HexBerlekampZassenhausMathlib.checkMultiPrimeCert p certificate do
              throwError "rcf: computed multi-prime certificate failed its check"
            let proof ← HexBerlekampZassenhausMathlib.FactorTactic.zpolyIrredProof
              pExpr (.multi certificate)
            let equivalence ← mkAppM ``ZPoly.isIrreducible_iff #[pExpr]
            let checked ← mkAppM ``Iff.mpr #[equivalence, proof]
            mkAppM ``ZPoly.CheckedIrreducible.mk #[checked, degree]
  let target ← mkAppM ``ZPoly.CheckedIrreducible #[pExpr]
  mkAuxTheorem target candidate (zetaDelta := true) (cache := false)

private meta def kernelDecide (goal : Expr) : MetaM Expr := do
  let candidate ← mkFreshExprMVar goal
  let remaining ← Lean.Elab.runTactic' candidate.mvarId!
    (← `(tactic|
      (simp only [CommonPresentation.checkPresentation, Field.checkSignTable,
        LiteralSign.Table.check, LiteralSign.Entry.check, Sturm.check, TarskiCertificate.check_eq, SignedRemainderChain.check,
        ← Array.all_toList, Array.toList_range, Bool.and_eq_true];
       repeat' (any_goals (apply And.intro)); all_goals decide +kernel)))
  unless remaining.isEmpty do
    let goals ← remaining.mapM fun goal => goal.withContext do
      return ← ppExpr (← goal.getType)
    throwError "rcf: literal source replay did not close: {MessageData.joinSep goals m!"\n"}"
  return ← instantiateMVars candidate

private meta def naturalSquareRoot? (source : Expr) : MetaM (Option Nat) := do
  unless source.isAppOfArity ``Real.sqrt 1 do return none
  let base : Q(ℝ) ← Reify.lowerSources #[] source.appArg!
  let result ← observing? do
    let ⟨value, _, _, _⟩ ← Mathlib.Meta.NormNum.deriveRat base
      (_inst := q(inferInstance))
    pure value
  let some value := result | return none
  unless value.den == 1 && 0 < value.num do return none
  return some value.num.toNat

/-- Prove the original radicand equality before using the selected positive root. -/
private meta def rootAlias (source : Expr) (radicand : Nat) : MetaM Expr := do
  let (base, equality) ← Reify.lowerWithProof #[] source.appArg!
  let base : Q(ℝ) := base
  let n : Q(ℕ) := mkNatLit radicand
  let candidate ← mkFreshExprMVar q($base = ($n : ℝ))
  let remaining ← Lean.Elab.runTactic' candidate.mvarId!
    (← `(tactic| norm_num [RealAlgebraicNumber.ofRat_toReal]))
  unless remaining.isEmpty do
    throwError "rcf: square-root radicand has no checked natural value"
  let proof ← mkEqTrans equality (← instantiateMVars candidate)
  checkWithKernel proof
  return ← mkEqSymm (← mkAppM ``congrArg #[mkConst ``Real.sqrt, proof])

private inductive SourceKind where
  | radical (radicand : Nat) (aliasProof : Expr)
  | root (parameters : RationalRoot.Parameters) (aliasProof : Expr)
  | selected (args : Array Expr) (checked : Expr)
  | normalized (selected checked : Expr)
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
    DensePoly.ofList [], default, default, .radical 1 default⟩

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
        x.isAppOfArity ``Coefficients.ofField 2 ||
        x.isAppOfArity ``RealAlgebraicNumber.ofAlgebraic 2) | return none
  if field.isAppOfArity ``Selected.field 11 then
    let args := field.getAppArgs
    let generator ← mkAppM ``Selected.real (args.extract 0 10)
    return some (true, generator, args[10]!)
  let args := field.getAppArgs
  if field.isAppOfArity ``Coefficients.ofField 2 then
    return some (false, args[0]!, args[1]!)
  let some converted ← unfoldHead? args[0]!
      (·.isAppOfArity ``QAdjoin.toAlgebraicNumber 2) | return none
  let convertedArgs := converted.getAppArgs
  let some generator ← unfoldHead? convertedArgs[0]!
      (·.isAppOfArity ``RealAlgebraicNumber.toAlgebraic 1) | return none
  -- Proof irrelevance identifies the caller's reality proof with `ofField`'s
  -- proof, while its algebraic value and selected generator remain unchanged.
  return some (false, generator.appArg!, convertedArgs[1]!)

private meta def coefficientProof (value expression : Expr) : MetaM Expr := do
  let goal ← mkAppM ``Eq #[value, expression]
  let candidate ← mkFreshExprMVar goal
  let remaining ← Lean.Elab.runTactic' candidate.mvarId! (← `(tactic| decide +kernel))
  unless remaining.isEmpty do
    throwError "rcf: source field coefficients differ from their literal encoding"
  return ← instantiateMVars candidate

private meta def normalizedArgs? (argument : Expr) :
    MetaM (Option (Array Expr × Expr)) := do
  if (← selectedArgs? argument).isSome then return none
  let some real ← unfoldHead? argument
      (·.isAppOfArity ``RealAlgebraicNumber.ofAlgebraic 2) | return none
  let realArgs := real.getAppArgs
  let some algebraic ← unfoldHead? realArgs[0]!
      (·.isAppOfArity ``AlgebraicNumber.ofNormalized 8) | return none
  return some (algebraic.getAppArgs, realArgs[1]!)

private partial def sourceAtoms (e : Expr) (seen : Array Expr) : Array Expr :=
  if RationalRoot.isNotation e ||
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

private partial def algebraicDivision (e : Expr) : Bool :=
  let args := e.getAppArgs
  let inverse := if e.isAppOfArity ``Inv.inv 3 then
      args[0]!.isConstOf ``Real && !(sourceAtoms args[2]! #[]).isEmpty
    else false
  let division := if e.isAppOfArity ``HDiv.hDiv 6 then
      args[0]!.isConstOf ``Real && !(sourceAtoms args[5]! #[]).isEmpty
    else false
  inverse || division || match e with
    | .app fn arg => algebraicDivision fn || algebraicDivision arg
    | .forallE _ type body _ | .lam _ type body _ =>
        algebraicDivision type || algebraicDivision body
    | .letE _ type value body _ =>
        algebraicDivision type || algebraicDivision value || algebraicDivision body
    | .mdata _ body | .proj _ _ body => algebraicDivision body
    | _ => false

private meta def candidate (target : Expr) : MetaM Bool := do
  -- Local aliases are resolved by the shared frontend, with their proofs.
  if target.hasFVar || algebraicDivision target then return true
  return !(sourceAtoms target #[]).isEmpty

/-- Preserve single-coefficient priority only when every original divisor
is rational. Rational normalization restores its temporary metavariable state. -/
private meta def rationalGuards (divisors : Array Expr) : MetaM Bool := do
  for original in divisors do
    let divisor ← Reify.lowerSources #[] original
    if !(sourceAtoms divisor #[]).isEmpty then return false
    let value : Q(ℝ) := divisor
    let result ← (do
      let saved ← saveState
      try
        let ⟨_, _, _, _⟩ ← Mathlib.Meta.NormNum.deriveRat value (_inst := q(inferInstance))
        return true
      catch _ => return false
      finally saved.restore : MetaM Bool)
    if !result then return false
  return true

private meta def rootParameters? (source : Expr) : MetaM (Option RationalRoot.Parameters) := do
  match ← RationalRoot.parameters? source with
  | .ok parameters => pure parameters
  | .error (.unsupported _ _) => pure none
  | .error error => throwError "rcf: {Hex.RealFormula.Reify.Error.toMessageData error}"

/-- Classify the entire source before executing any algebraic construction.
Unknown siblings must cause a decline before a recognized sibling can fail. -/
private meta def eligible (source : Expr) : MetaM Bool := do
  if (← naturalSquareRoot? source).isSome then return true
  if (← rootParameters? source).isSome then return true
  unless source.isAppOfArity ``RealAlgebraicNumber.toReal 1 do return false
  let argument := source.appArg!
  let anchor ← match ← fieldArgs? argument with
    | some (_, anchor, _) => pure anchor
    | none => pure argument
  return (← selectedArgs? anchor).isSome || (← normalizedArgs? anchor).isSome

/-- Bind source data by kernel reduction; authentication and resource failures
remain terminal, rather than becoming solver declines. -/
private meta def bindLiteral (goal : Expr) (literal : Expr)
    (kind label : String) : MetaM Expr := do
  try
    withOptions (fun opts =>
        debug.skipKernelTC.set (Elab.async.set opts false) false) do
      mkAuxTheorem goal (← mkEqRefl literal) (zetaDelta := true) (cache := false)
  catch error =>
    -- Core rethrows interrupt/runtime exceptions; retain kernel error details,
    -- including deterministic timeout and deep-recursion failures.
    throwError "rcf: {kind} source {label} must reduce to its literal encoding in the kernel\n{error.toMessageData}"

private meta def transportChecked (checked equality : Expr) : MetaM Expr := do
  let types ← mkAppM ``congrArg #[mkConst ``ZPoly.CheckedIrreducible, equality]
  mkAppM ``Eq.mp #[types, checked]

private meta def sourceRoot? (argument : Expr) :
    MetaM (Option (RealAlgebraicNumber × ZPoly × DyadicSquare × SourceKind)) := do
  if let some args ← selectedArgs? argument then
    let p ← FieldRuntime.evalZPoly args[0]!
    let sourceP : Q(ZPoly) ← pure args[0]!
    let literalP : Q(ZPoly) ← FieldLiteral.zpolyExpr p
    let equality ← bindLiteral q($sourceP = $literalP) literalP "selected" "polynomial"
    let checked ← transportChecked args[7]! equality
    return some (← FieldRuntime.evalReal argument, p,
      ← FieldRuntime.evalSquare args[1]!, .selected args checked)
  let some (args, hreal) ← normalizedArgs? argument | return none
  let p ← FieldRuntime.evalZPoly args[0]!
  let sourceP : Q(ZPoly) ← pure args[0]!
  let rep : Q(RefinedIsolation $sourceP) ← pure args[6]!
  let square := q(($rep).1.square)
  let s ← FieldRuntime.evalSquare square
  unless Decidable.decide (atomWitness p s) do
    throwError "rcf: normalized source square needs a directly checkable root witness"
  unless Decidable.decide ((mahlerPrec p : Int) ≤ s.prec) do
    throwError "rcf: normalized source square has insufficient precision"
  let literalP : Q(ZPoly) ← FieldLiteral.zpolyExpr p
  let literalSquare : Q(DyadicSquare) ← FieldLiteral.squareExpr s
  -- Authenticate executable data before canonicalization or common-field search.
  -- The kernel checks literal identities without reducing the constructor result.
  let hpoly ← bindLiteral q($sourceP = $literalP) literalP "normalized" "polynomial"
  let hs ← bindLiteral q(($rep).1.square = $literalSquare) literalSquare "normalized" "square"
  let checked ← transportChecked args[4]! hpoly
  let hw ← mkDecideProof (q(atomWitness $literalP $literalSquare) : Q(Prop))
  let hp ← mkDecideProof
    (q((mahlerPrec $literalP : Int) ≤ ($literalSquare).prec) : Q(Prop))
  let selected ← mkAppM ``Selected.normalized_toReal
    (args ++ #[hreal, literalP, hpoly, literalSquare, hw, hp, hs])
  return some (← FieldRuntime.evalReal argument, p, s, .normalized selected checked)

private meta def sourcePlan? (source : Expr) : MetaM (Option SourcePlan) := do
  let identity : DensePoly Rat := DensePoly.ofList [0, 1]
  if let some radicand ← naturalSquareRoot? source then
    let (_, _, anchorValue) ← FieldRuntime.coefficient source
    let sourceP := SquareRoot.polynomial radicand
    let sourceSquare := if anchorValue.toAlgebraic.p == sourceP then
        anchorValue.toAlgebraic.rep.1.square
      else
        -- A perfect-square radicand has a linear minimal polynomial. Its
        -- source alias is still authenticated with `X² - n`, independently
        -- of the canonical generator's defining polynomial.
        let precision := mahlerPrec sourceP + 4
        let ball := anchorValue.approxBall precision
        { re := ball.re, im := 0, prec := precision }
    unless Decidable.decide (atomWitness sourceP sourceSquare) &&
        Decidable.decide ((mahlerPrec sourceP : Int) ≤ sourceSquare.prec) do
      throwError "rcf: square-root source has no checked selected-root witness"
    let fieldExpr ← FieldLiteral.ratPolyExpr identity
    let sourceProof ← mkAppM ``CommonPresentation.generator_eval #[source]
    return some ⟨source, anchorValue, sourceP, sourceSquare,
      identity, fieldExpr, sourceProof,
      .radical radicand (← rootAlias source radicand)⟩
  if let some parameters ← rootParameters? source then
    let (_, _, anchorValue) ← FieldRuntime.coefficient source
    let sourceP := RationalRoot.polynomial parameters.base parameters.degree
    let sourceSquare := if anchorValue.toAlgebraic.p == sourceP then
        anchorValue.toAlgebraic.rep.1.square
      else
        let precision := mahlerPrec sourceP + 4
        let ball := anchorValue.approxBall precision
        { re := ball.re, im := 0, prec := precision }
    unless Decidable.decide (atomWitness sourceP sourceSquare) &&
        Decidable.decide ((mahlerPrec sourceP : Int) ≤ sourceSquare.prec) do
      throwError "rcf: rational-root source has no checked selected-root witness"
    let fieldExpr ← FieldLiteral.ratPolyExpr identity
    let sourceProof ← mkAppM ``CommonPresentation.generator_eval #[source]
    return some ⟨source, anchorValue, sourceP, sourceSquare,
      identity, fieldExpr, sourceProof,
      .root parameters (← RationalRoot.identify source parameters)⟩
  unless source.isAppOfArity ``RealAlgebraicNumber.toReal 1 do return none
  let argument := source.appArg!
  let field? ← fieldArgs? argument
  if field?.isNone then
    let some (anchorValue, sourceP, sourceSquare, kind) ← sourceRoot? argument |
      return none
    let anchorReal ← mkAppM ``RealAlgebraicNumber.toReal #[argument]
    let fieldExpr ← FieldLiteral.ratPolyExpr identity
    let sourceProof ← mkAppM ``CommonPresentation.generator_eval #[anchorReal]
    return some ⟨anchorReal, anchorValue, sourceP, sourceSquare,
      identity, fieldExpr, sourceProof,
      kind⟩
  let some (isSelectedField, anchorExpr, fieldValue) := field? | return none
  let some (anchorValue, sourceP, sourceSquare, kind) ← sourceRoot? anchorExpr |
    return none
  let anchorReal ← mkAppM ``RealAlgebraicNumber.toReal #[anchorExpr]
  let coeffs ← mkAppM ``PolyQuot.coeffs #[fieldValue]
  let field ← FieldRuntime.evalRatPoly coeffs
  let fieldExpr ← FieldLiteral.ratPolyExpr field
  -- `ofNormalized_p` exposes the generator polynomial as constructor data,
  -- so this reduces field arithmetic without replaying root isolation.
  let hcoeff ← coefficientProof coeffs fieldExpr
  let sourceProof ← if isSelectedField then
    let .selected args _ := kind |
      throwError "rcf: selected field has no selected generator"
    mkAppM ``Selected.field_eval
      #[args[0]!, args[1]!, args[2]!, args[3]!, args[4]!,
        args[5]!, args[6]!, args[7]!, args[8]!, args[9]!,
        fieldValue, fieldExpr, hcoeff]
  else do
    let sourceValue ← mkAppM ``CommonPresentation.ofField_eval
      #[anchorExpr, fieldValue, fieldExpr, hcoeff]
    mkAppM ``Eq.symm #[sourceValue]
  return some ⟨anchorReal, anchorValue, sourceP, sourceSquare,
    field, fieldExpr, sourceProof,
    kind⟩

private def oneQuantifier {n : Nat} (formula : RealFormula.Prenex n) :
    Option (RealFormula.Quantifier × RealFormula.QF (n + 1)) :=
  match formula with
  | .quant q (.matrix qf) => some (q, qf)
  | _ => none

private meta def prepareField (source : Reify.Source) (leafSources : Array Expr)
    (plans : Array SourcePlan) : MetaM Coefficients.Environment := do
  let anchors := plans.map (·.anchorValue)
  -- Several source coordinates may use the same selected generator. Search
  -- once for each generator, then restore the original source order. Every
  -- resulting coordinate still passes the polynomial and enclosure checks.
  let distinct := anchors.foldl (fun seen anchor =>
    if seen.contains anchor then seen else seen.push anchor) #[]
  let common := profileit "rcf common field" (← getOptions) fun _ =>
    (if distinct.size = 1 then
      let generator := distinct[0]!.toAlgebraic
      ⟨generator, #[generator.toQAdjoin]⟩
    else QAdjoin.common (distinct.map RealAlgebraicNumber.toAlgebraic) : QAdjoin.Presentation)
  unless common.entries.size == distinct.size do
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
      for anchor in anchors do
        let some index := distinct.idxOf? anchor |
          throwError "rcf: source generator is missing from the common field"
        let some entry := common.entries[index]? |
          throwError "rcf: common-field coordinate count differs from its generators"
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
          | .radical radicand _ => do
              unless sourceP == SquareRoot.polynomial radicand do
                throwError "rcf: source radical has a different defining polynomial"
              let nExpr : Q(ℕ) := mkNatLit radicand
              pure q(SquareRoot.polynomial $nExpr)
          | .root parameters _ => do
              unless sourceP == RationalRoot.polynomial parameters.base parameters.degree do
                throwError "rcf: source rational root has a different defining polynomial"
              let base : Q(ℚ) ← mkAppM ``mkRat
                #[mkIntLit parameters.base.num, mkNatLit parameters.base.den]
              let degree : Q(ℕ) ← pure (mkNatLit parameters.degree)
              pure q(RationalRoot.polynomial $base $degree)
          | .selected _ _ | .normalized _ _ => FieldLiteral.zpolyExpr sourceP
        let sourceWitness ← mkDecideProof
          (q(atomWitness $sourcePExpr $sourceSquareExpr) : Q(Prop))
        let sourcePrecision ← mkDecideProof
          (q((mahlerPrec $sourcePExpr : Int) ≤ ($sourceSquareExpr).prec) : Q(Prop))
        let selected ← match plans[i]!.kind with
          | .radical radicand aliasProof => do
              let nExpr : Q(ℕ) := mkNatLit radicand
              let hreal ← mkDecideProof
                (q(($sourceSquareExpr).meetsRealAxis = true) : Q(Prop))
              let hpositive ← Tactic.positiveLowerBound sourceSquareExpr
              let selected ← mkAppM ``SquareRoot.selected
                #[nExpr, sourceSquareExpr, sourceWitness, sourcePrecision,
                  hreal, hpositive]
              mkEqTrans selected aliasProof
          | .root parameters aliasProof => do
              let base : Q(ℚ) ← mkAppM ``mkRat
                #[mkIntLit parameters.base.num, mkNatLit parameters.base.den]
              let degree : Q(ℕ) ← pure (mkNatLit parameters.degree)
              let hn ← mkDecideProof (q($degree ≠ 0) : Q(Prop))
              let hreal ← mkDecideProof
                (q(($sourceSquareExpr).meetsRealAxis = true) : Q(Prop))
              let hpositive ← Tactic.positiveLowerBound sourceSquareExpr
              let selected ← mkAppM ``RationalRoot.selected
                #[base, degree, hn, sourceSquareExpr,
                  sourceWitness, sourcePrecision, hreal, hpositive]
              mkEqTrans selected aliasProof
          | .selected args _ => do
              let sourceValue ← mkAppM ``Selected.real_toReal args
              mkAppM ``Eq.symm #[sourceValue]
          | .normalized selected _ => pure selected
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
      let hdegree ← mkDecideProof (q(0 < ($pExpr).natDegree) : Q(Prop))
      let instType ← mkAppM ``ZPoly.CheckedIrreducible #[pExpr]
      let mut sourceIrred : Option Expr := none
      for plan in plans do
        if plan.sourcePolynomial != p then continue
        let checked ← match plan.kind with
          | .radical _ _ | .root _ _ => pure none
          | .selected _ checked | .normalized _ checked => pure (some checked)
        if let some checked := checked then
          unless (← inferType checked) == instType do
            throwError "rcf: internal: transported source irreducibility has a different literal polynomial"
          sourceIrred := some checked
          break
      let irred ← match sourceIrred with
        | some checked => pure checked
        | none => certify p pExpr hdegree
      -- Runtime field operations use the canonical generator's instance;
      -- quotation retains an exactly matching source instance or checks a
      -- literal irreducibility witness for the new presentation.
      letI : ZPoly.CheckedIrreducible p := common.generator.checked
      withLocalDecl `inst .instImplicit instType fun inst => do
        let sourcePolyRuntime : Fin n → DensePoly Rat := fun i =>
          (sourcePolys[i.val]?).getD (DensePoly.ofList [])
        let sourceSquareRuntime : Fin n → DyadicSquare := fun i =>
          (sourceSquares[i.val]?).getD s
        let some table := FieldBuild.buildTable p s hw hp extras |
          throwError "rcf: common-field source sign search failed"
        unless CommonPresentation.checkPresentation hw hp table
            sourcePolyRuntime sourceSquareRuntime anchorCoordinates do
          throwError "rcf: common-field source presentation rejected"
        let table ← FieldLiteral.prepareSigns table
        let signTable ← FieldLiteral.signTableExpr pExpr rootExpr table
        let checked ← mkAppM ``CommonPresentation.checkPresentation
          #[hwExpr, hpExpr, signTable, sourcePolyFn, sourceSquareFn, anchorExpr]
        let checkedGoal ← mkAppM ``Eq #[checked, mkConst ``Bool.true]
        let checkedProof ← kernelDecide checkedGoal
        let sourceValues ← FieldLiteral.finiteExpr (mkConst ``Real) leafSources leafSources[0]!
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
        let leaf (e : Expr) : MetaM (Option (FieldCompile.Result p
            (SimpleRoot.ofSquare p s hw hp))) := do
          let some index := leafSources.idxOf? e | return none
          if hindex : index < n then
            let indexExpr ← mkAppM ``Fin.mk #[mkNatLit index,
              ← mkDecideProof (← mkAppM ``LT.lt #[mkNatLit index, mkNatLit n])]
            let proof ← mkAppM ``congrFun #[eqVal, indexExpr]
            return some ⟨values ⟨index, hindex⟩, mkApp valuesExpr indexExpr, proof⟩
          else throwError "rcf: source leaf index exceeds common coordinates"
        let repExpr ← mkAppM ``Field.literalRep #[pExpr, sExpr, hwExpr, hpExpr]
        let hrepExpr ← mkAppM ``Field.literalRep_mk #[pExpr, sExpr, hwExpr, hpExpr]
        let hrealExpr ← mkDecideProof (q(($sExpr).meetsRealAxis = true) : Q(Prop))
        let hrExpr ← mkAppM ``Field.literalRep_real
          #[pExpr, sExpr, hwExpr, hpExpr, hrealExpr]
        let mut divisorProofs : Array Expr := #[]
        let mut divisorValues := []
        let mut divisorExpressions : Array Expr := #[]
        let mut divisorIdentities : Array Expr := #[]
        for divisor in source.divisors do
          let (lowered, equality) ← Reify.lowerWithProof #[] divisor
          let compiled ← FieldCompile.compile pExpr rootExpr repExpr hrepExpr hrExpr leaf lowered
          let originalProof ← mkEqTrans compiled.proof (← mkEqSymm equality)
          if compiled.value = 0 then
            throwError "rcf: original closed divisor is zero"
          let reflect ← mkAppM ``Field.value_ne_zero
            #[repExpr, hrepExpr, hrExpr, compiled.expression, divisor, originalProof]
          let coeffs ← mkAppM ``PolyQuot.coeffs #[compiled.expression]
          let zeroPoly ← FieldLiteral.ratPolyExpr (0 : DensePoly Rat)
          let goal ← mkAppM ``Ne #[coeffs, zeroPoly]
          let hcoeff ← mkDecideProof goal
          let hne ← mkAppM ``Field.coordinate_ne_zero #[compiled.expression, hcoeff]
          let proof := mkApp (← mkLambdaFVars #[inst] (mkApp reflect hne)) irred
          divisorProofs := divisorProofs.push proof
          divisorValues := divisorValues ++ [compiled.value]
          divisorExpressions := divisorExpressions.push
            (mkApp (← mkLambdaFVars #[inst] compiled.expression) irred)
          divisorIdentities := divisorIdentities.push
            (mkApp (← mkLambdaFVars #[inst] originalProof) irred)
        let mut compiled : Array (FieldCompile.Result p
            (SimpleRoot.ofSquare p s hw hp)) := #[]
        for coefficient in source.coefficients do
          compiled := compiled.push (← FieldCompile.compile pExpr rootExpr repExpr hrepExpr hrExpr
            leaf coefficient)
        let m := compiled.size
        let targetValues : Fin m → PolyQuot p (SimpleRoot.ofSquare p s hw hp) :=
          fun i => compiled[i.val].value
        let targetEntries := compiled.map (·.expression)
        let fieldType ← mkAppM ``PolyQuot #[pExpr, rootExpr]
        let zeroExpr := mkApp3 (mkConst ``PolyQuot.ofRat) pExpr rootExpr q((0 : Rat))
        let targetExpr ← FieldLiteral.finiteExpr fieldType targetEntries zeroExpr
        let formula ← FieldRuntime.evalFormula m source.formula
        let some (quantifier, qf) := oneQuantifier formula |
          throwError "rcf: expected one real quantifier over a matrix"
        let formulaWhnf ← whnf source.formula
        let matrixExpr ← whnf formulaWhnf.getAppArgs.back!
        let qfExpr := matrixExpr.getAppArgs.back!
        let targetFin := mkApp (mkConst ``Fin) (mkNatLit m)
        let targetEqGoal ← withLocalDeclD `i targetFin fun i => do
          let interpreted ← mkAppM ``Field.value #[repExpr, mkApp targetExpr i]
          mkForallFVars #[i] (← mkEq interpreted (mkApp source.valuation i))
        let pointwise ← FieldLiteral.proveFinCases targetEqGoal (compiled.map (·.proof))
        let eqVal ← mkAppM ``funext #[pointwise]
        let close (expression : Expr) : MetaM Expr := do
          let expression ← instantiateMVars expression
          return mkApp (← mkLambdaFVars #[inst] expression) irred
        return {
          source, polynomial := p, square := s, witness := hw, precision := hp,
          checked := common.generator.checked, arity := m, values := targetValues,
          formula := qf, quantifier, polynomialExpr := pExpr, rootExpr,
          valuesExpr := ← close targetExpr, formulaExpr := qfExpr,
          irreducibleExpr := irred, valuationProof := ← close eqVal, divisorProofs,
          divisors := divisorValues, divisorExpressions, divisorIdentities
        }
    else throwError "rcf: common square has insufficient precision"
  else throwError "rcf: common square failed its root witness"

-- Retain full fresh-record validation as a matched proof-cost control. The
-- editable public preparation API always validates independently of this option.
register_option rcf.algebraic.validateFresh : Bool := {
  defValue := false
  descr := "diagnostic comparison: repeat prepared-input validation for fresh tactic data"
}

/-- Assemble only factory-produced data. No editable environment is accepted
at this private boundary; the dispatcher checks the complete original proof. -/
private meta def proveFresh (prepared : Coefficients.Environment) : MetaM Expr :=
    withNewMCtxDepth <| withOptions (fun options =>
      debug.skipKernelTC.set (Elab.async.set options false) false) do
    for proof in [prepared.source.proof, prepared.valuationProof, prepared.irreducibleExpr] do
      let _ ← Hex.RCF.checkExpr `Hex.RCF.RealCoefficients.CommonTactic.proveFresh proof
    for i in [:prepared.source.divisors.size] do
      let divisor : Q(ℝ) := prepared.source.divisors[i]!
      let _ ← withoutModifyingEnv <| Hex.RCF.checkProof
        `Hex.RCF.RealCoefficients.CommonTactic.guard q($divisor ≠ 0) prepared.divisorProofs[i]!
    let _ : ZPoly.CheckedIrreducible prepared.polynomial := prepared.checked
    let instType ← mkAppM ``ZPoly.CheckedIrreducible #[prepared.polynomialExpr]
    let fixed ← withLocalDecl `inst .instImplicit instType fun inst => do
      let proof ← FieldLiteral.proveRefining prepared.polynomialExpr prepared.rootExpr
        prepared.valuesExpr prepared.formulaExpr prepared.values prepared.formula prepared.quantifier
      return mkApp (← mkLambdaFVars #[inst] proof) prepared.irreducibleExpr
    let congr ← withLocalDeclD `ρ (← inferType prepared.source.valuation) fun ρ => do
      let body ← mkAppM ``RealFormula.Prenex.toProp #[prepared.source.formula, ρ]
      mkAppM ``congrArg #[← mkLambdaFVars #[ρ] body, prepared.valuationProof]
    let specialized ← mkAppM ``Eq.mp #[congr, fixed]
    mkAppM ``Iff.mp #[prepared.source.proof, specialized]

private meta def prove (source : Reify.Source) (leafSources : Array Expr)
    (plans : Array SourcePlan) : MetaM Expr := do
  profileitM Exception "rcf algebraic frontend" (← getOptions)
    (do
      let prepared ← prepareField source leafSources plans
      if rcf.algebraic.validateFresh.get (← getOptions) then prepared.prove
      else proveFresh prepared)

private meta def proveRational (source : Reify.Source) : MetaM Expr := do
  Tactic.checkGuards source
  let proof ← Hex.RCF.proveRationalGoal source.sentence
  mkAppM ``Iff.mp #[source.sentenceProof, proof]

private meta partial def gatherCore (source : Expr) (leaves : Array Expr) :
    MetaM (Option (Array Expr)) := do
  if ← eligible source then
    return some (if leaves.contains source then leaves else leaves.push source)
  let e := source.consumeMData
  let args := e.getAppArgs
  let op := e.getAppFn.constName?
  if [``HAdd.hAdd, ``HSub.hSub, ``HMul.hMul, ``HDiv.hDiv].any (op == some ·) &&
      args.size == 6 then
    let some left ← gatherCore args[4]! leaves | return none
    return ← gatherCore args[5]! left
  if [``Neg.neg, ``Inv.inv].any (op == some ·) && args.size == 3 then
    return ← gatherCore args[2]! leaves
  if e.isAppOfArity ``HPow.hPow 6 then
    if (← inferType args[5]!).isConstOf ``Nat then
      return ← gatherCore args[4]! leaves
  let rational ← observing? do
    let q : Q(ℝ) := e
    let _ ← Mathlib.Meta.NormNum.deriveRat q (_inst := q(inferInstance))
    pure ()
  if rational.isSome then return some leaves
  return none

-- Registered subjects are handled before this frontend. Lower the entire
-- scalar once, rather than lowering each suffix again during its traversal.
private meta def gather (source : Expr) (leaves : Array Expr) :
    MetaM (Option (Array Expr)) := do
  gatherCore (← Reify.lowerSources #[] source) leaves

private meta def sourcePlans (source : Reify.Source) :
    MetaM (Option (Array Expr × Array SourcePlan)) := do
  for expression in #[source.proof, source.sentenceProof] ++
      source.coefficients ++ source.divisors do
    let _ ← Hex.RCF.checkExpr `Hex.RCF.RealCoefficients.CommonTactic.sourcePlans expression
  let mut leaves := #[]
  for scalar in source.coefficients ++ source.divisors do
    let some next ← gather scalar leaves | return none
    leaves := next
  let plans ← profileitM Exception "rcf source authentication" (← getOptions) do
    let mut plans : Array SourcePlan := #[]
    for scalar in leaves do
      let some plan ← sourcePlan? scalar |
        throwError "rcf: internal: eligible leaf has no plan"
      plans := plans.push plan
    pure plans
  return some (leaves, plans)

/-- Prepare an exact selected-field environment without root/cell production.
The rational-only input remains with the existing rational solver. -/
private meta def prepareSource (source : Reify.Source) : MetaM (Option Coefficients.Environment) := do
  let some (leaves, plans) ← sourcePlans source | return none
  if leaves.isEmpty then return none
  let prepared ← (← prepareField source leaves plans).instantiate
  prepared.checkDomains
  return some prepared

@[rcf_handler] meta def handle : Handler := fun target => do
  unless ← candidate target do return .declined
  if ← Registration.deferExact target then return .declined
  let source ← match ← Reify.prepare target with
    | .ok source => pure source
    | .error (.unsupported _ _) => return .declined
    | .error error => return .failed (Hex.RealFormula.Reify.Error.toMessageData error)
  if source.coefficients.isEmpty && (← rationalGuards source.divisors) then
    -- Checked constructor lowering retains all original guards.
    -- False, replay and resource failures from the base remain terminal.
    return .proved (← proveRational source)
  if source.coefficients.size == 1 then
    if (← Tactic.handlesCoefficient source.coefficients[0]!) &&
        (← rationalGuards source.divisors) then return .declined
  let some (leaves, plans) ← sourcePlans source | return .declined
  if leaves.isEmpty then return .proved (← proveRational source)
  return .proved (← prove source leaves plans)

end Hex.RCF.RealCoefficients.CommonTactic

namespace Hex.RCF.RealCoefficients.Coefficients
open Lean Meta

/-- Recognize and authenticate the exact algebraic fragment of a one-variable
source goal, in its original coefficient order, before goal certificate search.
Purely rational goals use the base solver; caller-registered bounds use the
finite-certificate frontend. A structured decline or exception restores the
metavariable and environment state. No failure starts a different solver. -/
meta def prepare (target : Expr) :
    MetaM (Except Hex.RealFormula.Reify.Error Environment) := do
  let saved ← saveState
  let (result, _) ← tryFinally' (withNewMCtxDepth <| withOptions (fun options =>
      debug.skipKernelTC.set (Elab.async.set options false) false) do
    let source ← match ← Reify.prepare target with
      | .ok source => pure source
      | .error error => return .error error
    let some prepared ← CommonTactic.prepareSource source |
      return .error (.unsupported target "no supported selected-field coefficient environment")
    return .ok prepared)
    (fun result => do
      match result with
      | some (.ok _) => modify fun state => {state with
          mctx := saved.meta.mctx, postponed := saved.meta.postponed,
          zetaDeltaFVarIds := saved.meta.zetaDeltaFVarIds}
      | _ => saved.restore)
  return result

end Hex.RCF.RealCoefficients.Coefficients
