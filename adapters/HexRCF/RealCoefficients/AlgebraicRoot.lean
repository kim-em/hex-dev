/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public meta import HexRCF.RealCoefficients.CommonPresentation
public meta import HexRCF.RealCoefficients.FieldCompile
public meta import HexRCF.RealCoefficients.Preparation
public meta import HexRCF.RealCoefficients.RationalRoot

public meta section

/-! Authenticate closed algebraic-base root aliases with frozen selected-root evidence. -/

namespace Hex.RCF.RealCoefficients.AlgebraicRoot
open Hex Lean Meta Qq

/-- Reduce each proposed literal certificate with the ordinary kernel. -/
private meta def kernelDecide (goal : Expr) : MetaM Expr :=
    withOptions (fun options =>
      debug.skipKernelTC.set (Elab.async.set options false) false) do
  let candidate ← mkFreshExprMVar goal
  let remaining ← Lean.Elab.runTactic' candidate.mvarId!
    (← `(tactic|
      (simp only [CommonPresentation.checkEntry, CommonPresentation.checkEquation,
        CommonPresentation.checkDisc, CommonPresentation.checkRoot,
        CommonPresentation.evalAt, DensePoly.evalCoeffList, Field.checkSignTable,
        LiteralSign.Table.check, LiteralSign.Entry.check, Sturm.check,
        TarskiCertificate.check_eq, SignedRemainderChain.check,
        ← Array.all_toList, Array.toList_range, Bool.and_eq_true];
       repeat' (any_goals (apply And.intro)); all_goals decide +kernel)))
  unless remaining.isEmpty do throwError "rcf: algebraic-root literal evidence did not check"
  return ← instantiateMVars candidate

structure Identity where
  value : RealAlgebraicNumber
  expression : Expr
  proof : Expr
  witness : Expr
  precision : Expr
  /-- Degree of the field used to authenticate this source, before root production. -/
  fieldDegree : Nat

private meta def identifyBase (source : Expr)
    (prepareBase : Expr → MetaM (Except Hex.RealFormula.Reify.Error Coefficients.Environment))
    (degree degreeLimit : Nat) (cache : Option (IO.Ref (ExprMap Identity))) :
    ExceptT Hex.RealFormula.Reify.Error MetaM Identity := do
  if degree > degreeLimit then
    throwThe Hex.RealFormula.Reify.Error (.budget
      {dimension := .exponent, limit := degreeLimit, consumed := 0, requested := degree})
  if let some cache := cache then
    if let some authenticated := (← cache.get)[source]? then
      -- Entries retain ordinary proof auxiliaries. A failed recursive
      -- preparation is terminal for the whole call; the top-level cache is
      -- then discarded. Reject an entry whose environment was rolled back.
      unless authenticated.proof.getAppFn.constName?.any (← getEnv).contains do
        throwThe Hex.RealFormula.Reify.Error (.internal "cached base proof is unavailable")
      let requested := degree * authenticated.fieldDegree
      if requested > degreeLimit then
        throwThe Hex.RealFormula.Reify.Error (.budget
          {dimension := .exponent, limit := degreeLimit,
           consumed := authenticated.fieldDegree, requested})
      return authenticated
  let x : Q(ℝ) ← pure source
  let target := q(∀ _ : ℝ, 0 ≤ $x)
  let outcome : Except Hex.RealFormula.Reify.Error Coefficients.Environment ←
    liftM (prepareBase target)
  let environment ← match outcome with
    | .ok environment => pure environment
    | .error (.unsupported subject reason) =>
      throwThe Hex.RealFormula.Reify.Error
        (.unsupported (if subject == target then source else subject) reason)
    | .error error => throwThe Hex.RealFormula.Reify.Error error
  let requested := degree * environment.polynomial.natDegree
  if requested > degreeLimit then
    throwThe Hex.RealFormula.Reify.Error (.budget
      {dimension := .exponent, limit := degreeLimit,
       consumed := environment.polynomial.natDegree, requested := requested})
  let rootArgs := environment.rootExpr.getAppArgs
  let rep ← mkAppM ``Field.literalRep rootArgs
  let hrep ← mkAppM ``Field.literalRep_mk rootArgs
  let square : Q(DyadicSquare) := rootArgs[1]!
  let realAxis ← mkDecideProof (q(($square).meetsRealAxis = true) : Q(Prop))
  let hreal ← mkAppM ``Field.literalRep_real (rootArgs.push realAxis)
  let leaf (e : Expr) : MetaM (Option (FieldCompile.Result environment.polynomial
      (SimpleRoot.ofSquare environment.polynomial environment.square
        environment.witness environment.precision))) := do
    let some index := environment.source.coefficients.idxOf? e | return none
    if hindex : index < environment.arity then
      let indexExpr ← mkAppM ``Fin.mk #[mkNatLit index,
        ← mkDecideProof (← mkLt (mkNatLit index) (mkNatLit environment.arity))]
      return some ⟨environment.values ⟨index, hindex⟩,
        mkApp environment.valuesExpr indexExpr,
        ← mkAppM ``congrFun #[environment.valuationProof, indexExpr]⟩
    throwError "base coefficient index is out of range"
  let instType ← mkAppM ``ZPoly.CheckedIrreducible #[environment.polynomialExpr]
  let _ : ZPoly.CheckedIrreducible environment.polynomial := environment.checked
  let outcome : Except Hex.RealFormula.Reify.Error Identity ←
      withLocalDecl `inst .instImplicit instType fun inst =>
        (show ExceptT Hex.RealFormula.Reify.Error MetaM Identity from do
          let result ← FieldCompile.compile environment.polynomialExpr environment.rootExpr
            rep hrep hreal leaf source
          let converted := result.value.toAlgebraicNumber
            (Field.literalRep environment.polynomial environment.square
              environment.witness environment.precision)
            (Field.literalRep_mk environment.polynomial environment.square
              environment.witness environment.precision)
          let some native := RealAlgebraicNumber.ofAlgebraic? converted |
            throwThe Hex.RealFormula.Reify.Error
              (.providerFailure (.internal "authenticated base conversion was not real") #[])
          let baseP := native.toAlgebraic.p
          let baseSquare := native.toAlgebraic.rep.1.square
          unless Decidable.decide (atomWitness baseP baseSquare) &&
              Decidable.decide ((mahlerPrec baseP : Int) ≤ baseSquare.prec) do
            throwThe Hex.RealFormula.Reify.Error
              (.providerFailure (.internal "algebraic base has no literal selected-root witness") #[])
          let some table := FieldBuild.buildTable environment.polynomial environment.square
              environment.witness environment.precision
              [CommonPresentation.discSlack baseSquare result.value] |
            throwThe Hex.RealFormula.Reify.Error
              (.providerFailure (.internal "base embedding sign production failed") #[])
          unless CommonPresentation.checkEntry environment.witness environment.precision
              table (ZPoly.toRatPoly baseP) baseSquare result.value do
            throwThe Hex.RealFormula.Reify.Error
              (.providerFailure (.internal "computed base embedding did not match authenticated source") #[])
          let pExpr : Q(ZPoly) ← FieldLiteral.zpolyExpr baseP
          let sExpr : Q(DyadicSquare) ← FieldLiteral.squareExpr baseSquare
          let hw ← mkDecideProof (q(atomWitness $pExpr $sExpr) : Q(Prop))
          let hp ← mkDecideProof (q((mahlerPrec $pExpr : Int) ≤ ($sExpr).prec) : Q(Prop))
          let sourceRep ← mkAppM ``Field.literalRep #[pExpr, sExpr, hw, hp]
          let sourceRoot ← mkAppM ``HexRootsTheory.RefinedIsolation.root #[sourceRep]
          let value : Q(ℝ) ← mkAppM ``Complex.re #[sourceRoot]
          let tableExpr ← FieldLiteral.signTableExpr environment.polynomialExpr
            environment.rootExpr table
          let basePoly ← mkAppM ``ZPoly.toRatPoly #[pExpr]
          let accepted ← kernelDecide
            (← mkEq (← mkAppM ``CommonPresentation.checkEntry
              #[rootArgs[2]!, rootArgs[3]!, tableExpr, basePoly, sExpr,
                result.expression]) q(true))
          let entryIdentity ← mkAppM ``CommonPresentation.checkEntry_sound_of_selected
            #[rootArgs[2]!, rootArgs[3]!, tableExpr, basePoly, sExpr, pExpr, hw, hp,
              ← mkEqRefl basePoly, value, ← mkEqRefl value, result.expression, accepted]
          let identity ← mkEqTrans (← mkEqSymm entryIdentity) result.proof
          let proof := mkApp (← mkLambdaFVars #[inst] identity) environment.irreducibleExpr
          let proof : Q($value = $x) ← Hex.RCF.checkProof
            `Hex.RCF.RealCoefficients.AlgebraicRoot q($value = $x) proof
          return ⟨native, value, proof, hw, hp, environment.polynomial.natDegree⟩).run
  let authenticated ← match outcome with
    | .ok authenticated => pure authenticated
    | .error error => throwThe Hex.RealFormula.Reify.Error error
  if let some cache := cache then
    cache.modify (·.insert source authenticated)
  return authenticated

/-- Authenticate the selected root of an algebraic base using only recorded
polynomial, power and sign evidence in the quoted ordinary proof. -/
meta def identify (source base : Expr) (degree : Nat)
    (prepareBase : Expr → MetaM (Except Hex.RealFormula.Reify.Error Coefficients.Environment))
    (degreeLimit : Nat) (cache : Option (IO.Ref (ExprMap Identity)) := none) :
    ExceptT Hex.RealFormula.Reify.Error MetaM Identity := do
  if degree == 0 then
    throwThe Hex.RealFormula.Reify.Error (.unsupported source "zero root degree")
  let authenticated ← identifyBase base prepareBase degree degreeLimit cache
  if degree == 1 then
    let source : Q(ℝ) ← pure source
    let base : Q(ℝ) ← pure base
    let normalize ← mkFreshExprMVar q($base = $source)
    let remaining ← Elab.runTactic' normalize.mvarId!
      (← `(tactic| norm_num [Real.rpow_one]))
    unless remaining.isEmpty do
      throwThe Hex.RealFormula.Reify.Error (.internal "degree-one root notation did not normalize")
    let proof ← mkEqTrans authenticated.proof (← instantiateMVars normalize)
    let selected : Q(ℝ) ← pure authenticated.expression
    let proof ← Hex.RCF.checkProof `Hex.RCF.RealCoefficients.AlgebraicRoot.degreeOne
      q($selected = $source) proof
    return {authenticated with proof}
  let value ← if nonnegative : 0 ≤ authenticated.value then
      pure (Coefficients.root authenticated.value degree nonnegative)
    else do
      throwThe Hex.RealFormula.Reify.Error
        (.unsupported base "negative algebraic root base")
  let p := value.toAlgebraic.p
  let s := value.toAlgebraic.rep.1.square
  if hw : atomWitness p s then
    if hp : (mahlerPrec p : Int) ≤ s.prec then
      let v := PolyQuot.ofSquare p s (DensePoly.ofList [0, 1]) hw hp
      let powered := v ^ degree
      let baseP := authenticated.value.toAlgebraic.p
      let baseSquare := authenticated.value.toAlgebraic.rep.1.square
      let some table := FieldBuild.buildTable p s hw hp
          [v, CommonPresentation.discSlack baseSquare powered] |
        throwThe Hex.RealFormula.Reify.Error
          (.providerFailure (.internal "root/base sign production failed") #[])
      unless CommonPresentation.checkEntry hw hp table (ZPoly.toRatPoly baseP)
          baseSquare powered && CommonPresentation.checkRoot table v powered degree do
        throwThe Hex.RealFormula.Reify.Error
          (.providerFailure (.internal "proposed root has the wrong base or branch") #[])
      let pe : Q(ZPoly) ← FieldLiteral.zpolyExpr p
      let se : Q(DyadicSquare) ← FieldLiteral.squareExpr s
      let hwe ← mkDecideProof (q(atomWitness $pe $se) : Q(Prop))
      let hpe ← mkDecideProof (q((mahlerPrec $pe : Int) ≤ ($se).prec) : Q(Prop))
      let root ← mkAppM ``SimpleRoot.ofSquare #[pe, se, hwe, hpe]
      let rep ← mkAppM ``Field.literalRep #[pe, se, hwe, hpe]
      let ve ← FieldLiteral.fieldExpr pe root v
      let poweredExpr ← FieldLiteral.fieldExpr pe root powered
      let tableExpr ← FieldLiteral.signTableExpr pe root table
      let spe : Q(ZPoly) ← FieldLiteral.zpolyExpr baseP
      let sse : Q(DyadicSquare) ← FieldLiteral.squareExpr baseSquare
      let hswe := authenticated.witness
      let hspe := authenticated.precision
      let spoly ← mkAppM ``ZPoly.toRatPoly #[spe]
      let acceptedBase ← kernelDecide
        (← mkEq (← mkAppM ``CommonPresentation.checkEntry
          #[hwe, hpe, tableExpr, spoly, sse, poweredExpr]) q(true))
      let baseIdentity ← mkAppM ``CommonPresentation.checkEntry_sound_of_selected
        #[hwe, hpe, tableExpr, spoly, sse, spe, hswe, hspe,
          ← mkEqRefl spoly, base, authenticated.proof, poweredExpr, acceptedBase]
      let de : Q(ℕ) := mkNatLit degree
      let accepted ← kernelDecide
        (← mkEq (← mkAppM ``CommonPresentation.checkRoot
          #[tableExpr, ve, poweredExpr, de]) q(true))
      let checked ← mkAppM ``CommonPresentation.checkEntry_signs
        #[hwe, hpe, tableExpr, spoly, sse, poweredExpr, acceptedBase]
      let hre ← mkAppM ``CommonPresentation.signTable_real #[hwe, hpe, tableExpr, checked]
      let rootIdentity ← mkAppM ``CommonPresentation.checkRoot_sound
        #[hwe, hpe, hre, tableExpr, checked, ve, poweredExpr, base,
          baseIdentity, de, accepted]
      let source : Q(ℝ) ← pure source
      let base : Q(ℝ) ← pure base
      let normalize ← mkFreshExprMVar q($base ^ (1 / ($de : ℝ)) = $source)
      let remaining ← Elab.runTactic' normalize.mvarId!
        (← `(tactic| norm_num [Real.sqrt_eq_rpow]))
      unless remaining.isEmpty do
        throwThe Hex.RealFormula.Reify.Error (.internal "source root notation did not normalize")
      let identity ← mkEqTrans rootIdentity (← instantiateMVars normalize)
      let generator ← mkAppM ``CommonPresentation.literalGenerator #[hwe, hpe, hre]
      let identity ← mkEqTrans (← mkEqSymm generator) identity
      let literalRoot ← mkAppM ``HexRootsTheory.RefinedIsolation.root #[rep]
      let selected : Q(ℝ) ← mkAppM ``Complex.re #[literalRoot]
      let proof : Q($selected = $source) ← Hex.RCF.checkProof
        `Hex.RCF.RealCoefficients.AlgebraicRoot q($selected = $source) identity
      return ⟨value, selected, proof, hwe, hpe, p.natDegree⟩
  throwThe Hex.RealFormula.Reify.Error
    (.providerFailure (.internal "proposed root has no literal selected-root witness") #[])

end Hex.RCF.RealCoefficients.AlgebraicRoot
