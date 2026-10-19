/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public meta import HexRCF.RealCoefficients.FieldDecisionProgress
public meta import HexRCF.RealCoefficients.FieldBuildBudget
public meta import HexRCF.RealCoefficients.FiniteReplay
public meta import HexRCF.RealCoefficients.FieldRefinement
public meta import HexRCF.RealCoefficients.FieldIndex
public meta import HexRealAlgebraicTheory.Laws
public meta import Lean
public meta import HexRCF.Tactic

public meta section

/-! Embed computed fixed-field certificates as literal Lean expressions. -/

namespace Hex.RCF.RealCoefficients.FieldLiteral

open Hex Lean Meta

register_option rcf.algebraic.directDepth : Nat := {
  defValue := 256
  descr := "maximum direct algebraic interval bisection depth"
}

register_option rcf.algebraic.maxDoublings : Nat := {
  defValue := 10
  descr := "maximum fixed-field enclosure attempts at precisions 1, 2, 4, ... bits"
}

-- A comparison control for literal quotation, with the same replay checker
-- and soundness theorem in both modes. This does not change solver dispatch.
register_option rcf.algebraic.reducedLiterals : Bool := {
  defValue := false
  descr := "quote fixed-field coordinates directly instead of reducing them again"
}

-- The false arm produces full queries as a reproducible comparison control.
-- Only tactic producers use this control. Frozen quotation and the explicit
-- prepared replay API always preserve the supplied evidence.
register_option rcf.algebraic.intervalSigns : Bool := {
  defValue := true
  descr := "produce exact Horner signs on the authenticated generator interval"
}

-- Compare one Boolean replay goal with separately checked conjuncts.
register_option rcf.algebraic.singleReplay : Bool := {
  defValue := false
  descr := "check the full fixed-field certificate in one kernel decision goal"
}

register_option rcf.algebraic.monicCore : Bool := {
  defValue := true
  descr := "normalize the proposed carrier core before checked root isolation"
}

register_option rcf.algebraic.signRefinements : Nat := {
  defValue := 0
  descr := "maximum checked generator-window refinement steps for inconclusive Horner signs"
}

register_option rcf.algebraic.indexSigns : Bool := {
  defValue := true
  descr := "retrieve fixed-field replay signs through a checked positional index"
}

private def indexExpr : LiteralSign.Index → Expr
  | .empty => mkConst ``LiteralSign.Index.empty
  | .node position left right =>
      mkApp3 (mkConst ``LiteralSign.Index.node) (mkNatLit position)
        (indexExpr left) (indexExpr right)

private def arrayLit (ty : Expr) (xs : List Expr) : Expr :=
  let nil := mkApp (mkConst ``List.nil [Level.zero]) ty
  let list := xs.foldr
    (fun x rest => mkApp3 (mkConst ``List.cons [Level.zero]) ty x rest) nil
  mkApp2 (mkConst ``List.toArray [Level.zero]) ty list

private def listLit (ty : Expr) (xs : List Expr) : Expr :=
  xs.foldr (fun x rest => mkApp3 (mkConst ``List.cons [Level.zero]) ty x rest)
    (mkApp (mkConst ``List.nil [Level.zero]) ty)

private def optionLit (ty : Expr) : Option Expr → Expr
  | none => mkApp (mkConst ``Option.none [Level.zero]) ty
  | some value => mkApp2 (mkConst ``Option.some [Level.zero]) ty value

private def vectorLit (ty : Expr) {n : Nat} (xs : Vector Expr n) : MetaM Expr := do
  let data := arrayLit ty xs.toArray.toList
  let proof ← mkAppM ``Eq.refl #[mkNatLit n]
  mkAppM ``Vector.mk #[data, proof]

/-- Shared literal evidence reductions for tactic and explicit finite replay.
Each caller supplies its own envelope and verdict equations. -/
meta def evidenceLemmas : MetaM (TSyntaxArray ``Parser.Tactic.simpLemma) := do
  return #[← `(Parser.Tactic.simpLemma| Field.checkSignTable),
    ← `(Parser.Tactic.simpLemma| LiteralSign.Table.check),
    ← `(Parser.Tactic.simpLemma| LiteralSign.Window.check),
    ← `(Parser.Tactic.simpLemma| LiteralSign.Entry.check),
    ← `(Parser.Tactic.simpLemma| RadicalCert.check),
    ← `(Parser.Tactic.simpLemma| FieldRootSigns.Table.check),
    ← `(Parser.Tactic.simpLemma| IsolationReplay.check),
    ← `(Parser.Tactic.simpLemma| Sturm.check),
    ← `(Parser.Tactic.simpLemma| TarskiCertificate.check_eq),
    ← `(Parser.Tactic.simpLemma| SignedRemainderChain.check),
    ← `(Parser.Tactic.simpLemma| ← Array.all_toList),
    ← `(Parser.Tactic.simpLemma| Array.toList_range)]

private def ratExpr (q : Rat) : MetaM Expr :=
  mkAppM ``mkRat #[mkIntLit q.num, mkNatLit q.den]

private def dyadicExpr (d : Dyadic) : MetaM Expr := do
  let q := d.toRat
  let base ← mkAppM ``Dyadic.ofInt #[mkIntLit q.num]
  if q.den = 1 then return base
  mkAppM ``HShiftRight.hShiftRight #[base, mkIntLit (Int.ofNat q.den.log2)]

private def intervalExpr (interval : DyadicInterval) : MetaM Expr := do
  let lower ← dyadicExpr interval.lower
  let upper ← dyadicExpr interval.upper
  let orderTy ← mkAppM ``LT.lt #[lower, upper]
  let order ← mkDecideProof orderTy
  mkAppM ``DyadicInterval.mk #[lower, upper, order]

private def denseExpr {E : Type} [Zero E] [DecidableEq E]
    (elem : E → MetaM Expr) (poly : DensePoly E) : MetaM Expr := do
  let coeffs ← poly.toArray.toList.mapM elem
  let ty ← inferType (← elem (0 : E))
  mkAppM ``DensePoly.ofCoeffs #[arrayLit ty coeffs]

/-- Quote a reduced field coordinate as literal rational coefficients. -/
meta def fieldExpr {p : ZPoly} {root : SimpleRoot p}
    (pExpr rootExpr : Expr) (value : PolyQuot p root) : MetaM Expr := do
  let coeffs ← denseExpr ratExpr value.coeffs
  if !(rcf.algebraic.reducedLiterals.get (← getOptions)) then
    return ← mkAppM ``PolyQuot.reduce #[pExpr, rootExpr, coeffs]
  let modulusDegree ← mkAppM ``DensePoly.natDegree #[pExpr]
  let bound ← mkDecideProof
    (← mkLt (mkNatLit (value.coeffs.toArray.size - 1)) modulusDegree)
  let bound ← mkAppM ``Coefficients.degree_bound #[coeffs.appArg!, pExpr, bound]
  mkAppOptM ``PolyQuot.mk #[some pExpr, some rootExpr, some coeffs, some bound]

/-- The defining integer polynomial as printable coefficient data. -/
meta def zpolyExpr (p : ZPoly) : MetaM Expr :=
  denseExpr (fun (z : Int) => pure (mkIntLit z)) p

/-- A rational coordinate polynomial as printable coefficient data. -/
meta def ratPolyExpr (p : DensePoly Rat) : MetaM Expr :=
  denseExpr ratExpr p

/-- The selected dyadic square as printable data. -/
meta def squareExpr (s : DyadicSquare) : MetaM Expr := do
  mkAppM ``DyadicSquare.mk
    #[← dyadicExpr s.re, ← dyadicExpr s.im, mkIntLit s.prec]

/-- A literal finite coefficient valuation. The default is never selected by
a `Fin n` argument; it makes the expression total without a proof-bearing
array lookup in every formula occurrence. -/
meta def valuesExpr {p : ZPoly} {root : SimpleRoot p} {n : Nat}
    (pExpr rootExpr : Expr) (values : Fin n → PolyQuot p root) : MetaM Expr := do
  let ty ← inferType (← fieldExpr pExpr rootExpr (0 : PolyQuot p root))
  let entries ← (List.finRange n).mapM fun i => fieldExpr pExpr rootExpr (values i)
  let literals := listLit ty entries
  let fallback ← fieldExpr pExpr rootExpr (0 : PolyQuot p root)
  withLocalDeclD `i (mkApp (mkConst ``Fin) (mkNatLit n)) fun i => do
    let index ← mkAppM ``Fin.val #[i]
    let body ← mkAppM ``List.getD #[literals, index, fallback]
    mkLambdaFVars #[i] body

/-- Reify an ordered finite family as printable entries. The fallback cannot
be selected by a `Fin n` index. -/
meta def finiteExpr (ty : Expr) (entries : Array Expr) (fallback : Expr) : MetaM Expr := do
  let literals := listLit ty entries.toList
  withLocalDeclD `i (mkApp (mkConst ``Fin) (mkNatLit entries.size)) fun i => do
    let index ← mkAppM ``Fin.val #[i]
    let body ← mkAppM ``List.getD #[literals, index, fallback]
    mkLambdaFVars #[i] body

/-- A finite iterated-quadratic-norm irreducibility certificate as constructor
data, independent of the certificate search. -/
meta def quadraticCertExpr (cert : QuadraticNormCertificate) : MetaM Expr :=
  mkAppM ``QuadraticNormCertificate.mk
    #[mkIntLit cert.translation,
      arrayLit (mkConst ``Int) (cert.radicands.toList.map mkIntLit)]

/-- Assemble index-specific ordinary proofs into an ordered `Fin n` family.
Each branch is typechecked against the original indexed proposition. -/
meta def proveFinCases (goal : Expr) (proofs : Array Expr) : MetaM Expr := do
  let candidate ← mkFreshExprMVar goal
  let cases ← Lean.Elab.runTactic' candidate.mvarId!
    (← `(tactic| intro i; fin_cases i))
  unless cases.length == proofs.size do
    throwError "rcf: finite proof count differs from the source coefficients"
  for index in [:cases.length] do
    let caseGoal := cases[index]!
    let proof := proofs[index]!
    caseGoal.withContext do
      unless ← isDefEq (← inferType proof) (← caseGoal.getType) do
        throwError "rcf: source proof at index {index} does not match its literal entry\nactual: {← ppExpr (← inferType proof)}\nexpected: {← ppExpr (← caseGoal.getType)}"
      caseGoal.assign proof
  return ← instantiateMVars candidate

private def endpointExpr {E : Type} (ty : Expr) (elem : E → MetaM Expr) :
    Endpoint E → MetaM Expr
  | .negInf => return mkApp (mkConst ``Endpoint.negInf [Level.zero]) ty
  | .posInf => return mkApp (mkConst ``Endpoint.posInf [Level.zero]) ty
  | .finite value => return mkApp2 (mkConst ``Endpoint.finite [Level.zero]) ty (← elem value)

private def stepExpr {E : Type} [Zero E] [DecidableEq E]
    (elem : E → MetaM Expr) (step : RemainderStep E) : MetaM Expr := do
  mkAppM ``RemainderStep.mk
    #[← elem step.leftScale, ← denseExpr elem step.quotient, ← elem step.rightScale]

private def chainExpr {E : Type} [Zero E] [DecidableEq E]
    (elem : E → MetaM Expr) (chain : SignedRemainderChain E) : MetaM Expr := do
  let ty ← inferType (← elem (0 : E))
  let polyTy ← inferType (← denseExpr elem (0 : DensePoly E))
  let stepTy ← inferType (← stepExpr elem chain.initial)
  let entries ← chain.chain.toList.mapM (denseExpr elem)
  let steps ← chain.steps.toList.mapM (stepExpr elem)
  let terminal ← chain.terminal.mapM fun pair => do
    mkAppM ``Prod.mk #[← elem pair.1, ← denseExpr elem pair.2]
  let pairTy ← mkAppM ``Prod #[ty, polyTy]
  mkAppM ``SignedRemainderChain.mk
    #[arrayLit polyTy entries,
      arrayLit (mkConst ``Nat) (chain.degrees.toList.map mkNatLit),
      ← stepExpr elem chain.initial, arrayLit stepTy steps,
      optionLit pairTy terminal]

private def tarskiExpr {E : Type} [Zero E] [DecidableEq E]
    (elem : E → MetaM Expr) (cert : TarskiCertificate E E Unit) : MetaM Expr := do
  let ty ← inferType (← elem (0 : E))
  mkAppM ``TarskiCertificate.mk
    #[mkConst ``Unit.unit, ← denseExpr elem cert.head,
      ← denseExpr elem cert.queryPoly,
      ← endpointExpr ty elem cert.lower, ← endpointExpr ty elem cert.upper,
      ← chainExpr elem cert.squarefree, ← chainExpr elem cert.remainders,
      arrayLit (mkConst ``Int) (cert.lowerSigns.toList.map mkIntLit),
      arrayLit (mkConst ``Int) (cert.upperSigns.toList.map mkIntLit),
      mkNatLit cert.lowerVariations, mkNatLit cert.upperVariations,
      mkIntLit cert.value]

private def isolationExpr {E : Type} [Zero E] [DecidableEq E]
    (elem : E → MetaM Expr) (cert : IsolationReplay E Unit) : MetaM Expr := do
  let intervals ← cert.isolations.intervals.toList.mapM intervalExpr
  let isolation ← mkAppM ``IsolationCert.mk
    #[arrayLit (mkConst ``DyadicInterval) intervals]
  let total ← tarskiExpr elem cert.total
  let queryTy ← inferType total
  let counts ← cert.counts.mapM (tarskiExpr elem)
  mkAppM ``IsolationReplay.mk
    #[isolation, total, ← vectorLit queryTy counts]

private def radicalExpr {E : Type} [Zero E] [DecidableEq E]
    (elem : E → MetaM Expr) (cert : RadicalCert E Unit) : MetaM Expr := do
  mkAppM ``RadicalCert.mk
    #[mkConst ``Unit.unit, ← denseExpr elem cert.core,
      ← denseExpr elem cert.quotient, ← denseExpr elem cert.cofactor,
      mkNatLit cert.exponent]

/-- Produce full queries for the comparison control before quotation. The
original table must already pass replay; this cannot repair invalid evidence. -/
meta def prepareSigns {p : ZPoly} {root : SimpleRoot p}
    (table : LiteralSign.Table (PolyQuot p root)) : MetaM (LiteralSign.Table (PolyQuot p root)) := do
  if rcf.algebraic.intervalSigns.get (← getOptions) then return table
  unless table.check PolyQuot.coeffs do
    throwError "rcf: original literal sign table failed replay"
  let interval := table.interval
  let some domain := Sturm.prepare Sturm.orderSign table.head
      (.finite interval.lower) (.finite interval.upper) |
    throwError "rcf: literal sign interval could not be prepared"
  let entries ← table.entries.mapM fun entry => do
    if entry.evidence.isSome then return entry
    let evidence := Sturm.certifyPrepared () domain entry.key.coeffs
    unless evidence.value == entry.value do
      throwError "rcf: literal sign query disagrees with its checked enclosure"
    return { entry with evidence := some evidence }
  let result := {table with entries}
  unless result.check PolyQuot.coeffs do
    throwError "rcf: produced literal sign table failed replay"
  return result

/-- Quote exactly the frozen sign table. No production option changes its
entries, and no preparation, gcd or query producer runs here. -/
meta def signTableExpr {p : ZPoly} {root : SimpleRoot p}
    (pExpr rootExpr : Expr) (table : LiteralSign.Table (PolyQuot p root)) : MetaM Expr := do
  let ty ← inferType (← fieldExpr pExpr rootExpr (0 : PolyQuot p root))
  let entryTy ← mkAppM ``LiteralSign.Entry #[ty]
  let evidenceTy ← inferType (← tarskiExpr ratExpr table.count)
  let entries ← table.entries.mapM fun entry => do
    let evidence ← entry.evidence.mapM (tarskiExpr ratExpr)
    mkAppM ``LiteralSign.Entry.mk
      #[← fieldExpr pExpr rootExpr entry.key, mkIntLit entry.value,
        optionLit evidenceTy evidence]
  let window ← table.refinement.mapM fun window => do
    mkAppM ``LiteralSign.Window.mk #[← ratExpr window.lower, ← ratExpr window.upper,
      ← tarskiExpr ratExpr window.count]
  mkAppM ``LiteralSign.Table.mk
    #[← denseExpr ratExpr table.head, ← ratExpr table.lower,
      ← ratExpr table.upper, ← tarskiExpr ratExpr table.count,
      listLit entryTy entries, optionLit (mkConst ``LiteralSign.Window) window]

/-- The atom expression comes from the already reflected source formula.
The default is unreachable for a row produced from that formula; replay still
checks the copied atom against every query polynomial. -/
private def atomAtExpr (formulaExpr : Expr) (n index : Nat) : MetaM Expr := do
  let polys ← mkAppM ``RealFormula.QF.polys #[formulaExpr]
  let atomTy ← mkAppM ``RealFormula.Poly #[mkNatLit n]
  let zeroInst ← synthInstance (mkApp (mkConst ``Zero [Level.zero]) atomTy)
  let fallback := mkApp2 (mkConst ``Zero.zero [Level.zero]) atomTy zeroInst
  mkAppM ``List.getD #[polys, mkNatLit index, fallback]

private def rootSignsExpr {p : ZPoly} {root : SimpleRoot p} {n roots : Nat}
    (pExpr rootExpr formulaExpr : Expr) (polys : List (RealFormula.Poly n))
    (table : FieldRootSigns.Table (PolyQuot p root) Unit n roots) : MetaM Expr := do
  unless table.entries.length = polys.length do
    throwError "rcf: root-sign row count differs from the source formula"
  let ty ← inferType (← fieldExpr pExpr rootExpr (0 : PolyQuot p root))
  let zeroClass ← synthInstance (mkApp (mkConst ``Zero [Level.zero]) ty)
  let eqClass := mkApp2 (mkConst ``PolyQuot.instDecidableEq) pExpr rootExpr
  let queryTy := mkAppN (mkConst ``TarskiCertificate
    [Level.zero, Level.zero, Level.zero])
    #[ty, ty, mkConst ``Unit, zeroClass, eqClass]
  let entryTy := mkAppN (mkConst ``FieldRootSigns.Entry [Level.zero, Level.zero])
    #[ty, mkConst ``Unit, mkNatLit n, mkNatLit roots, zeroClass, eqClass]
  let mut rows := []
  let mut index := 0
  for row in table.entries do
    let some expected := polys[index]? |
      throwError "rcf: root-sign atom index exceeds the source formula"
    unless row.atom = expected do
      throwError "rcf: root-sign atom order differs from the source formula"
    let atom ← atomAtExpr formulaExpr n index
    let certs ← row.evidence.mapM (tarskiExpr (fieldExpr pExpr rootExpr))
    let evidence ← vectorLit queryTy certs
    rows := (← mkAppM ``FieldRootSigns.Entry.mk #[atom, evidence]) :: rows
    index := index + 1
  mkAppM ``FieldRootSigns.Table.mk #[listLit entryTy rows.reverse]

/-- Embed all four parts of a successful fixed-field result without importing
the producer into the proof term. The checker independently validates every
field, query, sign and context binding after elaboration. -/
meta def resultExpr {p : ZPoly} {s : DyadicSquare}
    {hw : atomWitness p s} {hp : (mahlerPrec p : Int) ≤ s.prec}
    {n : Nat} (pExpr rootExpr formulaExpr : Expr)
    (formula : RealFormula.QF n)
    (data : FieldBuild.Result p s hw hp Unit n) : MetaM Expr := do
  let elem := fieldExpr pExpr rootExpr
  let radical ← radicalExpr elem data.radical
  let isolation ← isolationExpr elem data.isolation
  let roots ← rootSignsExpr pExpr rootExpr formulaExpr formula.polys data.rootSigns
  let signs ← signTableExpr pExpr rootExpr data.signs
  mkAppM ``FieldBuild.Result.mk #[radical, isolation, roots, signs]

private meta def checkPreview {p : ZPoly} {s : DyadicSquare}
    {hw : atomWitness p s} {hp : (mahlerPrec p : Int) ≤ s.prec}
    [ZPoly.CheckedIrreducible p] {n : Nat}
    (values : Fin n → PolyQuot p (SimpleRoot.ofSquare p s hw hp))
    (formula : RealFormula.QF (n + 1)) (quantifier : RealFormula.Quantifier)
    (extraSignKeys : List (PolyQuot p (SimpleRoot.ofSquare p s hw hp)))
    (validate : FieldBuild.Result p s hw hp Unit (n + 1) → MetaM Unit)
    (data : FieldBuild.Result p s hw hp Unit (n + 1)) : MetaM Unit := do
  validate data
  let keys := FieldBuild.signKeys values formula data.radical.core data.isolation
    data.rootSigns extraSignKeys
  unless keys.all (fun key => (data.signs.lookup? key).isSome) do
    throwError "rcf: fixed-field sign table omitted a replay or cell sign"
  let preview := match quantifier with
    | .forallReal => data.allValue values formula
    | .existsReal => data.anyValue values formula
  -- False or unresolved previews cannot turn malformed frozen evidence into
  -- a goal diagnostic. Successful proposals still undergo kernel replay.
  if preview != some true then
    unless data.checkFinite values formula () extraSignKeys do
      throwError "rcf: fixed-field certificate evidence failed replay"
  match quantifier, preview with
  | .forallReal, some false =>
      throwError "rcf: the universal sentence is false on the prepared cells"
  | .existsReal, some false =>
      throwError "rcf: the existential sentence is false on the prepared cells"
  | _, none => throwError "rcf: finite sign table did not decide the sentence"
  | _, some true => pure ()

/-- Refinement changes producer evidence only after the original finite
certificate passes. Frozen replay never invokes this optimization. -/
private meta def refineCertificate {p : ZPoly} {s : DyadicSquare}
    {hw : atomWitness p s} {hp : (mahlerPrec p : Int) ≤ s.prec}
    [ZPoly.CheckedIrreducible p] {n : Nat}
    (values : Fin n → PolyQuot p (SimpleRoot.ofSquare p s hw hp))
    (formula : RealFormula.QF (n + 1)) (quantifier : RealFormula.Quantifier)
    (extraSignKeys : List (PolyQuot p (SimpleRoot.ofSquare p s hw hp)))
    (validate : FieldBuild.Result p s hw hp Unit (n + 1) → MetaM Unit)
    (data : FieldBuild.Result p s hw hp Unit (n + 1)) :
    MetaM (FieldBuild.Result p s hw hp Unit (n + 1)) := do
  let options ← getOptions
  let steps := rcf.algebraic.signRefinements.get options
  if steps = 0 then return data
  unless rcf.algebraic.intervalSigns.get options do return data
  checkPreview values formula quantifier extraSignKeys validate data
  unless data.checkFinite values formula () extraSignKeys do
    throwError "rcf: original fixed-field certificate evidence failed replay"
  Core.checkInterrupted
  match profileit "rcf generator refinement" options (fun _ =>
      FieldBuild.refineSigns p s hw hp data.signs steps) with
  | .error _ =>
      Core.checkInterrupted
      throwError "rcf: generator sign-window refinement produced invalid replay"
  | .ok signs =>
      Core.checkInterrupted
      let result := {data with signs := signs.val}
      validate result
      return result

/-- Quote and replay one fixed-field certificate. Search is already complete;
all finite sign operands are checked before evaluating the source verdict. -/
private meta def quoteCertificate {p : ZPoly} {s : DyadicSquare}
    {hw : atomWitness p s} {hp : (mahlerPrec p : Int) ≤ s.prec}
    [ZPoly.CheckedIrreducible p] {n : Nat}
    (pExpr rootExpr valuesExpr formulaExpr : Expr)
    (values : Fin n → PolyQuot p (SimpleRoot.ofSquare p s hw hp))
    (formula : RealFormula.QF (n + 1)) (quantifier : RealFormula.Quantifier)
    (extraSignKeys : List (PolyQuot p (SimpleRoot.ofSquare p s hw hp)))
    (validate : FieldBuild.Result p s hw hp Unit (n + 1) → MetaM Unit)
    (data : FieldBuild.Result p s hw hp Unit (n + 1)) :
    MetaM (Expr × Expr × FieldBuild.Result p s hw hp Unit (n + 1) × Expr) := do
  checkPreview values formula quantifier extraSignKeys validate data
  let certificate ← profileitM Exception "rcf literal quotation" (← getOptions) do
    resultExpr pExpr rootExpr formulaExpr formula data
  let indexed := rcf.algebraic.indexSigns.get (← getOptions)
  let index := if indexed then LiteralSign.Index.build data.signs.entries.toArray Field.keyOrder
    else LiteralSign.Index.empty
  let routing ← mkAppOptM ``Field.keyOrder #[some pExpr, some rootExpr]
  let quotedIndex := indexExpr index
  let verdictName := match indexed, quantifier with
    | true, .forallReal => ``FieldBuild.Result.checkForallIndex
    | true, .existsReal => ``FieldBuild.Result.checkExistsIndex
    | false, .forallReal => ``FieldBuild.Result.checkForall
    | false, .existsReal => ``FieldBuild.Result.checkExists
  let soundName := match quantifier with
    | .forallReal => ``FieldBuild.Result.checkForall_sound
    | .existsReal => ``FieldBuild.Result.checkExists_sound
  let arguments := if indexed then
    #[certificate, routing, quotedIndex, valuesExpr, formulaExpr, mkConst ``Unit.unit]
    else #[certificate, valuesExpr, formulaExpr, mkConst ``Unit.unit]
  let verdict ← mkAppM verdictName arguments
  let proofType ← mkAppM ``Eq #[verdict, mkConst ``Bool.true]
  let candidate ← mkFreshExprMVar proofType
  let checker := mkIdent (match indexed, quantifier with
    | true, .forallReal => ``FieldBuild.Result.checkForallIndex
    | true, .existsReal => ``FieldBuild.Result.checkExistsIndex
    | false, .forallReal => ``FieldBuild.Result.checkForall_eq
    | false, .existsReal => ``FieldBuild.Result.checkExists_eq)
  let evidence := mkIdent (if indexed then ``FieldBuild.Result.checkEvidenceIndex
    else ``FieldBuild.Result.checkEvidence)
  let lemmas ← evidenceLemmas
  let script ← if rcf.algebraic.singleReplay.get (← getOptions) then
    `(tactic|
        (simp only [$checker:ident, $evidence:ident,
          $lemmas,*]; try (decide +kernel)))
  else
    `(tactic|
        (simp only [$checker:ident, $evidence:ident,
          $lemmas,*, Bool.and_eq_true];
          repeat' (any_goals (apply And.intro)); all_goals try (decide +kernel)))
  let remaining ← profileitM Exception "rcf literal replay" (← getOptions) do
    Lean.Elab.runTactic' candidate.mvarId! script
  unless remaining.isEmpty do
    throwError "rcf: fixed-field certificate replay did not prove a true verdict"
  let checked ← instantiateMVars candidate
  let checked ← if indexed then do
    let signTableName := match quantifier with
      | .forallReal => ``FieldBuild.Result.checkForallIndex_signTable
      | .existsReal => ``FieldBuild.Result.checkExistsIndex_signTable
    let sameName := match quantifier with
      | .forallReal => ``FieldBuild.Result.checkForallIndex_eq
      | .existsReal => ``FieldBuild.Result.checkExistsIndex_eq
    let signed ← mkAppM signTableName (arguments.push checked)
    let same ← mkAppM sameName (arguments.push signed)
    let reverse ← mkAppM ``Eq.symm #[same]
    mkAppM ``Eq.trans #[reverse, checked]
  else pure checked
  let proof ← mkAppM soundName
    #[certificate, valuesExpr, formulaExpr, mkConst ``Unit.unit, checked]
  check proof
  return (proof, certificate, data, checked)

/-- Replay a supplied frozen result without production. Original extra operands
must already be recorded. Errors restore caller state and remain terminal;
accepted false is diagnostic. The returned fixed-field proof is checked in the
ordinary kernel and rejects every nonstandard axiom dependency. -/
meta def replay {p : ZPoly} {s : DyadicSquare}
    {hw : atomWitness p s} {hp : (mahlerPrec p : Int) ≤ s.prec}
    [ZPoly.CheckedIrreducible p] {n : Nat}
    (pExpr rootExpr valuesExpr formulaExpr : Expr)
    (values : Fin n → PolyQuot p (SimpleRoot.ofSquare p s hw hp))
    (formula : RealFormula.QF (n + 1)) (quantifier : RealFormula.Quantifier)
    (data : FieldBuild.Result p s hw hp Unit (n + 1))
    (extraSignKeys : List (PolyQuot p (SimpleRoot.ofSquare p s hw hp)) := []) : MetaM Expr := do
  let saved ← saveState
  let (proof, _) ← tryFinally' (withOptions (fun options =>
      debug.skipKernelTC.set (Elab.async.set options false) false) do
    let (proof, _, _, _) ← quoteCertificate pExpr rootExpr valuesExpr formulaExpr
      values formula quantifier extraSignKeys (fun _ => pure ()) data
    let proof := ShareCommon.shareCommon' proof
    Hex.RCF.checkAxioms `Hex.RCF.RealCoefficients.FieldLiteral.replay proof
    checkWithKernel proof
    return proof)
    (fun result => unless result.isSome do saved.restore)
  return proof

/-- Construct a checked proof for a fixed-field existential or universal
sentence. Search runs in meta code; the resulting term contains only literal
certificate data, the Boolean replay proof, and its soundness theorem. Return
the producer result and checked verdict as well so another checker can use the
same finite sign table without running search or replay a second time. -/
meta def proveWithCertificate {p : ZPoly} {s : DyadicSquare}
    {hw : atomWitness p s} {hp : (mahlerPrec p : Int) ≤ s.prec}
    [ZPoly.CheckedIrreducible p] {n : Nat}
    (pExpr rootExpr valuesExpr formulaExpr : Expr)
    (values : Fin n → PolyQuot p (SimpleRoot.ofSquare p s hw hp))
    (formula : RealFormula.QF (n + 1))
    (quantifier : RealFormula.Quantifier) (precision : Nat := 8)
    (extraSignKeys : List (PolyQuot p (SimpleRoot.ofSquare p s hw hp)) := [])
    (validate : FieldBuild.Result p s hw hp Unit (n + 1) → MetaM Unit := fun _ => pure ()) :
    MetaM (Expr × Expr × FieldBuild.Result p s hw hp Unit (n + 1) × Expr) := do
  let proposed := profileit "rcf certificate production" (← getOptions) fun _ =>
    FieldBuild.build p s hw hp values formula () precision extraSignKeys
  let some data := proposed |
    throwError "rcf: fixed-field certificate construction failed"
  let data ← refineCertificate values formula quantifier extraSignKeys validate data
  unless rcf.algebraic.intervalSigns.get (← getOptions) do
    checkPreview values formula quantifier extraSignKeys validate data
  let signs ← prepareSigns data.signs
  let data := {data with signs}
  return ← quoteCertificate pExpr rootExpr valuesExpr formulaExpr values formula
    quantifier extraSignKeys validate data

/-- Produce and quote a fixed-field certificate within explicit frontend
search budgets. The complete library producer is separate. Accepted false,
exhaustion and invalid replay remain terminal; search is absent from proofs.
Cancellation is checked before and after native production. Individual native
root computations do not check Lean cancellation or elaboration heartbeats. -/
meta def proveRefiningWithCertificate {p : ZPoly} {s : DyadicSquare}
    {hw : atomWitness p s} {hp : (mahlerPrec p : Int) ≤ s.prec}
    [ZPoly.CheckedIrreducible p] {n : Nat}
    (pExpr rootExpr valuesExpr formulaExpr : Expr)
    (values : Fin n → PolyQuot p (SimpleRoot.ofSquare p s hw hp))
    (formula : RealFormula.QF (n + 1)) (quantifier : RealFormula.Quantifier)
    (extraSignKeys : List (PolyQuot p (SimpleRoot.ofSquare p s hw hp)) := [])
    (validate : FieldBuild.Result p s hw hp Unit (n + 1) → MetaM Unit := fun _ => pure ()) :
    MetaM (Expr × Expr × FieldBuild.Result p s hw hp Unit (n + 1) × Expr) := do
  if real : s.meetsRealAxis = true then
    let options ← getOptions
    Core.checkInterrupted
    let result := profileit "rcf certificate production" options fun _ =>
      FieldBuild.produceWithin p s hw hp real values formula ()
        (rcf.algebraic.directDepth.get options) (rcf.algebraic.maxDoublings.get options) extraSignKeys
        (rcf.algebraic.monicCore.get options)
    match result with
    | .error .exhausted =>
        Core.checkInterrupted
        throwError "rcf: algebraic interval refinement budget exhausted; increase rcf.algebraic.maxDoublings or rcf.algebraic.directDepth"
    | .error .invalidReplay =>
        Core.checkInterrupted
        throwError "rcf: algebraic certificate construction or replay failed"
    | .ok data =>
        Core.checkInterrupted
        let data ← refineCertificate values formula quantifier extraSignKeys validate data
        unless rcf.algebraic.intervalSigns.get (← getOptions) do
          checkPreview values formula quantifier extraSignKeys validate data
        let signs ← prepareSigns data.signs
        let data := {data with signs}
        Core.checkInterrupted
        return ← quoteCertificate pExpr rootExpr valuesExpr formulaExpr values formula
          quantifier extraSignKeys validate data
  else throwError "rcf: selected square does not name a real coefficient field"

/-- Construct the checked fixed-field proof when no additional sign queries
are needed by an enclosing coefficient-presentation checker. -/
meta def prove {p : ZPoly} {s : DyadicSquare}
    {hw : atomWitness p s} {hp : (mahlerPrec p : Int) ≤ s.prec}
    [ZPoly.CheckedIrreducible p] {n : Nat}
    (pExpr rootExpr valuesExpr formulaExpr : Expr)
    (values : Fin n → PolyQuot p (SimpleRoot.ofSquare p s hw hp))
    (formula : RealFormula.QF (n + 1))
    (quantifier : RealFormula.Quantifier) (precision : Nat := 8) : MetaM Expr := do
  return (← proveWithCertificate pExpr rootExpr valuesExpr formulaExpr values formula
    quantifier precision).1

/-- Quote a refining algebraic field search with no extra presentation keys. -/
meta def proveRefining {p : ZPoly} {s : DyadicSquare}
    {hw : atomWitness p s} {hp : (mahlerPrec p : Int) ≤ s.prec}
    [ZPoly.CheckedIrreducible p] {n : Nat}
    (pExpr rootExpr valuesExpr formulaExpr : Expr)
    (values : Fin n → PolyQuot p (SimpleRoot.ofSquare p s hw hp))
    (formula : RealFormula.QF (n + 1)) (quantifier : RealFormula.Quantifier) : MetaM Expr := do
  return (← proveRefiningWithCertificate pExpr rootExpr valuesExpr formulaExpr values formula quantifier).1

end Hex.RCF.RealCoefficients.FieldLiteral
