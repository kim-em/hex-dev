/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module
public import HexRCF.RealCoefficients.IsolationTransport
public import HexRCF.RealCoefficients.PolynomialBoundsSoundness
public import HexRCF.RealCoefficients.Registration
public import Mathlib.Analysis.Real.Pi.Bounds
public meta import HexRCF.RealCoefficients.PolynomialBounds
public meta import HexRCF.RealCoefficients.FieldIsolate
public meta import HexRCF.RealCoefficients.IsolationTransport
public meta import HexRCF.RealCoefficients.FieldLiteral
public meta import HexMvPolyTheory.Equiv
public meta import Lean.Elab.Command
public section

set_option debug.skipKernelTC false
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 8000000

namespace Hex.RCF.PolynomialIsolation
open RealCoefficients Hex.OrderedFn.Oracle Lean Meta

abbrev E := PolynomialBounds.Poly 1

/-- Caller data for this test, with no convergence or requested-width claim. -/
@[expose] def bounds : Bounds := ⟨mkRat 31415 10000, mkRat 31416 10000, by decide⟩

@[expose] def registration : Registration Real.pi where
  version := 1
  approximation _ := bounds
  containment _ _ := by
    have lower := Real.pi_gt_d4.le
    have upper := Real.pi_lt_d4.le
    norm_num at lower upper
    norm_num [Contains, bounds, mkRat]
    exact ⟨lower, upper⟩

@[expose] def parameter : E := MvPoly.X (0 : Fin 1)

/-- The complete carrier for the three atoms x²=π, 1<x, x<2. -/
@[expose] def head : DensePoly E :=
  DensePoly.ofList [-2 * parameter, 3 * parameter, 2 - parameter, -3, 1]

@[expose] def point (d : Dyadic) : E := MvPoly.C d.toRat

@[expose] def lookup (q : E) : Option Int :=
  PolynomialBounds.sign? (fun _ => bounds) q

noncomputable def read (q : E) : ℝ := PolynomialBounds.value (fun _ => Real.pi) q

theorem read_closed : Hex.RealClosure.Transport.Closed read (fun _ => True) :=
  PolynomialBounds.closed (fun _ => Real.pi)

theorem lookup_spec (q : E) (value : Int) (found : lookup q = some value) :
    value = (SignType.sign (read q) : Int) :=
  PolynomialBounds.sign_spec (fun _ => bounds) (fun _ => Real.pi)
    (fun _ => registration.containment 1 (by norm_num)) q value found

/-- Literal constructor for the univariate coefficient data in this test. -/
@[expose] def fromTerms (terms : List (Nat × Rat)) : E :=
  MvPoly.ofTerms (terms.map fun term => (Vector.replicate 1 term.1, term.2))

private meta def coordinateExpr (q : E) : MetaM Expr := do
  let terms ← q.termsList.mapM fun (m, c) => do
    let coefficient ← mkAppM ``mkRat #[mkIntLit c.num, mkNatLit c.den]
    mkAppM ``Prod.mk #[mkNatLit m[0], coefficient]
  let pairType ← mkAppM ``Prod #[mkConst ``Nat, mkConst ``Rat]
  mkAppM ``fromTerms #[← mkListLit pairType terms]

private meta def runStrict (goal : MVarId) (code : Syntax) : MetaM (List MVarId) := do
  instantiateMVarDeclMVars goal
  let action : Elab.TermElabM (List MVarId) :=
    Elab.Term.withSynthesize do
      Elab.Tactic.run goal <| Elab.Tactic.withoutRecover
        (Elab.Tactic.evalTactic code *> Elab.Tactic.pruneSolvedGoals)
  action.run' {} {}

run_meta withoutExporting do
  let sign := fun q : E => (lookup q).getD 0
  let some total := TarskiCertificate.certify sign (EndpointSigns.ofSign sign)
      SignedRemainderChain.normalizeId () head 1 .negInf .posInf |
    throwError "polynomial-ring pi carrier production failed"
  let some intervals := FieldIsolate.proposeWith? sign point
      SignedRemainderChain.normalizeId head 64 |
    throwError "polynomial-ring pi carrier isolation failed"
  let certificate : IsolationReplay E Unit := {
    isolations := intervals
    total := total
    counts := Vector.ofFn fun i =>
      let interval := intervals.intervals[i]
      TarskiCertificate.fromChains sign (EndpointSigns.ofSign sign) () head 1
        (.finite (point interval.lower)) (.finite (point interval.upper))
        total.squarefree total.remainders }
  unless intervals.intervals.size == 4 && IsolationTransport.check lookup point () head certificate do
    let missing := (IsolationTransport.keys point head certificate).filter fun q => (lookup q).isNone
    throwError "polynomial-ring pi carrier replay failed; missing signs={missing.length}"
  unless !(IsolationTransport.check lookup point () head
      {certificate with total := {total with value := total.value + 1}}) do
    throwError "polynomial-ring pi carrier accepted a changed root count"
  unless !(IsolationTransport.check lookup point () (head + 1) certificate) do
    throwError "polynomial-ring pi carrier accepted a changed subject"
  let wrongCounts := {certificate with counts := certificate.counts.map fun query =>
    {query with value := query.value + 1}}
  unless !(IsolationTransport.check lookup point () head wrongCounts) do
    throwError "polynomial-ring pi carrier accepted wrong interval counts"
  let incomplete := {intervals with intervals := intervals.intervals.pop}
  let missingRoot : IsolationReplay E Unit := {
    isolations := incomplete
    total := total
    counts := Vector.ofFn fun i =>
      let interval := incomplete.intervals[i]
      TarskiCertificate.fromChains sign (EndpointSigns.ofSign sign) () head 1
        (.finite (point interval.lower)) (.finite (point interval.upper))
        total.squarefree total.remainders }
  unless !(IsolationTransport.check lookup point () head missingRoot) do
    throwError "polynomial-ring pi carrier accepted incomplete root coverage"
  let broad := fun _ : Fin 1 => (⟨0, 4, by decide⟩ : Bounds)
  unless (PolynomialBounds.sign? broad parameter).isNone &&
      PolynomialBounds.sign? broad (parameter - parameter) == some 0 do
    throwError "polynomial bounds confused cancellation and unresolved signs"
  unless !(IsolationTransport.check (PolynomialBounds.sign? broad) point () head certificate) do
    throwError "polynomial-ring pi carrier accepted unresolved coefficient signs"
  let literal ← instantiateMVars (← FieldLiteral.isolationExpr coordinateExpr certificate)
  let frozenName := `Hex.RCF.PolynomialIsolation.frozen
  withExporting (isExporting := true) do addDecl (.defnDecl {
    name := frozenName
    levelParams := []
    type := ← inferType literal
    value := literal
    hints := .abbrev
    safety := .safe })
  enableRealizationsForConst frozenName
  setReducibilityStatus frozenName .reducible
  let checked ← mkAppM ``IsolationTransport.check #[mkConst ``lookup, mkConst ``point,
    mkConst ``Unit.unit, mkConst ``head, mkConst frozenName]
  let target ← instantiateMVars (← mkEq checked (mkConst ``Bool.true))
  let candidate ← mkFreshExprMVar target
  let frozenId := mkIdent frozenName
  let remaining ← runStrict candidate.mvarId!
    (← `(tactic| simp only [$frozenId:ident, IsolationTransport.check,
      QueryReplay.check, QueryReplay.covered, QueryReplay.leading, QueryReplay.cached,
      Sturm.check, TarskiCertificate.check_eq, SignedRemainderChain.check,
      SignInputs.certificate, lookup, PolynomialBounds.sign?, head, point, parameter,
      Bool.and_eq_true, ← Array.all_toList, Array.toList_range,
      List.all_toArray', List.size_toArray, List.length_cons, List.length_nil,
      List.finRange_succ, List.finRange_zero, List.map_cons, List.map_nil,
      List.all_cons, List.all_nil]))
  let rec prove (goal : MVarId) : MetaM Unit := do
    let type ← whnf (← goal.getType)
    if type.isConstOf ``True then
      goal.assign (mkConst ``True.intro)
    else if type.isAppOfArity ``And 2 then
      for child in ← goal.apply (mkConst ``And.intro) do prove child
    else
      let some (_, expression, _) := type.eq? |
        throwError "unexpected frozen pi check shape: {type}"
      if expression.isAppOf ``Array.all then
        let arguments := expression.getAppArgs
        unless ← isDefEq arguments[3]! (mkNatLit 0) do
          throwError "unexpected sliced array in frozen pi replay"
        let elements ← mkAppM ``Array.toList #[arguments[1]!]
        let same ← mkAppOptM ``List.all_toArray'
          #[some arguments[0]!, some arguments[2]!, some elements,
            some arguments[4]!, some (← mkEqRefl arguments[4]!)]
        let rewritten ← goal.rewrite (← goal.getType) same
        let candidate ← mkFreshExprMVar rewritten.eNew
        goal.assign (← mkEqMP (← mkEqSymm rewritten.eqProof) candidate)
        let children ← runStrict candidate.mvarId! (← `(tactic|
          simp only [List.all_cons, List.all_nil, Bool.and_eq_true]))
        for child in children do
          let children ← runStrict child (← `(tactic| simp only [Bool.and_eq_true]))
          for child in children do prove child
      else if expression.isAppOf ``List.all &&
          (← whnf expression.getAppArgs[0]!).isAppOfArity ``Fin 1 then
        let children ← runStrict goal (← `(tactic|
          (apply List.all_eq_true.mpr
           intro i _
           fin_cases i)))
        for child in children do
          let children ← runStrict child (← `(tactic| simp only [Bool.and_eq_true]))
          for child in children do prove child
      else
        let unresolved ← runStrict goal (← `(tactic| decide +kernel))
        unless unresolved.isEmpty do throwError "frozen pi isolation has an unproved check"
  for goal in remaining do prove goal
  let proof ← Hex.RCF.checkProof `Hex.RCF.PolynomialIsolation.accepted target
    (← instantiateMVars candidate)
  withExporting (isExporting := true) do addDecl (.thmDecl {
    name := `Hex.RCF.PolynomialIsolation.accepted
    levelParams := []
    type := target
    value := proof })
  Lean.logInfo m!"POLYNOMIAL_ISOLATION: pi carrier roots={intervals.intervals.size}; intervals={intervals.intervals.map fun i => (i.lower.toRat, i.upper.toRat)}; complete finite replay and changed-count refusal checked"

end Hex.RCF.PolynomialIsolation
