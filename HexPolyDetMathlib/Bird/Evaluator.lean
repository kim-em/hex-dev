/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public meta import HexBareissMathlib.Tactic
public meta import HexPolyDetMathlib.Bird.Relations
public import Mathlib.LinearAlgebra.Matrix.Determinant.Bird.Correctness
public meta import Mathlib.Tactic.ReduceModChar

public meta section

open Lean Meta Qq Mathlib.Tactic.Ring Mathlib.Tactic.Determinant
open HexMatrixMathlib.Literal

namespace HexPolyDetMathlib.Bird

/-- Reduce literal coefficients only when a positive characteristic is known.
This also finds local `CharP` instances whose modulus reduces to a numeral. -/
private def reduceCoefficients (e : Expr) : MetaM Simp.Result := do
  let ⟨_, α, _⟩ ← inferTypeQ' e
  let char ← Tactic.ReduceModChar.typeToCharP (expensive := true) α
  match char with
  | .failure => return {expr := e}
  | .intLike n _ _ =>
    let some p ← (Meta.evalNat n).run | return {expr := e}
    if p == 0 then return {expr := e}
    let first ← Tactic.ReduceModChar.derive (expensive := true) e
    return ← first.mkEqTrans (← Tactic.ReduceModChar.derive (expensive := true) first.expr)

/-- One stronger scalar comparison in a fresh atom context. Only expressions
and equality proofs cross the context boundary. -/
private def strongCompare (left right : Expr) : MetaM (Option Expr) := do
  let ⟨_, α, right⟩ ← inferTypeQ' right
  have left : Q($α) := left
  let rα ← synthInstanceQ q(CommRing $α)
  let cα ← Common.mkCache (commSemiringOfCommRing rα)
  let rc := ringCompute cα
  (do
    let a ← Common.eval rcℕ rc cα left
    let b ← Common.eval rcℕ rc cα right
    if a.val.eq rcℕ rc b.val then
      have x : Q($α) := a.expr
      have y : Q($α) := b.expr
      have : $x =Q $y := ⟨⟩
      have pa : Q($left = $x) := a.proof
      have pb : Q($right = $y) := b.proof
      return some q(Eq.trans $pa (Eq.symm $pb))
    let cleanedA ← Mathlib.Tactic.RingNF.cleanup {}
      {expr := a.expr, proof? := some a.proof}
    let cleanedB ← Mathlib.Tactic.RingNF.cleanup {}
      {expr := b.expr, proof? := some b.proof}
    let reducedA ← reduceCoefficients cleanedA.expr
    let reducedB ← reduceCoefficients cleanedB.expr
    let a' ← Common.eval rcℕ rc cα reducedA.expr
    let b' ← Common.eval rcℕ rc cα reducedB.expr
    unless a'.val.eq rcℕ rc b'.val do return none
    have x : Q($α) := a'.expr
    have y : Q($α) := b'.expr
    have : $x =Q $y := ⟨⟩
    let pa : Q($left = $x) ← mkEqTrans
      (← mkEqTrans (← cleanedA.getProof) (← reducedA.getProof)) a'.proof
    let pb : Q($right = $y) ← mkEqTrans
      (← mkEqTrans (← cleanedB.getProof) (← reducedB.getProof)) b'.proof
    return some q(Eq.trans $pa (Eq.symm $pb))).run .reducible

private def finalCompare {u : Level} {α : Q(Type u)} {rα : Q(CommRing $α)}
    (left : Cert rα) (right : Expr) : MetaM (Option Expr) := do
  let cleaned ← Mathlib.Tactic.RingNF.cleanup {}
    {expr := left.norm, proof? := some left.proof}
  let reducedLeft ← reduceCoefficients cleaned.expr
  let reducedRight ← reduceCoefficients right
  trace[HexMatrix.certificate] "final scalar comparison: {cleaned.expr} → {reducedLeft.expr}; {right} → {reducedRight.expr}"
  let some equality ← strongCompare reducedLeft.expr reducedRight.expr | return none
  let proof ← mkEqTrans (← cleaned.getProof) (← reducedLeft.getProof)
  let proof ← mkEqTrans proof equality
  return some (← mkEqTrans proof (← mkEqSymm (← reducedRight.getProof)))

/-- Compare a computed Bird certificate with a proposed value in its scalar
session. The recurrence never sees the proposed value. -/
private def compare {u : Level} {α : Q(Type u)} {rα : Q(CommRing $α)}
    (limit : Nat) (state : IO.Ref Relations.State)
    (cache : IO.Ref (Std.HashMap Expr (Cert rα)))
    (left : Cert rα) (right : Q($α)) : CertM rα (Option Expr) := do
  if ← withReducible <| isDefEq left.norm right then
    return some (← mkExpectedTypeHint left.proof (← mkEq left.subject right))
  let ctx ← read
  let target ← toCert <$> Scalar.eval rcℕ ctx.rc ctx.cα right
  let (left, target) ← Relations.align limit state cache left target
  unless left.val.eq rcℕ ctx.rc target.val do return none
  have a : Q($α) := left.norm
  have b : Q($α) := target.norm
  have : $a =Q $b := ⟨⟩
  have subject : Q($α) := left.subject
  have pa : Q($subject = $a) := left.proof
  have pb : Q($right = $b) := target.proof
  return some q(Eq.trans $pa (Eq.symm $pb))

/-- Entry proofs identify a simplified row-major list with the original
literal. No decidable equality on the scalar carrier is used. -/
private def listProof (α : Expr) (entries : Array (Expr × Simp.Result)) : MetaM Expr := do
  let mut sourceTail ← mkListLit α []
  let mut normalTail := sourceTail
  let mut proof ← mkEqRefl sourceTail
  for (source, result) in entries.reverse do
    let sourceCons ← mkAppM ``List.cons #[source, sourceTail]
    let normalCons ← mkAppM ``List.cons #[result.expr, normalTail]
    let headFn ← withLocalDeclD `z α fun z => do
      mkLambdaFVars #[z] (← mkAppM ``List.cons #[z, sourceTail])
    let tailFn ← withLocalDeclD `t (← inferType sourceTail) fun t => do
      mkLambdaFVars #[t] (← mkAppM ``List.cons #[result.expr, t])
    let headProof ← mkCongrArg headFn (← result.getProof' source)
    let tailProof ← mkCongrArg tailFn proof
    proof ← mkEqTrans headProof tailProof
    sourceTail := sourceCons
    normalTail := normalCons
  return proof

/-- Recognized source matrix, flattened in the row order used by Bird's array. -/
private def entries? (A : Expr) : MetaM (HexMatrixMathlib.Det.Outcome (Array (Expr × Simp.Result))) := do
  if A.hasMVar then
    return .notApplicable m!"unresolved matrix metavariables"
  let some lit ← literal? A (allowOpen := true) |
    return .notApplicable m!"expected a square matrix literal"
  unless lit.n == lit.m do
    return .notApplicable m!"expected a square matrix literal"
  let ctx ← Simp.mkContext (config := { decide := true })
    (simpTheorems := #[← getSimpTheorems])
  let entries ← lit.entries.flatten.mapM fun entry => do
    let result ← if entry.getAppFn.isConstOf ``ite then do
      let args := entry.getAppArgs
      if args.size < 4 then pure (← Simp.main entry ctx).1 else
        let condition := args[args.size - 4]!
        let conditionInstance := args[args.size - 3]!
        let yes := args[args.size - 2]!
        let no := args[args.size - 1]!
        -- Only the closed Fin-index condition is reduced with full transparency;
        -- neither branch nor the scalar carrier is unfolded for this decision.
        let decided ← withTransparency .all <| whnf (← mkDecide condition)
        if decided.isConstOf ``Bool.true then
          let proof ← mkAppOptM ``if_pos #[some condition, some conditionInstance,
            some (← decideProof condition), some (← inferType yes), some yes, some no]
          pure ({expr := yes, proof? := some proof} : Simp.Result)
        else if decided.isConstOf ``Bool.false then
          let proof ← mkAppOptM ``if_neg #[some condition, some conditionInstance,
            some (← decideProof (mkNot condition)), some (← inferType yes), some yes, some no]
          pure ({expr := no, proof? := some proof} : Simp.Result)
        else pure (← Simp.main entry ctx).1
    else pure (← Simp.main entry ctx).1
    return (entry, result)
  trace[HexMatrix.certificate] "symbolic entries: {entries.map (·.2.expr)}"
  return .success entries

/-- Add a local symbolic ceiling without increasing an outer remaining allowance. -/
def withBudget {β : Type} (limit : Nat) (action : MetaM β) : MetaM β := do
  let requested := limit * 1000
  let ctx ← readThe Core.Context
  checkSystem "det"
  let now ← IO.getNumHeartbeats
  let remaining := ctx.maxHeartbeats - (now - ctx.initHeartbeats)
  if ctx.maxHeartbeats != 0 && remaining == 0 then
    Core.throwMaxHeartbeat `det `maxHeartbeats ctx.maxHeartbeats
  let effective := if ctx.maxHeartbeats == 0 then requested else min remaining requested
  trace[HexMatrix.certificate] "symbolic heartbeat ceiling: {effective / 1000} public units"
  withTheReader Core.Context (fun ctx => {ctx with initHeartbeats := now, maxHeartbeats := effective}) do
    let result ← action
    checkSystem "det"
    return result

/-- Build one Bird certificate, then produce a public value or compare a target
in the same scalar session. -/
def evaluate (cfg : HexMatrixMathlib.Det.Config) (A : Expr) (rhs? : Option Expr := none) :
    MetaM (HexMatrixMathlib.Det.Outcome HexMatrixMathlib.Det.Result) := do
  if cfg.maxHeartbeats == 0 then
    return .declined m!"symbolic heartbeat budget exhausted (0/0) before evaluation"
  if cfg.maxRelationWork == 0 then
    return .declined m!"relation work budget exhausted (0/0) before evaluation"
  withBudget cfg.maxHeartbeats do
    let some (_, _, carrier) ← shape? (← inferType A) |
      return .notApplicable m!"expected a matrix over Fin indices"
    try
      let _ ← synthInstance (← mkAppM ``CommRing #[carrier])
    catch ex =>
      if ex.isInterrupt || ex.isMaxHeartbeat || ex.isMaxRecDepth then throw ex
      if let .internal _ _ := ex then throw ex
      return .notApplicable m!"expected a commutative ring"
    let entries ← match ← entries? A with
      | .success entries => pure entries
      | .notApplicable msg => return .notApplicable msg
      | .declined msg => return .declined msg
    let e ← mkAppM ``Matrix.det #[A]
    let ⟨_, α, e⟩ ← inferTypeQ' e
    let args := e.getAppArgs
    unless e.getAppFn.isConstOf ``Matrix.det && args.size == 6 do
      return .notApplicable m!"expected a determinant over Fin indices"
    let_expr Fin dim := args[0]! |
      return .notApplicable m!"expected Fin indices"
    let some n ← checkTypeQ dim q(ℕ) |
      return .notApplicable m!"expected a known dimension"
    let some _rα ← checkTypeQ args[4]! q(CommRing $α) |
      return .notApplicable m!"expected a commutative ring"
    have matrix : Q(Matrix (Fin $n) (Fin $n) $α) := args[5]!
    let sources := entries.map (·.1)
    let values := entries.map (·.2.expr)
    let originals : Q(List $α) ← mkListLit α sources.toList
    let xs : Q(List $α) ← mkListLit α values.toList
    let arrayExpr := q(List.toArray $xs)
    have : (List.ofFn fun k : Fin ($n * $n) ↦ $matrix k.divNat k.modNat) =Q $originals := ⟨⟩
    let originalProof : Q(List.ofFn (fun k : Fin ($n * $n) ↦ $matrix k.divNat k.modNat) = $originals) := q(rfl)
    let hlist : Q(List.ofFn (fun k : Fin ($n * $n) ↦ $matrix k.divNat k.modNat) = $xs) :=
      ← mkEqTrans originalProof (← listProof α entries)
    let hArray := q($hlist ▸ List.toArray_ofFn)
    let transport := q($hArray ▸ Matrix.ofArray_ofFn $matrix ▸ BirdDet.det_eq_birdDet
      (Array.ofFn fun k : Fin ($n * $n) ↦ $matrix k.divNat k.modNat) Array.size_ofFn)
    let reified ← reifyBirdDet q(BirdDet.birdDet $n $arrayExpr)
    let cα ← Common.mkCache (commSemiringOfCommRing reified.rα)
    let ctx := { reified.ctx with cα, rc := ringCompute cα }
    let relationState ← IO.mkRef ({} : Relations.State)
    let relationCache ← IO.mkRef ({} : Std.HashMap Expr (Cert reified.rα))
    let action : CertM reified.rα (Cert reified.rα × Option Expr) := do
      let cert ← Recurrence.certBirdDet
        (Relations.normalize cfg.maxRelationWork relationState relationCache)
      let proof? ← match rhs? with
        | none => pure none
        | some rhs => compare cfg.maxRelationWork relationState relationCache cert rhs
      return (cert, proof?)
    let (cert, comparison?) ← try
      action.run' {} |>.run ctx |>.run .reducible
    catch ex =>
      if let .internal id _ := ex then
        if id == Relations.budgetException then
          let count := (← relationState.get).work
          return .declined m!"relation work budget exhausted during Bird evaluation/comparison ({count}/{cfg.maxRelationWork})"
      throw ex
    let stats ← relationState.get
    trace[HexMatrix.certificate]
      "route: symbolic-Bird; relation work: {stats.work}/{cfg.maxRelationWork}; rewrites: {stats.rewrites}"
    if let some rhs := rhs? then
      let comparison? ← match comparison? with
        | some proof => pure (some proof)
        | none => finalCompare cert rhs
      let some comparison := comparison? |
        return .declined m!"symbolic scalar comparison did not establish equality"
      return .success ⟨rhs, ← mkEqTrans transport comparison⟩
    let cleaned ← Mathlib.Tactic.RingNF.cleanup {}
      {expr := cert.norm, proof? := some cert.proof}
    let reduced ← reduceCoefficients cleaned.expr
    let proof ← mkEqTrans (← cleaned.getProof) (← reduced.getProof)
    return .success ⟨reduced.expr, ← mkEqTrans transport proof⟩

/-- Compute and certify a determinant without receiving an answer. -/
def compute (cfg : HexMatrixMathlib.Det.Config) (A : Expr) :
    MetaM (HexMatrixMathlib.Det.Outcome HexMatrixMathlib.Det.Result) :=
  evaluate cfg A

/-- Compare a numeric certificate with a symbolic target through scalar ring
normalization. The numeric determinant is already computed at this point. -/
private def compareNumeric (value right : Expr) : MetaM (Option Expr) := do
  let ⟨_, α, right⟩ ← inferTypeQ' right
  have value : Q($α) := value
  let rα ← synthInstanceQ q(CommRing $α)
  let cα ← Common.mkCache (commSemiringOfCommRing rα)
  let rc := ringCompute cα
  let compact ← (do
    let left ← Scalar.eval rcℕ rc cα value
    let target ← Scalar.eval rcℕ rc cα right
    unless left.val.eq rcℕ rc target.val do return none
    have a : Q($α) := left.expr
    have b : Q($α) := target.expr
    have : $a =Q $b := ⟨⟩
    have pa : Q($value = $a) := left.proof
    have pb : Q($right = $b) := target.proof
    return some q(Eq.trans $pa (Eq.symm $pb))).run .reducible
  if compact.isSome then return compact
  strongCompare value right

/-- Close a supplied determinant equality using exactly one determinant
computation. Numeric targets use the certificate closing handler when it accepts
the entire equation; otherwise scalar comparison follows numeric computation. -/
def prove (cfg : HexMatrixMathlib.Det.Config) (target : Expr) :
    MetaM (HexMatrixMathlib.Det.Outcome Expr) := do
  let target ← instantiateMVars target
  let some (A, rhs, reverse) := HexMatrixMathlib.Det.detTarget? target |
    return .notApplicable m!"expected a determinant equality"
  if A.hasMVar || rhs.hasMVar then
    return .notApplicable m!"unresolved input metavariables"
  let saved ← saveState
  if let .success _ ← HexMatrixMathlib.Det.recognize A then
    let closesNumerically ← if rhs.hasFVar then pure false else do
      try
        let _ ← HexMatrixMathlib.Literal.evalEntry rhs
        pure true
      catch ex =>
        if ex.isInterrupt || ex.isMaxHeartbeat || ex.isMaxRecDepth then throw ex
        pure false
    if closesNumerically then
      trace[HexMatrix.certificate] "route: numeric-certificate"
      match ← HexMatrixMathlib.Det.proveGoal cfg.toKernelConfig target with
      | .success proof => return .success proof
      | .declined msg =>
        saved.restore
        return .declined msg
      | .notApplicable msg =>
        saved.restore
        return .notApplicable msg
    let p ← match ← HexMatrixMathlib.Det.compute cfg A with
      | .success p => pure p
      | .declined msg =>
        saved.restore
        return .declined msg
      | .notApplicable msg =>
        saved.restore
        return .notApplicable msg
    let some equality ← compareNumeric p.value rhs |
      saved.restore
      return .declined m!"numeric scalar comparison did not establish equality"
    let proof ← mkEqTrans p.proof equality
    return .success (← if reverse then mkEqSymm proof else pure proof)
  match ← evaluate cfg A (some rhs) with
  | .success result =>
    return .success (← if reverse then mkEqSymm result.proof else pure result.proof)
  | .declined msg =>
    saved.restore
    return .declined msg
  | .notApplicable msg =>
    saved.restore
    return .notApplicable msg

end HexPolyDetMathlib.Bird
