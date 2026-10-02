/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public meta import HexRealFormulaMathlib.Reify.Parse
public meta import Mathlib.Tactic.FinCases
public meta import Mathlib.Lean.Elab.Tactic.Meta

public meta section

/-! Compose ring-batch certificates, coordinate maps, and logical equivalences. -/

namespace Hex.RealFormula.Reify

open Lean Meta Qq

def quoteCmp : Cmp → Expr
  | .eq => mkConst ``Cmp.eq | .ne => mkConst ``Cmp.ne
  | .lt => mkConst ``Cmp.lt | .le => mkConst ``Cmp.le
  | .gt => mkConst ``Cmp.gt | .ge => mkConst ``Cmp.ge

def quoteQuantifier : Quantifier → Expr
  | .existsReal => mkConst ``Quantifier.existsReal
  | .forallReal => mkConst ``Quantifier.forallReal

def quoteFin (n i : Nat) : MetaM Expr := do
  let nQ : Q(ℕ) := toExpr n
  let iQ : Q(ℕ) := toExpr i
  mkAppM ``Fin.mk #[iQ, ← mkDecideProof q($iQ < $nQ)]

/-- The valuation used while closing binders follows the public append convention. -/
def valuation (scope : Array Expr) : MetaM Expr := do
  let mut ρ : Expr := q((Fin.elim0 : Fin 0 → ℝ))
  for x in scope do ρ ← mkAppM ``append #[ρ, x]
  return ρ

private def projection (atoms scope : Array Expr) : MetaM Expr := do
  let ty := mkApp (mkConst ``Fin) (mkNatLit scope.size)
  let optionTy := mkApp (mkConst ``Option [.zero]) ty
  let entries ← atoms.toList.mapM fun x => do
    match scope.toList.idxOf? x with
    | none => pure (mkApp (mkConst ``Option.none [.zero]) ty)
    | some i => pure (mkApp2 (mkConst ``Option.some [.zero]) ty (← quoteFin scope.size i))
  let arr ← mkArrayLit optionTy entries
  let vector := mkApp4 (mkConst ``Vector.mk [.zero]) optionTy (mkNatLit atoms.size)
    arr (← mkEqRefl (mkNatLit atoms.size))
  mkAppM ``Vector.get #[vector]

def prove (target : Expr) (tacticCode : Syntax) : ReifyM Expr := do
  let goal ← mkFreshExprMVar target
  let goals ← liftM <| Lean.Elab.runTactic' goal.mvarId! tacticCode
  unless goals.isEmpty do abort (.internal "coordinate proof left open goals")
  let proof ← instantiateMVars goal
  accountProof proof
  return proof

structure ScopedResult where
  expr : Expr
  proof : Expr
  qf? : Option Expr

private def atom (batch : Reflect.RingBatch) (source : Expr) (scope : Array Expr)
    (cmp : Cmp) (view : Arithmetic) (id : Nat) : ReifyM ScopedResult := do
  let some entry := batch.entries[id]?
    | abort (.internal "ring batch entry identifier out of range")
  let poly := entry.result.value
  unless ← isDefEq (← inferType poly) (mkApp (mkConst ``Poly) (mkNatLit batch.sealed.n)) do
    abort (.unsupported source "ring provider must return integer coefficients")
  let σ ← projection batch.sealed.atoms scope
  let p ← mkAppM ``Poly.project #[σ, poly]
  let ρ ← valuation scope
  let hp ← mkAppM ``Poly.project_correct #[σ, poly, ρ]
  let zero := realNat 0
  let values := batch.sealed.atoms.map fun x => if scope.contains x then x else zero
  let ringProof := entry.result.proof.replaceFVars batch.sealed.atoms values
  let some (_, _, rhs) := (← inferType hp).eq?
    | abort (.internal "projection proof is not an equality")
  let some (_, lhs, _) := (← inferType ringProof).eq?
    | abort (.internal "ring proof is not an equality")
  let hρ ← prove (← mkEq rhs lhs)
    (← `(tactic| (unfold Poly.eval; congr 1 <;> (first | (funext i; fin_cases i <;> simp only [Nat.cast_zero] <;> rfl) | rfl))))
  let evalProof ← mkEqTrans hp (← mkEqTrans hρ ringProof)
  let clearProof ← mkEqTrans view.proof (← mkEqSymm evalProof)
  let dQ : Q(ℕ) := toExpr view.denominator
  let hd ← mkDecideProof q(0 < $dQ)
  let proof ← mkAppM ``Cmp.clear_correct #[quoteCmp cmp, hd, clearProof]
  let a ← mkAppM ``Atom.mk #[p, quoteCmp cmp]
  let qf ← mkAppM ``QF.atom #[a]
  let expr ← mkAppM ``Scoped.matrix #[qf]
  let target := mkApp2 (mkConst ``Iff) (← mkAppM ``Scoped.toProp #[expr, ρ]) source
  unless ← isDefEq (← inferType proof) target do
    abort (.unsupported source "comparison or arithmetic instances differ from real arithmetic")
  accountProof proof
  return ⟨expr, ← mkExpectedTypeHint proof target, some qf⟩

def assemble (batch : Reflect.RingBatch) : Tree → ReifyM ScopedResult
  | .atom source scope cmp view id => atom batch source scope cmp view id
  | .truth value scope => do
    let qf := mkApp (mkConst (if value then ``QF.tt else ``QF.ff)) (mkNatLit scope.size)
    let expr ← mkAppM ``Scoped.matrix #[qf]
    let proposition := mkConst (if value then ``True else ``False)
    return ⟨expr, mkApp (mkConst ``Iff.rfl) proposition, some qf⟩
  | .not _ p => do
    let p ← assemble batch p
    let qf? ← p.qf?.mapM fun q => mkAppM ``QF.not #[q]
    return ⟨← mkAppM ``Scoped.not #[p.expr], ← mkAppM ``not_congr #[p.proof], qf?⟩
  | .binary _ op p q => do
    let ρ ← valuation p.scope
    let p ← assemble batch p
    let q ← assemble batch q
    let (ctor, qctor, congruence) := match op with
      | .and => (``Scoped.and, ``QF.and, ``and_congr)
      | .or => (``Scoped.or, ``QF.or, ``or_congr)
      | .imp => (``Scoped.imp, ``QF.imp, ``imp_congr)
      | .iff => (``Scoped.iff, ``QF.iff, ``iff_congr)
    let expr ← mkAppM ctor #[p.expr, q.expr]
    let proof ← mkAppM congruence #[p.proof, q.proof]
    let proof ← match op with
      | .imp => mkAppM ``Iff.trans #[← mkAppM ``Scoped.imp_correct #[p.expr, q.expr, ρ], proof]
      | .iff => mkAppM ``Iff.trans #[← mkAppM ``Scoped.iff_correct #[p.expr, q.expr, ρ], proof]
      | _ => pure proof
    let qf? ← match p.qf?, q.qf? with
      | some a, some b => pure (some (← mkAppM qctor #[a, b]))
      | _, _ => pure none
    return ⟨expr, proof, qf?⟩
  | .quant _ kind x _ p => do
    let p ← assemble batch p
    let predicateProof ← mkLambdaFVars #[x] p.proof
    let proof ← mkAppM (if kind == .existsReal then ``exists_congr else ``forall_congr')
      #[predicateProof]
    return ⟨← mkAppM ``Scoped.quant #[quoteQuantifier kind, p.expr], proof, none⟩

end Hex.RealFormula.Reify
