/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public meta import HexMatrixTactic.Model
public import HexMatrixTactic.Model
public meta import HexMatrixTactic.Syntax
public import HexMatrixTactic.Syntax

public section

/-!
The rank frontend on `Hex.Matrix` inputs.

Domain rank names `Hex.Matrix.rankWith quot` or its integer specialization
`Hex.Matrix.rank`, from `HexRank`; field rank names
`Hex.Matrix.rowReduce_rank`, from `HexRowReduce`.  Both producers are
structural, so the kernel replays the producer on the matrix expression for
the equality; an inequality is the replayed equality followed by a checked
natural-number comparison.  Rectangular and empty matrices are accepted.
-/

namespace Hex.MatrixTactic

open Lean Meta Elab

/-- The rank operations the Hex frontend recognizes. -/
public meta inductive RankOp where
  /-- `Hex.Matrix.rankWith quot A`, or its integer specialization
  `Hex.Matrix.rank A`. -/
  | domain (quot : Expr)
  /-- `Hex.Matrix.rowReduce_rank A`, field row reduction. -/
  | field

/-- The comparison a rank target states between `rank A` and the other side. -/
public meta inductive RankRel where
  /-- `rank A = r` (or `r = rank A`). -/
  | eq
  /-- `rank A ≤ r` (or `r ≥ rank A`). -/
  | le
  /-- `r ≤ rank A` (or `rank A ≥ r`). -/
  | ge

/-- Recognize a rank application, returning the operation and its matrix
argument. -/
public meta def rankOp? (e : Expr) : Option (RankOp × Expr) :=
  match e.getAppFnArgs with
  | (``Hex.Matrix.rank, #[_, _, A]) =>
      some (.domain (mkConst ``HexArith.Int.exactDiv), A)
  | (``Hex.Matrix.rankWith, args) =>
      if h : 2 ≤ args.size then some (.domain args[args.size - 2], args[args.size - 1])
      else none
  | (``Hex.Matrix.rowReduce_rank, args) =>
      if h : 1 ≤ args.size then some (.field, args[args.size - 1]) else none
  | _ => none

/-- Recognize a rank target: the rank application, the other side, the
relation from the rank's point of view, and whether an equality was stated
with the rank on the right. -/
public meta def rankTarget? (target : Expr) : Option (RankOp × Expr × Expr × RankRel × Bool) := do
  let isRank (e : Expr) := (rankOp? e).isSome
  if let some (opE, other, reverse) := eqSides? target isRank then
    let some (op, A) := rankOp? opE | none
    return (op, A, other, .eq, reverse)
  match target.getAppFnArgs with
  | (``LE.le, #[_, _, a, b]) =>
      if isRank a then
        let some (op, A) := rankOp? a | none
        some (op, A, b, .le, false)
      else if isRank b then
        let some (op, A) := rankOp? b | none
        some (op, A, a, .ge, false)
      else none
  | (``GE.ge, #[_, _, a, b]) =>
      if isRank a then
        let some (op, A) := rankOp? a | none
        some (op, A, b, .ge, false)
      else if isRank b then
        let some (op, A) := rankOp? b | none
        some (op, A, a, .le, false)
      else none
  | _ => none

/-- The rank producer selected for a model and operation: the function
expression (of the matrix) and the compiled computation on an input. -/
private meta structure Producer (n m : Nat) where
  fn : Expr
  compute : Input n m → MetaM Nat

/-- Select the producer for an operation, or decline. -/
private meta def producer? (model : Model) (n m : Nat) (op : RankOp) :
    MetaM (Outcome (Producer n m)) := do
  match op with
  | .domain quot =>
      let some quotExpr := model.quot? |
        return .declined m!"the {model.name} model has no kernel-checkable exact quotient, so the domain rank is unavailable; over a field state the goal with `Hex.Matrix.rowReduce_rank`"
      unless ← isDefEq quot quotExpr do
        return .declined m!"the quotient{indentExpr quot}\nis not the certified exact quotient of the {model.name} model"
      let fn ←
        if model.carrier.isConstOf ``Int then
          pure (mkApp2 (mkConst ``Hex.Matrix.rank) (mkNatLit n) (mkNatLit m))
        else
          withLocalDeclD `M (matrixType model.carrier n m) fun M => do
            mkLambdaFVars #[M] (← mkAppM ``Hex.Matrix.rankWith #[quotExpr, M])
      return .success ⟨fn, fun input => do
        let some compute := input.domainRank? |
          throwError "rank: the {model.name} model offered no domain rank"
        compute⟩
  | .field =>
      unless model.isField do
        return .declined m!"the {model.name} model is not a field with kernel-evaluable arithmetic, so row-reduction rank is unavailable"
      let fn ← withLocalDeclD `M (matrixType model.carrier n m) fun M => do
        mkLambdaFVars #[M] (← mkAppM ``Hex.Matrix.rowReduce_rank #[M])
      return .success ⟨fn, fun input => do
        let some compute := input.fieldRank? |
          throwError "rank: the {model.name} model offered no field rank"
        compute⟩

/-- The default producer for the `rank%` record: domain rank when the model
has an exact quotient, field rank otherwise. -/
private meta def defaultOp (model : Model) : RankOp :=
  match model.quot? with
  | some quotExpr => .domain quotExpr
  | none => .field

/-- Classify a candidate input: a Hex matrix under a numeric model, a non-Hex
type, or a decline. -/
private meta def rankModel? (e : Expr) : MetaM (Outcome (Model × Nat × Nat)) := do
  let some shape ← shape? "rank" (← inferType e) | return .notApplicable
  let some model ← modelFor? shape.carrier |
    return .declined m!"no numeric entry model for the carrier{indentExpr shape.carrier}"
  return .success (model, shape.rows, shape.cols)

/-- Prove `fn A = r` by kernel replay of the producer on the original
expression. -/
private meta def proveRankEq {n m : Nat} (input : Input n m) (fn r : Expr) : MetaM Expr := do
  kernelDecideProof "rank" (← mkEq (.headBeta (mkApp fn input.expr)) r)

/-- The `rank% A` record for a Hex input. -/
public meta def rankCertified (e : Expr) : MetaM (Outcome Expr) := do
  let e ← instantiateMVars e
  let (model, n, m) ← match ← rankModel? e with
    | .success r => pure r
    | .notApplicable => return .notApplicable
    | .declined msg => return .declined msg
    | .failure msg => return .failure msg
  let producer ← match ← producer? model n m (defaultOp model) with
    | .success p => pure p
    | .notApplicable => return .notApplicable
    | .declined msg => return .declined msg
    | .failure msg => return .failure msg
  let input ← model.evalInput "rank" n m e
  let value := mkNatLit (← producer.compute input)
  let proof ← proveRankEq input producer.fn value
  return .success (← mkAppOptM ``Hex.MatrixTactic.Certified.mk
    #[none, none, some producer.fn, some e, some value, some proof])

/-- Prove a rank equality or inequality target on a Hex input. -/
public meta def proveRankGoal (target : Expr) : MetaM (Outcome Expr) := do
  let target ← instantiateMVars target
  let some (op, A, other, rel, reverse) := rankTarget? target | return .notApplicable
  let (model, n, m) ← match ← rankModel? A with
    | .success r => pure r
    | .notApplicable => return .notApplicable
    | .declined msg => return .declined msg
    | .failure msg => return .failure msg
  let producer ← match ← producer? model n m op with
    | .success p => pure p
    | .notApplicable => return .notApplicable
    | .declined msg => return .declined msg
    | .failure msg => return .failure msg
  checkClosed "rank" "bound" other
  let input ← model.evalInput "rank" n m A
  let r ← producer.compute input
  let rExpr := mkNatLit r
  let proof ← match rel with
    | .eq =>
        let proof ← proveRankEq input producer.fn other
        if reverse then mkEqSymm proof else pure proof
    | .le =>
        -- `rank A = r`, then `r ≤ other` checked in the kernel.
        let eq ← proveRankEq input producer.fn rExpr
        let le ← kernelDecideProof "rank" (← mkAppM ``LE.le #[rExpr, other])
        mkAppM ``Nat.le_trans #[← mkAppM ``Nat.le_of_eq #[eq], le]
    | .ge =>
        let eq ← proveRankEq input producer.fn rExpr
        let le ← kernelDecideProof "rank" (← mkAppM ``LE.le #[other, rExpr])
        mkAppM ``Nat.le_trans #[le, ← mkAppM ``Nat.le_of_eq #[← mkEqSymm eq]]
  return .success proof

@[term_elab rankTerm]
public meta def elabRankTerm : Term.TermElab := fun stx expectedType? => do
  match stx with
  | `(rank% $t) =>
      let e ← elabMatrixArgument t
      let result ← (← rankCertified e).get "rank"
      Term.ensureHasType expectedType? result
  | _ => throwUnsupportedSyntax

@[tactic rankTac]
public meta def evalRankTac : Tactic.Tactic := fun _ => Tactic.withMainContext do
  let proof ← (← proveRankGoal (← Tactic.getMainTarget)).get "rank"
  Tactic.closeMainGoal `rank proof

end Hex.MatrixTactic
