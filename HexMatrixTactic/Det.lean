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
The determinant frontend on `Hex.Matrix` inputs.

The producer is the row-pivoted fraction-free Bareiss elimination.  Compiled
code discovers the value; the kernel replays the `ofFn` form of the pivot loop
on the matrix literal (`bareissReplay`), so a `bareiss`/`bareissWith` goal is
closed without evaluating the Leibniz specification.  A goal stated with
`Hex.Matrix.det` itself is replayed directly up to `leibnizDimension`, since
no Mathlib-free theorem identifies the two; the Mathlib companion transports
through `bareissWith_eq_mathlib_det` instead.
-/

namespace Hex.MatrixTactic

open Lean Meta Elab

/-- The determinant operations the Hex frontend recognizes in goals. -/
public meta inductive DetOp where
  /-- `Hex.Matrix.bareissWith quot A`, or its integer specialization
  `Hex.Matrix.bareiss A`. -/
  | bareiss (quot : Expr)
  /-- `Hex.Matrix.det A`, the Leibniz specification. -/
  | leibniz

/-- The largest dimension at which a `Hex.Matrix.det` goal is proved by
replaying the Leibniz expansion in the kernel.  The expansion has `n!` terms;
this provisional cutoff is fixed until Phase-4 measurement. -/
public meta def leibnizDimension : Nat := 5

/-- Recognize a determinant application, returning the operation and its
matrix argument. -/
public meta def detOp? (e : Expr) : Option (DetOp × Expr) :=
  match e.getAppFnArgs with
  | (``Hex.Matrix.bareiss, #[_, A]) =>
      some (.bareiss (mkConst ``HexArith.Int.exactDiv), A)
  | (``Hex.Matrix.bareissWith, args) =>
      if h : 2 ≤ args.size then some (.bareiss args[args.size - 2], args[args.size - 1])
      else none
  | (``Hex.Matrix.det, args) =>
      if h : 1 ≤ args.size then some (.leibniz, args[args.size - 1]) else none
  | _ => none

/-- Classify the type of a candidate input: a square Hex matrix under a
numeric model, a non-Hex type (left to another frontend), or an error. -/
private meta def squareModel? (op : String) (e : Expr) :
    MetaM (Outcome (Model × Nat)) := do
  let some shape ← shape? op (← inferType e) | return .notApplicable
  unless shape.rows = shape.cols do
    throwError "{op}: expected a square matrix, but got dimensions {shape.rows} × {shape.cols}"
  let some model ← modelFor? shape.carrier |
    return .declined m!"no numeric entry model for the carrier{indentExpr shape.carrier}"
  return .success (model, shape.rows)

/-- Prove `bareissWith quot A = rhs` by a kernel `decide` on `bareissReplay`
over the literal of `A`. -/
private meta def proveBareiss {n : Nat} (input : Input n n) (quot rhs : Expr) :
    MetaM Expr := do
  let replay ← mkAppM ``Hex.Matrix.bareissReplay #[quot, input.literal]
  let check ← kernelDecideProof "det" (← mkEq replay rhs)
  withTransparency .all <|
    mkAppM ``Hex.Matrix.bareissWith_eq_of_replay #[quot, input.expr, rhs, check]

/-- The Bareiss determinant as a function expression, for the `det%` record. -/
private meta def bareissFn (model : Model) (n : Nat) (quot : Expr) : MetaM Expr := do
  if model.carrier.isConstOf ``Int then
    return mkApp (mkConst ``Hex.Matrix.bareiss) (mkNatLit n)
  withLocalDeclD `M (matrixType model.carrier n n) fun M => do
    mkLambdaFVars #[M] (← mkAppM ``Hex.Matrix.bareissWith #[quot, M])

/-- The `det% A` record for a Hex input: the Bareiss determinant with its
kernel-replayed proof. -/
public meta def detCertified (e : Expr) : MetaM (Outcome Expr) := do
  let e ← instantiateMVars e
  let (model, n) ← match ← squareModel? "det" e with
    | .success r => pure r
    | .notApplicable => return .notApplicable
    | .declined msg => return .declined msg
    | .failure msg => return .failure msg
  let some quotExpr := model.quot? |
    return .declined m!"the {model.name} model has no kernel-checkable exact quotient, so the Bareiss determinant is unavailable"
  let input ← model.evalInput "det" n n e
  let some bareiss := input.bareiss? | return .failure m!"the {model.name} model offered no determinant"
  let value ← bareiss rfl
  let proof ← proveBareiss input quotExpr value
  let fn ← bareissFn model n quotExpr
  return .success (← mkAppOptM ``Hex.MatrixTactic.Certified.mk
    #[none, none, some fn, some e, some value, some proof])

/-- Prove a determinant equality target on a Hex input, in either
orientation. -/
public meta def proveDetGoal (target : Expr) : MetaM (Outcome Expr) := do
  let target ← instantiateMVars target
  let some (opE, rhs, reverse) := eqSides? target (fun e => (detOp? e).isSome) |
    return .notApplicable
  let some (op, A) := detOp? opE | return .notApplicable
  let (model, n) ← match ← squareModel? "det" A with
    | .success r => pure r
    | .notApplicable => return .notApplicable
    | .declined msg => return .declined msg
    | .failure msg => return .failure msg
  checkClosed "det" "right-hand side" rhs
  let input ← model.evalInput "det" n n A
  let proof ← match op with
    | .bareiss quot =>
        let some quotExpr := model.quot? |
          return .declined m!"the {model.name} model has no kernel-checkable exact quotient, so the Bareiss determinant is unavailable"
        unless ← isDefEq quot quotExpr do
          return .declined m!"the quotient{indentExpr quot}\nis not the certified exact quotient of the {model.name} model"
        proveBareiss input quotExpr rhs
    | .leibniz =>
        if leibnizDimension < n then
          return .declined m!"replaying the Leibniz determinant in the kernel is limited to dimension {leibnizDimension}; state the goal with `Hex.Matrix.bareiss`, or import `HexMatrixTacticMathlib` and use a Mathlib matrix"
        kernelDecideProof "det" (← mkEq (← mkAppM ``Hex.Matrix.det #[input.literal]) rhs)
  return .success (← if reverse then mkEqSymm proof else pure proof)

@[term_elab detTerm]
public meta def elabDetTerm : Term.TermElab := fun stx expectedType? => do
  match stx with
  | `(det% $t) =>
      let e ← elabMatrixArgument t
      let result ← (← detCertified e).get "det"
      Term.ensureHasType expectedType? result
  | _ => throwUnsupportedSyntax

@[tactic detTac]
public meta def evalDetTac : Tactic.Tactic := fun _ => Tactic.withMainContext do
  let proof ← (← proveDetGoal (← Tactic.getMainTarget)).get "det"
  Tactic.closeMainGoal `det proof

end Hex.MatrixTactic
