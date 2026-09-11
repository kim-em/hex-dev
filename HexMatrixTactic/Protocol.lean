/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public meta import HexMatrixTactic.Result
public import HexMatrixTactic.Result
public import Lean

public section

/-!
The protocol shared by every matrix frontend operation: the four-way outcome,
kernel-checked Boolean proofs, closedness and shape recognition for
`Hex.Matrix R n m` inputs, and literal builders for reified values.

Compiled code only discovers values.  Every emitted proof is a kernel `decide`
on a closed executable equality, a certificate check, or a soundness theorem
applied to such a check.
-/

namespace Hex.MatrixTactic

open Lean Meta

/-- The outcome of one frontend operation. -/
public meta inductive Outcome (α : Type) where
  /-- The input is outside this frontend's fragment; another frontend may try. -/
  | notApplicable
  /-- The input is in the fragment, but a capability is missing or a budget
  was exceeded.  The message names what is missing. -/
  | declined (msg : MessageData)
  /-- A value together with its proof. -/
  | success (value : α)
  /-- Malformed output or a certificate that failed to check. -/
  | failure (msg : MessageData)

/-- Prove `prop` by evaluating its `Decidable` instance in the kernel.  The
elaborator asks the kernel for the verdict first so that a false or stuck check
is reported by `op` before any proof term is built. -/
public meta def kernelDecideProof (op : String) (prop : Expr) : MetaM Expr := do
  let prop ← instantiateMVars prop
  let d ← mkDecide prop
  let r ← match Kernel.whnf (← getEnv) (← getLCtx) d with
    | .ok r => pure r
    | .error e =>
        throwError "{op}: the kernel could not evaluate the generated check{indentExpr prop}\n{e.toMessageData (← getOptions)}"
  unless r.isConstOf ``Bool.true do
    if r.isConstOf ``Bool.false then
      throwError "{op}: the generated check is false{indentExpr prop}"
    throwError "{op}: kernel evaluation of the generated check got stuck{indentExpr prop}"
  let proof := mkApp3 (mkConst ``of_decide_eq_true) prop d.appArg!
    (← mkEqRefl (mkConst ``Bool.true))
  mkExpectedTypeHint proof prop

/-- Reject free variables and unresolved metavariables before compiled
evaluation. -/
public meta def checkClosed (op what : String) (e : Expr) : MetaM Unit := do
  if e.hasFVar || e.hasExprMVar then
    throwError "{op}: the {what}{indentExpr e}\nmust be a closed term (no local hypotheses or metavariables)"

/-- The carrier and literal dimensions of a `Hex.Matrix R n m` type. -/
public meta structure Shape where
  /-- The entry carrier `R`. -/
  carrier : Expr
  /-- The number of rows. -/
  rows : Nat
  /-- The number of columns. -/
  cols : Nat

/-- Recognize the type `Hex.Matrix R n m`.  A Mathlib matrix type returns
`none`, leaving the syntax to the companion frontend; any other type, or a Hex
matrix type whose dimensions are not literals, is an error. -/
public meta def shape? (op : String) (ty : Expr) : MetaM (Option Shape) := do
  let ty ← whnfR (← instantiateMVars ty)
  let_expr Hex.Matrix R rows cols := ty | do
    if ty.getAppFn.isConstOf `Matrix then
      throwError "{op}: Mathlib matrices need `import HexMatrixTacticMathlib`"
    throwError "{op}: expected a matrix, but the term has type{indentExpr ty}"
  let some n ← getNatValue? rows |
    throwError "{op}: the row dimension must reduce to a concrete natural number{indentExpr rows}"
  let some m ← getNatValue? cols |
    throwError "{op}: the column dimension must reduce to a concrete natural number{indentExpr cols}"
  return some ⟨← whnfR R, n, m⟩

/-- The type `Hex.Matrix R n m` as an expression, for a carrier in `Type`. -/
public meta def matrixType (R : Expr) (n m : Nat) : Expr :=
  mkApp3 (mkConst ``Hex.Matrix [Level.zero]) R (mkNatLit n) (mkNatLit m)

/-- Literal list expression. -/
public meta def listLit (ty : Expr) (xs : List Expr) : Expr :=
  let nil := mkApp (mkConst ``List.nil [Level.zero]) ty
  xs.foldr (fun x acc => mkApp3 (mkConst ``List.cons [Level.zero]) ty x acc) nil

/-- Literal `Array` expression backed by a literal list. -/
public meta def arrayLit (ty : Expr) (xs : List Expr) : Expr :=
  mkApp2 (mkConst ``List.toArray [Level.zero]) ty (listLit ty xs)

/-- Reify a fixed-length vector from reified entries. -/
public meta def vectorLit (ty : Expr) (n : Nat) (xs : List Expr) : MetaM Expr :=
  -- The size proof is `Eq.refl n` against `#[…].size = n`; checking it needs
  -- default transparency, whatever the caller's (a simproc runs reducibly).
  withTransparency .default do
    let size := mkNatLit n
    mkAppOptM ``_root_.Vector.mk
      #[some ty, some size, some (arrayLit ty xs), some (← mkAppM ``Eq.refl #[size])]

/-- Reify a matrix from its reified rows through the public constructor
`Hex.Matrix.ofRows`. -/
public meta def matrixLit (ty : Expr) (n m : Nat) (rows : List (List Expr)) : MetaM Expr :=
  withTransparency .default do
    let rowType := mkApp2 (mkConst ``_root_.Vector [Level.zero]) ty (mkNatLit m)
    let rows ← rows.mapM fun row => vectorLit ty m row
    mkAppM ``Hex.Matrix.ofRows #[← vectorLit rowType n rows]

/-- The literal `⟨i, _⟩ : Fin n`. -/
public meta def finLit (n i : Nat) : MetaM Expr := do
  let lt ← mkAppM ``LT.lt #[mkNatLit i, mkNatLit n]
  mkAppM ``Fin.mk #[mkNatLit i, ← mkDecideProof lt]

/-- Reify an integer vector. -/
public meta def reifyIntVector {n : Nat} (v : _root_.Vector Int n) : MetaM Expr :=
  vectorLit (mkConst ``Int) n (v.toArray.toList.map toExpr)

/-- Reify an integer dense polynomial as `DensePoly.ofCoeffs #[...]`. -/
public meta def reifyZPoly (p : DensePoly Int) : MetaM Expr :=
  mkAppM ``DensePoly.ofCoeffs #[arrayLit (mkConst ``Int) (p.toArray.toList.map toExpr)]

/-- The entries of a matrix, row by row, read through the public `rows`
accessor. -/
public meta def entryRows {R : Type} {n m : Nat} (A : Matrix R n m) : List (List R) :=
  (Matrix.rows A).toList.map (·.toList)

/-- Reify an integer matrix. -/
public meta def reifyIntMatrix {n m : Nat} (A : Matrix Int n m) : MetaM Expr :=
  matrixLit (mkConst ``Int) n m ((entryRows A).map (·.map toExpr))

/-- Prove `DensePoly.beqCoeffs a b = true` by kernel evaluation. -/
public meta def beqCoeffsProof (op : String) (a b : Expr) : MetaM Expr := do
  let check ← mkAppM ``DensePoly.beqCoeffs #[a, b]
  kernelDecideProof op (← mkEq check (mkConst ``Bool.true))

/-- Report an outcome as an elaboration result: `notApplicable` lets the next
frontend try the same syntax, the other non-success outcomes are errors. -/
public meta def Outcome.get {α : Type} (op : String) : Outcome α → MetaM α
  | .notApplicable => Elab.throwUnsupportedSyntax
  | .declined msg => throwError "{op}: declined: {msg}"
  | .failure msg => throwError "{op}: {msg}"
  | .success value => return value

/-- Split an equality target into the operation side and the other side,
returning whether the operation appeared on the right. -/
public meta def eqSides? (target : Expr) (isOp : Expr → Bool) :
    Option (Expr × Expr × Bool) := do
  let some (_, lhs, rhs) := target.eq? | none
  if isOp lhs then some (lhs, rhs, false)
  else if isOp rhs then some (rhs, lhs, true)
  else none

end Hex.MatrixTactic
