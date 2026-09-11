/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public meta import HexMatrixTactic
public import HexMatrixTactic
public import HexMatrixMathlib
public import Mathlib.LinearAlgebra.Matrix.Notation
public meta import Mathlib.Data.Fin.VecNotation

public section

/-!
Mathlib matrix literal reconstruction: the batch certificate `matrix_eq`
proving that an evaluated Hex matrix reproduces a closed Mathlib matrix
entrywise, and the recognition, evaluation and quotation of the four literal
syntaxes (`!![…]`, `Matrix.of ![…]`, `fun i j => …`, `Matrix.ofArray xs h`)
through the numeric entry models of `HexMatrixTactic`.

The reconstruction proof is one kernel `decide` on the entrywise equality
rather than a definitional identification of the enumeration with a literal.
-/

namespace HexMatrixTacticMathlib

open HexMatrixMathlib

universe u v

variable {n m : Nat}

/-- A Hex matrix reproduces a Mathlib matrix through a ring homomorphism when
their entries agree. -/
theorem matrix_eq {C : Type u} {R : Type v} [NonAssocSemiring C] [NonAssocSemiring R]
    (B : Hex.Matrix C n m) (φ : C →+* R) (A : Matrix (Fin n) (Fin m) R)
    (hentries : ∀ i j, φ (B[(i, j)]) = A i j) : (matrixEquiv B).map φ = A := by
  ext i j
  rw [Matrix.map_apply, matrixEquiv_apply, ← hentries, Hex.Matrix.getElem_pair_eq_nested]

/-- The entrywise comparison of a Hex matrix with a Mathlib matrix, as a
Boolean the kernel evaluates by enumerating every `(i, j)`. -/
@[expose]
def entriesEq {R : Type u} [DecidableEq R] (B : Hex.Matrix R n m) (A : Matrix (Fin n) (Fin m) R) :
    Bool :=
  (List.finRange n).all fun i => (List.finRange m).all fun j => decide (B[(i, j)] = A i j)

/-- A passing entrywise comparison reconstructs the Mathlib matrix. -/
theorem matrix_eq_of_entriesEq {R : Type u} [DecidableEq R] (B : Hex.Matrix R n m)
    (A : Matrix (Fin n) (Fin m) R) (h : entriesEq B A = true) : matrixEquiv B = A := by
  ext i j
  rw [matrixEquiv_apply, ← Hex.Matrix.getElem_pair_eq_nested]
  have h := List.all_eq_true.mp h i (List.mem_finRange i)
  have h := List.all_eq_true.mp h j (List.mem_finRange j)
  exact of_decide_eq_true h

/-- Same-carrier specialization of `matrix_eq`. -/
theorem matrix_eq_id {R : Type u} (B : Hex.Matrix R n m) (A : Matrix (Fin n) (Fin m) R)
    (hentries : ∀ i j, B[(i, j)] = A i j) : matrixEquiv B = A := by
  ext i j
  rw [matrixEquiv_apply, ← hentries, Hex.Matrix.getElem_pair_eq_nested]

/-- A row-major array literal reproduces a Hex matrix when the entries agree. -/
theorem ofArray_eq {R : Type u} (B : Hex.Matrix R n m) (xs : Array R) (hsize : xs.size = n * m)
    (hentries : ∀ i : Fin n, ∀ j : Fin m, (Matrix.ofArray xs hsize) i j = B[(i, j)]) :
    Matrix.ofArray xs hsize = matrixEquiv B := by
  ext i j
  rw [matrixEquiv_apply, hentries, Hex.Matrix.getElem_pair_eq_nested]

/-- `ofArray_eq` with the hypothesis read at the flat offset `i * m + j`. -/
theorem ofArray_eq_of_flat {R : Type u} (B : Hex.Matrix R n m) (xs : Array R)
    (hsize : xs.size = n * m)
    (hentries : ∀ i : Fin n, ∀ j : Fin m,
      xs[i.val * m + j.val]'(hsize ▸ Hex.Matrix.flatIdx_lt i.isLt j.isLt) = B[(i, j)]) :
    Matrix.ofArray xs hsize = matrixEquiv B := by
  apply ofArray_eq
  intro i j
  rw [Matrix.ofArray_apply, ← hentries i j, Fin.getElem_fin]
  congr 1
  simp [Fin.mkDivMod, Nat.mul_comm]

namespace Literal

open Lean Meta Elab Hex.MatrixTactic

/-- The shape of a Mathlib matrix type `Matrix (Fin n) (Fin m) R`. -/
public meta structure Shape where
  /-- The entry carrier `R`. -/
  carrier : Expr
  /-- The number of rows. -/
  rows : Nat
  /-- The number of columns. -/
  cols : Nat

/-- Recognize the type `Matrix (Fin n) (Fin m) R` with literal dimensions.  A
type that is not a Mathlib matrix returns `none`; a Mathlib matrix indexed by
anything but `Fin` is an error. -/
public meta def shape? (op : String) (ty : Expr) : MetaM (Option Shape) := do
  let ty ← whnfR (← instantiateMVars ty)
  let_expr _root_.Matrix rows cols R := ty | return none
  let_expr Fin nE := (← whnfR rows) |
    throwError "{op}: Mathlib support requires a matrix indexed by `Fin n` and `Fin m`, but the row type is{indentExpr rows}"
  let_expr Fin mE := (← whnfR cols) |
    throwError "{op}: Mathlib support requires a matrix indexed by `Fin n` and `Fin m`, but the column type is{indentExpr cols}"
  let some n ← getNatValue? nE |
    throwError "{op}: the Mathlib matrix dimension must reduce to a concrete natural number{indentExpr nE}"
  let some m ← getNatValue? mE |
    throwError "{op}: the Mathlib matrix dimension must reduce to a concrete natural number{indentExpr mE}"
  return some ⟨← whnfR R, n, m⟩

/-- How many reducible wrappers and definitions are unfolded when looking for
a recognized literal head. -/
public meta def unfoldBudget : Nat := 8

/-- Whether `e` is one of the recognized literal shapes after unfolding
wrappers within `unfoldBudget`: `Matrix.of` applied to a vector chain (the
`!![…]` notation included), a lambda, or `Matrix.ofArray`. -/
public meta partial def isLiteral (e : Expr) (budget : Nat := unfoldBudget) : MetaM Bool := do
  let e ← whnfR e
  if e.isLambda then return true
  let fn := e.getAppFn
  if fn.isConstOf ``Matrix.ofArray then return true
  if fn.isConstOf ``DFunLike.coe then
    let args := e.getAppArgs
    if 6 ≤ args.size && args[4]!.getAppFn.isConstOf ``Matrix.of then return true
  if budget = 0 then return false
  match ← unfoldDefinition? e with
  | some e' => isLiteral e' (budget - 1)
  | none => return false

/-- A closed Mathlib matrix under a numeric entry model, with the Hex matrix
that reproduces it. -/
public meta structure Input where
  /-- The number of rows. -/
  n : Nat
  /-- The number of columns. -/
  m : Nat
  /-- The entry carrier. -/
  carrier : Expr
  /-- The original Mathlib matrix expression. -/
  expr : Expr
  /-- The selected entry model. -/
  model : Model
  /-- The evaluated Hex matrix, with the producers the model offers. -/
  hex : Hex.MatrixTactic.Input n m

/-- The Hex matrix `matrixEquiv.symm A` as an expression, the closed term the
model evaluates. -/
public meta def toHexExpr (carrier : Expr) (n m : Nat) (A : Expr) : MetaM Expr := do
  let equiv ← mkAppOptM ``HexMatrixMathlib.matrixEquiv
    #[some carrier, some (mkNatLit n), some (mkNatLit m)]
  mkAppM ``Equiv.toFun #[← mkAppM ``Equiv.symm #[equiv], A]

/-- Classify and evaluate a closed Mathlib matrix expression.  A type other
than a Mathlib matrix is `notApplicable`; a matrix outside the literal fragment
or without a numeric entry model is `declined`. -/
public meta def input? (op : String) (e : Expr) : MetaM (Outcome Input) := do
  let e ← instantiateMVars e
  let some shape ← shape? op (← inferType e) | return .notApplicable
  checkClosed op "matrix" e
  unless ← isLiteral e do
    return .declined m!"the matrix{indentExpr e}\nis not a recognized literal (`!![…]`, `Matrix.of ![…]`, `fun i j => …`, or `Matrix.ofArray`)"
  let some model ← modelFor? shape.carrier |
    return .declined m!"no numeric entry model for the carrier{indentExpr shape.carrier}"
  let hexExpr ← toHexExpr shape.carrier shape.rows shape.cols e
  let hex ← model.evalInput op shape.rows shape.cols hexExpr
  return .success ⟨shape.rows, shape.cols, shape.carrier, e, model, hex⟩

/-- Instantiate a theorem whose next explicit hypothesis is a decidable
proposition: return the proposition so the caller can prove it in the kernel. -/
public meta def hypothesisType (applied : Expr) : MetaM Expr := do
  let ty ← whnf (← inferType applied)
  unless ty.isForall do
    throwError "internal error: expected a remaining hypothesis in{indentExpr ty}"
  return ty.bindingDomain!

/-- Prove `matrixEquiv B = A` for the literal `B` of an input by one kernel
`decide` on the entrywise equality. -/
public meta def reconstructionProof (op : String) (input : Input) : MetaM Expr := do
  let applied ← mkAppM ``HexMatrixTacticMathlib.matrix_eq_of_entriesEq
    #[input.hex.literal, input.expr]
  let hentries ← kernelDecideProof op (← hypothesisType applied)
  return mkApp applied hentries

/-- Elaborate a Mathlib matrix argument.  The `!![…]` notations are given an
integer coefficient expectation so their numerals do not default to `Nat`. -/
public meta def elabArgument (t : Syntax) : Term.TermElabM Expr := do
  let e ←
    if t.getKind == ``Matrix.matrixNotation ||
        t.getKind == ``Matrix.matrixNotationRx0 ||
        t.getKind == ``Matrix.matrixNotation0xC then
      let n ← mkFreshExprMVar (mkConst ``Nat)
      let m ← mkFreshExprMVar (mkConst ``Nat)
      let fin (k : Expr) := mkApp (mkConst ``Fin) k
      let expected := mkApp3 (mkConst ``Matrix [Level.zero, Level.zero, Level.zero])
        (fin n) (fin m) (mkConst ``Int)
      Term.elabTerm t (some expected)
    else
      Term.elabTerm t none
  Term.synthesizeSyntheticMVarsNoPostponing
  instantiateMVars e

end Literal

end HexMatrixTacticMathlib
