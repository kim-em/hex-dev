/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public meta import HexRankMathlib.Kernel
public import HexRankMathlib.Kernel
public meta import Mathlib.Data.Fin.VecNotation
public meta import Mathlib.Tactic.Echelon.Rat
public meta import Lean

public meta section

/-!
The `rank` tactic on Mathlib matrices: closes `A.rank = r`, `A.rank ≤ r`,
`r ≤ A.rank` (and their mirror images) for a closed integer matrix literal
`A` written as `!![…]` or `Matrix.of ![…]`, possibly behind definitions.

Compiled code evaluates the entries, runs the rank producer and builds a
`RankWitness`; the proof is `rank_eq_of_checkList'` applied to `rfl` (the
literal is definitionally `ofLists n m L` for its row list `L`) and to one
kernel `decide` on `checkRankList`.  The whole proof is added as an auxiliary
theorem so the kernel checks it exactly once.

Outcomes follow the matrix-tactic protocol: a goal that is not a rank
comparison is not applicable; a matrix that is not a closed integer literal is
declined; a certificate the kernel rejects is a failure (a producer bug, since
the producer re-checks its own output).
-/

namespace HexMatrixMathlib.Rank

open Lean Meta Elab Hex.Matrix

deriving instance ToExpr for Hex.Matrix.RankWitness

/-- The comparison a target states between `A.rank` and the other side. -/
inductive Rel where
  /-- `A.rank = r` (or `r = A.rank`). -/
  | eq
  /-- `A.rank ≤ r` (or `r ≥ A.rank`). -/
  | le
  /-- `r ≤ A.rank` (or `A.rank ≥ r`). -/
  | ge

/-- Recognize a rank target: the matrix, the other side, the relation from the
rank's point of view, and whether an equality had the rank on the right. -/
def rankTarget? (target : Expr) : Option (Expr × Expr × Rel × Bool) :=
  let isRank (e : Expr) := e.getAppFn.isConstOf ``Matrix.rank
  match target.getAppFnArgs with
  | (``Eq, #[_, a, b]) =>
      if isRank a then some (a.appArg!, b, .eq, false)
      else if isRank b then some (b.appArg!, a, .eq, true)
      else none
  | (``LE.le, #[_, _, a, b]) =>
      if isRank a then some (a.appArg!, b, .le, false)
      else if isRank b then some (b.appArg!, a, .ge, false)
      else none
  | (``GE.ge, #[_, _, a, b]) =>
      if isRank a then some (a.appArg!, b, .ge, false)
      else if isRank b then some (b.appArg!, a, .le, false)
      else none
  | _ => none

/-- A recognized integer matrix literal: its shape, the entry expressions as
written, and their values. -/
structure Literal where
  /-- Rows. -/
  n : Nat
  /-- Columns. -/
  m : Nat
  /-- The entry expressions, row-major, as they appear in the literal. -/
  entries : Array (Array Expr)
  /-- The evaluated entries. -/
  values : Array (Array Int)

/-- How many definitions are unfolded when looking for a literal. -/
def unfoldBudget : Nat := 8

/-- Match a closed `Matrix.of ![…]` literal (the `!![…]` notation included):
its dimensions, entry type, and rows of entries.  Like Mathlib's
`matchMatrixLit?`, but the dimensions may be any closed expressions that
evaluate to numerals, as `Matrix.of ![…]` elaborates them as `Nat.succ`
chains. -/
def matchLit? (A : Expr) : MetaM (Option (Nat × Nat × Expr × Array (Array Expr))) := do
  if A.hasFVar || A.hasMVar then return none
  let_expr Matrix finM finN R := ← inferType A | return none
  let_expr Fin mE := ← whnfR finM | return none
  let_expr Fin nE := ← whnfR finN | return none
  let some m ← (Meta.evalNat mE).run | return none
  let some n ← (Meta.evalNat nE).run | return none
  let_expr DFunLike.coe _ _ _ _ f v := A | return none
  let_expr Matrix.of _ _ _ := f | return none
  let (rows, _, _) ← Matrix.matchVecConsPrefix mE v
  unless rows.length == m do return none
  let entries ← rows.toArray.mapM fun row => do
    let (es, _, _) ← Matrix.matchVecConsPrefix nE row
    return es.toArray
  unless entries.all (·.size == n) do return none
  return some (m, n, R, entries)

/-- Find the literal behind `A`, unfolding definitions within `unfoldBudget`. -/
partial def matchLiteral? (A : Expr) (budget : Nat := unfoldBudget) :
    MetaM (Option (Nat × Nat × Expr × Array (Array Expr))) := do
  if let some r ← matchLit? A then return some r
  if budget = 0 then return none
  match ← unfoldDefinition? A with
  | some A' => matchLiteral? A' (budget - 1)
  | none => return none

/-- Recognize and evaluate a closed integer literal. -/
def literal? (A : Expr) : MetaM (Option Literal) := do
  let some (n, m, R, entries) ← matchLiteral? A | return none
  unless (← whnfR R).isConstOf ``Int do
    throwError "rank: declined: only integer matrices are supported; the entry type is{indentExpr R}"
  let values ← entries.mapM (·.mapM fun e => do
    let q ← Mathlib.Tactic.Echelon.evalRatEntry true e
    unless q.den = 1 do
      throwError "rank: declined: the entry is not an integer{indentExpr e}"
    return q.num)
  return some ⟨n, m, entries, values⟩

/-- The witness of a literal, by the compiled producer. -/
def witness (lit : Literal) : MetaM RankWitness := do
  let A : Hex.Matrix Int lit.n lit.m := Hex.Matrix.ofFn fun i j => (lit.values[i.val]!)[j.val]!
  match Hex.Matrix.rankWitness A with
  | some w => return w
  | none => throwError "rank: declined: no modulus in `witnessModuli` makes the pivot block's denominator a unit"

/-- The row list of a literal, reusing its entry expressions so that the
identification with the literal is definitional. -/
def rowList (lit : Literal) : MetaM Expr := do
  let int := mkConst ``Int
  let rows ← lit.entries.toList.mapM fun row => mkListLit int row.toList
  mkListLit (mkApp (mkConst ``List [Level.zero]) int) rows

/-- `of_decide_eq_true` on a closed decidable proposition, for the kernel to
evaluate; no elaborator-side evaluation happens. -/
def decideProof (prop : Expr) : MetaM Expr := do
  let d ← mkDecide prop
  return mkApp3 (mkConst ``of_decide_eq_true) prop d.appArg! (← mkEqRefl (mkConst ``Bool.true))

/-- Diagnose a proof the kernel rejected: evaluate each decided proposition
with the kernel and report the first that is false or stuck. -/
def diagnose (props : List Expr) (e : Exception) : MetaM Exception := do
  for prop in props do
    let d ← mkDecide prop
    match Kernel.whnf (← getEnv) (← getLCtx) d with
    | .ok r =>
        if r.isConstOf ``Bool.false then
          return .error e.getRef m!"rank: the target is false: the kernel refutes{indentExpr prop}"
        unless r.isConstOf ``Bool.true do
          return .error e.getRef m!"rank: the kernel check got stuck{indentExpr prop}"
    | .error err =>
        return .error e.getRef
          m!"rank: the kernel could not evaluate the check: {err.toMessageData (← getOptions)}"
  return .error e.getRef m!"rank: the kernel rejected the proof: {e.toMessageData}"

/-- Prove a rank target, or throw. -/
def proveGoal (target : Expr) : MetaM Expr := do
  let target ← instantiateMVars target
  let some (A, other, rel, reverse) := rankTarget? target |
    throwError "rank: the goal is not `A.rank = r`, `A.rank ≤ r` or `r ≤ A.rank` for a Mathlib matrix `A`"
  if A.hasFVar || A.hasExprMVar then
    throwError "rank: declined: the matrix{indentExpr A}\nmust be a closed term"
  if other.hasFVar || other.hasExprMVar then
    throwError "rank: declined: the bound{indentExpr other}\nmust be a closed term"
  let some lit ← literal? A |
    throwError "rank: declined: the matrix is not a closed `!![…]` or `Matrix.of ![…]` literal{indentExpr A}"
  let w ← witness lit
  let L ← rowList lit
  let c := toExpr w
  let nE := mkNatLit lit.n
  let mE := mkNatLit lit.m
  let ofL ← mkAppM ``HexMatrixMathlib.ofLists #[nE, mE, L]
  let hA ← mkExpectedTypeHint (← mkEqRefl A) (← mkEq A ofL)
  let check ← mkEq (← mkAppM ``Hex.Matrix.checkRankList #[nE, mE, L, c]) (mkConst ``Bool.true)
  let hcheck ← decideProof check
  -- the certified rank as a literal; `c.rank` reduces to it
  let crank := mkNatLit w.rank
  -- a bound that evaluates is compared here, for a clear message on a false target
  if let some v ← (Meta.evalNat other).run then
    let ok : Bool := match rel with
      | .eq => w.rank == v
      | .le => decide (w.rank ≤ v)
      | .ge => decide (v ≤ w.rank)
    unless ok do
      throwError "rank: the target is false: the rank is {w.rank}"
  -- the comparison with the stated bound, decided by the kernel as well
  let bound ← match rel with
    | .eq => mkEq crank other
    | .le => mkAppM ``LE.le #[crank, other]
    | .ge => mkAppM ``LE.le #[other, crank]
  let hbound ← decideProof bound
  let proof ← match rel with
    | .eq =>
        let eq ← mkAppM ``HexMatrixMathlib.rank_eq_of_checkList' #[A, L, c, hA, hcheck]
        let proof ← mkEqTrans eq hbound
        if reverse then mkEqSymm proof else pure proof
    | .le => mkAppM ``HexMatrixMathlib.rank_le_of_checkList' #[A, L, c, hA, hcheck, hbound]
    | .ge => mkAppM ``HexMatrixMathlib.le_rank_of_checkList' #[A, L, c, hA, hcheck, hbound]
  try
    mkAuxTheorem target proof
  catch e =>
    throw (← diagnose [bound, check] e)

/-- `rank` closes `A.rank = r`, `A.rank ≤ r` and `r ≤ A.rank` for a closed
integer matrix literal `A`, with the kernel checking a rank certificate.  The
keyword is non-reserved, so `rank` stays usable as an identifier. -/
syntax (name := rankTac) &"rank" : tactic

@[tactic rankTac]
def evalRankTac : Tactic.Tactic := fun _ => Tactic.withMainContext do
  let proof ← proveGoal (← Tactic.getMainTarget)
  Tactic.closeMainGoal `rank proof

end HexMatrixMathlib.Rank
