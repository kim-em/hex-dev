/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public meta import HexRankMathlib.Kernel
public import HexRankMathlib.Kernel
public meta import Lean

public meta section

/-!
The `rank` tactic on Mathlib matrices: closes `A.rank = r`, `A.rank ≤ r`,
`r ≤ A.rank` (and their mirror images) for a closed integer matrix literal
`A` in one of the four syntaxes of `HexMatrixMathlib.Literal` (`!![…]`,
`Matrix.of ![…]`, `fun i j => …`, `Matrix.ofArray xs h`), possibly behind
definitions.

Compiled code evaluates the entries with `norm_num`, runs the rank producer
and builds a `RankWitness`; the proof is `rank_eq_of_checkList'` applied to
the identification of the literal with the row list `L` of its entries'
numerals (`rfl` for a vector chain, one kernel `decide` on `entriesEq`
otherwise) and to one kernel `decide` on `checkRankList`.
The whole proof is added as an auxiliary theorem, checked synchronously, so
the kernel checks it exactly once and a rejection is reported by the tactic.
Entries must be closed integer expressions that `norm_num` evaluates and
that the kernel reduces to their numerals (numerals and arithmetic on
them); an entry the kernel cannot reduce is reported as such.

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
rank's point of view, and whether an equality had the rank on the right.
Inequalities must use the ordinary order on `Nat`. -/
def rankTarget? (target : Expr) : Option (Expr × Expr × Rel × Bool) :=
  let isRank (e : Expr) := e.getAppFn.isConstOf ``Matrix.rank
  match target.getAppFnArgs with
  | (``Eq, #[_, a, b]) =>
      if isRank a then some (a.appArg!, b, .eq, false)
      else if isRank b then some (b.appArg!, a, .eq, true)
      else none
  | (``LE.le, #[_, inst, a, b]) =>
      if !inst.isConstOf ``instLENat then none
      else if isRank a then some (a.appArg!, b, .le, false)
      else if isRank b then some (b.appArg!, a, .ge, false)
      else none
  | (``GE.ge, #[_, inst, a, b]) =>
      if !inst.isConstOf ``instLENat then none
      else if isRank a then some (a.appArg!, b, .ge, false)
      else if isRank b then some (b.appArg!, a, .le, false)
      else none
  | _ => none

/-- A recognized integer matrix literal with its evaluated entries. -/
structure Literal where
  /-- The recognized literal. -/
  lit : HexMatrixMathlib.Literal.Recognized
  /-- The evaluated entries. -/
  values : Array (Array Int)

/-- Recognize and evaluate a closed integer literal. -/
def literal? (A : Expr) : MetaM (Option Literal) := do
  let some lit ← HexMatrixMathlib.Literal.literal? A | return none
  unless lit.carrier.isConstOf ``Int do
    throwError "rank: declined: only integer matrices are supported; the entry type is{indentExpr lit.carrier}"
  let values ← lit.entries.mapM (·.mapM fun e => do
    let q ← HexMatrixMathlib.Literal.evalEntry e
    unless q.den = 1 do
      throwError "rank: declined: the entry is not an integer{indentExpr e}"
    return q.num)
  return some ⟨lit, values⟩

/-- The witness of a literal, by the compiled producer. -/
def witness (lit : Literal) : MetaM RankWitness := do
  let A : Hex.Matrix Int lit.lit.n lit.lit.m :=
    Hex.Matrix.ofFn fun i j => (lit.values[i.val]!)[j.val]!
  match Hex.Matrix.rankWitness A with
  | .ok w => return w
  | .error e => throwError "rank: declined: the producer found no witness: {e}"

/-- The row list of a literal as integer numerals.  A numeral entry of the
literal is syntactically the same expression, so the identification with
the literal is by `rfl` at no cost; any other closed entry, such as
`1 - 1`, is reduced to its numeral by the kernel once. -/
def rowList (lit : Literal) : MetaM Expr :=
  HexMatrixMathlib.Literal.rowList (mkConst ``Int) (lit.values.map (·.map toExpr))

open HexMatrixMathlib.Literal (decideProof)

/-- Diagnose a proof the kernel rejected: evaluate the bound comparison and
the certificate check with the kernel, and test the identification of the
literal with its row list, reporting the first that fails. -/
def diagnose (bound check : Expr) (A ofL : Expr) (e : Exception) : MetaM Exception := do
  let env ← getEnv
  let lctx ← getLCtx
  let evalBool (prop : Expr) : MetaM (Option Bool) := do
    match Kernel.whnf env lctx (← mkDecide prop) with
    | .ok r => return if r.isConstOf ``Bool.true then some true
        else if r.isConstOf ``Bool.false then some false else none
    | .error _ => return none
  match ← evalBool bound with
  | some false => return .error e.getRef m!"rank: the target is false: the kernel refutes{indentExpr bound}"
  | none => return .error e.getRef m!"rank: the kernel cannot decide the bound{indentExpr bound}"
  | some true => pure ()
  match ← evalBool check with
  | some false =>
      return .error e.getRef
        m!"rank: the producer's certificate fails the kernel check (a producer bug){indentExpr check}"
  | none => return .error e.getRef m!"rank: the kernel check got stuck{indentExpr check}"
  | some true => pure ()
  match Kernel.isDefEq env lctx A ofL with
  | .ok true => pure ()
  | _ =>
      return .error e.getRef
        m!"rank: the entries of the matrix do not reduce to their numerals in the kernel{indentExpr A}"
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
    throwError "rank: declined: the matrix is not a closed `!![…]`, `Matrix.of ![…]`, `fun i j => …` or `Matrix.ofArray` literal{indentExpr A}"
  let w ← witness lit
  let L ← rowList lit
  let c := toExpr w
  let nE := mkNatLit lit.lit.n
  let mE := mkNatLit lit.lit.m
  let ofL ← mkAppM ``HexMatrixMathlib.ofLists #[nE, mE, L]
  let hA ← HexMatrixMathlib.Literal.identification lit.lit A L
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
  -- check synchronously, so that a rejection is reported here, not later
  try
    withOptions (Lean.Elab.async.set · false) do
      mkAuxTheorem target proof
  catch e =>
    throw (← diagnose bound check A ofL e)

/-- `rank` closes `A.rank = r`, `A.rank ≤ r` and `r ≤ A.rank` for a closed
integer matrix literal `A`, with the kernel checking a rank certificate.  The
keyword is non-reserved, so `rank` stays usable as an identifier. -/
syntax (name := rankTac) &"rank" : tactic

@[tactic rankTac]
def evalRankTac : Tactic.Tactic := fun _ => Tactic.withMainContext do
  let proof ← proveGoal (← Tactic.getMainTarget)
  Tactic.closeMainGoal `rank proof

end HexMatrixMathlib.Rank
