/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public meta import HexRankMathlib.Rational
public import HexRankMathlib.Rational
public meta import Lean

public meta section

/-!
The `rank` tactic on Mathlib matrices: closes `A.rank = r`, `A.rank ≤ r`,
`r ≤ A.rank` (and their mirror images) for a closed integer or rational matrix literal
`A` in one of the four syntaxes of `HexMatrixMathlib.Literal` (`!![…]`,
`Matrix.of ![…]`, `fun i j => …`, `Matrix.ofArray xs h`), possibly behind
definitions.

Compiled code evaluates the entries with `norm_num`, runs the rank producer
and builds a `RankWitness`; the proof is `rank_eq_of_checkList'` applied to
the identification of the literal with the row list `L` of its entries'
numerals (`rfl` for a vector chain, one kernel `decide` on `entriesEq`
otherwise) and to one kernel `decide` on `checkRankList`.
The whole proof is added as an auxiliary lemma on the closed target
(`addClosedProof`), checked synchronously, so the kernel checks it exactly
once, with no elaborator type check first, and a rejection is reported by
the tactic. Rational rows are scaled by their positive denominator least common
multiples and checked by `rank_eq_of_scaledRows`. Entries must be closed numeric
expressions that `norm_num` evaluates and
that the kernel reduces to their numerals (numerals and arithmetic on
them); an entry the kernel cannot reduce is reported as such.

Outcomes follow the matrix-tactic protocol: a goal that is not a rank
comparison, a matrix that is not a closed integer or rational literal, or an open bound
is not applicable and delegates to the next handler; in-fragment errors commit.
A certificate the kernel rejects is a failure (a producer bug, since the
producer re-checks its own output).
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

/-- A recognized integer or rational matrix, with integral rows for certification. -/
structure Literal where
  /-- The recognized literal. -/
  lit : HexMatrixMathlib.Literal.Recognized
  /-- The evaluated entries. -/
  values : Array (Array Int)
  /-- Original rational rows and their positive integer scales. -/
  rat : Option (Array (Array Rat) × Array Nat) := none

/-- Classify the target before evaluating entries or running the producer. An
error here is a reason for numeric inapplicability, not a tactic failure. -/
def classify (target : Expr) : MetaM
    (Except MessageData (Expr × Expr × Rel × Bool × HexMatrixMathlib.Literal.Recognized)) := do
  let target ← instantiateMVars target
  let some (A, other, rel, reverse) := rankTarget? target |
    return .error m!"the goal is not `A.rank = r`, `A.rank ≤ r` or `r ≤ A.rank` for a Mathlib matrix `A`"
  if A.hasFVar || A.hasExprMVar then
    return .error m!"the matrix{indentExpr A}\nmust be a closed term"
  if other.hasFVar || other.hasExprMVar then
    return .error m!"the bound{indentExpr other}\nmust be a closed term"
  let some lit ← HexMatrixMathlib.Literal.literal? A |
    return .error m!"the matrix is not a closed `!![…]`, `Matrix.of ![…]`, `fun i j => …` or `Matrix.ofArray` literal{indentExpr A}"
  unless lit.carrier.isConstOf ``Int || lit.carrier.isConstOf ``Rat do
    return .error m!"only integer and rational matrices are supported; the entry type is{indentExpr lit.carrier}"
  return .ok (A, other, rel, reverse, lit)

/-- Evaluate a recognized literal and clear rational row denominators. -/
def evalLiteral (lit : HexMatrixMathlib.Literal.Recognized) : MetaM Literal := do
  let values ← lit.entries.mapM (·.mapM HexMatrixMathlib.Literal.evalEntry)
  if lit.carrier.isConstOf ``Int then
    return ⟨lit, values.map (·.map (·.num)), none⟩
  let scales := values.map fun row => row.foldl (fun l q => Nat.lcm l q.den) 1
  let rows := values.zipWith (fun row s => row.map fun q => (q * (s : Rat)).num) scales
  return ⟨lit, rows, some (values, scales)⟩

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

/-- Combine a certified rank with the requested comparison, reporting a false
closed target before constructing its kernel proof. -/
def boundProof (r : Nat) (eq other : Expr) (rel : Rel) (reverse : Bool) : MetaM (Expr × Expr) := do
  -- the certified rank as a literal; `c.rank` reduces to it
  let crank := mkNatLit r
  -- a bound that evaluates is compared here, for a clear message on a false target
  if let some v ← (Meta.evalNat other).run then
    let ok : Bool := match rel with
      | .eq => r == v
      | .le => decide (r ≤ v)
      | .ge => decide (v ≤ r)
    unless ok do
      throwError "rank: the target is false: the rank is {r}"
  -- the comparison with the stated bound, decided by the kernel as well
  let bound ← match rel with
    | .eq => mkEq crank other
    | .le => mkAppM ``LE.le #[crank, other]
    | .ge => mkAppM ``LE.le #[other, crank]
  let hbound ← decideProof bound
  let proof ← match rel with
    | .eq =>
        let proof ← mkEqTrans eq hbound
        if reverse then mkEqSymm proof else pure proof
    | .le => mkAppM ``LE.le.trans #[(← mkAppM ``Eq.le #[eq]), hbound]
    | .ge => mkAppM ``LE.le.trans #[hbound, (← mkAppM ``Eq.ge #[eq])]
  return (proof, bound)

/-- The slot width for the packed check: the least positive `W` with
`rank · modulus² < 2^W` (`Nat.lt_log2_self`). -/
def slotWidth (w : RankWitness) : Nat :=
  Nat.log2 (w.rank * (w.modulus * w.modulus)) + 1

/-- Prove a rank target, or throw. -/
def proveGoal (cfg : HexMatrixMathlib.KernelConfig) (target : Expr) : MetaM Expr := do
  let target ← instantiateMVars target
  let .ok (A, other, rel, reverse, recognized) ← classify target | throwUnsupportedSyntax
  let lit ← evalLiteral recognized
  let w ← witness lit
  let L ← rowList lit
  let c := toExpr w
  let nE := mkNatLit lit.lit.n
  let mE := mkNatLit lit.lit.m
  -- the check the kernel evaluates, and a proof of the plain check from it
  let plainCheck ← mkEq (← mkAppM ``Hex.Matrix.checkRankList #[nE, mE, L, c]) (mkConst ``Bool.true)
  let (check, hcheck) ← if cfg.packing then do
      let wE := mkNatLit (slotWidth w)
      let check ← mkEq (← mkAppM ``Hex.Matrix.checkRankListPacked #[wE, nE, mE, L, c])
        (mkConst ``Bool.true)
      let hpacked ← decideProof check
      pure (check, ← mkAppM ``HexMatrixMathlib.checkRankList_of_packed #[wE, nE, mE, L, c, hpacked])
    else
      pure (plainCheck, ← decideProof plainCheck)
  let (eq, ofL) ← match lit.rat with
    | none =>
      let ofL ← mkAppM ``HexMatrixMathlib.ofLists #[nE, mE, L]
      let hA ← HexMatrixMathlib.Literal.identification lit.lit A L
      let eq ← mkAppM ``HexMatrixMathlib.rank_eq_of_checkList' #[A, L, c, hA, hcheck]
      pure (eq, ofL)
    | some (values, scales) =>
      let Q ← HexMatrixMathlib.Literal.rowList (mkConst ``Rat) (values.map (·.map toExpr))
      let s := toExpr scales.toList
      let hA ← HexMatrixMathlib.Literal.identification lit.lit A Q
      let hs ← decideProof (← mkEq
        (← mkAppM ``Hex.Matrix.DetWitness.scaledRows #[s, Q, L]) (mkConst ``Bool.true))
      let eq ← mkAppM ``HexMatrixMathlib.rank_eq_of_scaledRows #[A, Q, s, L, c, hA, hs, hcheck]
      pure (eq, ← mkAppM ``HexMatrixMathlib.ofLists #[nE, mE, Q])
  let (proof, bound) ← boundProof w.rank eq other rel reverse
  -- check synchronously, so that a rejection is reported here, not later
  try
    HexMatrixMathlib.Literal.addClosedProof target proof
  catch e =>
    throw (← diagnose bound check A ofL e)

/-- `rank` closes `A.rank = r`, `A.rank ≤ r` and `r ≤ A.rank` for a closed
integer or rational matrix literal `A`, with the kernel checking a rank certificate.  The
keyword is non-reserved, so `rank` stays usable as an identifier. Extensions
must use `@[no_fallback]` to preserve their errors and `throwUnsupportedSyntax`
to delegate outside their fragment. -/
syntax (name := rankTac) &"rank" optConfig : tactic

/-- Registered before the numeric handler because Lean tries equal-priority
handlers in reverse registration order. Reclassify only to report the reason;
entry evaluation and certificate production belong to the numeric handler. -/
@[tactic rankTac, no_fallback]
def rankFallback : Tactic.Tactic := fun _ => Tactic.withMainContext do
  match ← classify (← Tactic.getMainTarget) with
  | .error msg => throwError "rank: not applicable: {msg}"
  | .ok _ => throwUnsupportedSyntax

-- Ordinary errors commit; unsupported syntax still tries the next handler.
@[tactic rankTac, no_fallback]
def evalRankTac : Tactic.Tactic := fun stx => Tactic.withMainContext do
  let cfg ← HexMatrixMathlib.Literal.elabKernelConfig stx[1]
  let proof ← proveGoal cfg (← Tactic.getMainTarget)
  Tactic.closeMainGoal `rank proof

end HexMatrixMathlib.Rank
