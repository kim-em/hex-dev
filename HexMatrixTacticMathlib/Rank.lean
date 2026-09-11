/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public meta import HexMatrixTacticMathlib.Literal
public import HexMatrixTacticMathlib.Literal
public import HexRankMathlib

public section

/-!
The rank frontend on Mathlib matrices.  The two-sided certificate of `HexRank`
is discovered by compiled code, replayed by the kernel through `checkRank`,
and transported to `Matrix.rank` by `checkRank_sound`; the adapters here add
the reconstruction step and the two inequality forms.  Rectangular and empty
matrices are accepted.
-/

namespace HexMatrixTacticMathlib

open HexMatrixMathlib

universe u

variable {R : Type u} [CommRing R] [IsDomain R] [DecidableEq R] {n m : Nat}

/-- `Matrix.rank` from a reconstruction and a checked rank certificate. -/
theorem rank_eq_of_check (B : Hex.Matrix R n m) (c : Hex.Matrix.RankCert R n m)
    (A : Matrix (Fin n) (Fin m) R) (hB : matrixEquiv B = A)
    (h : Hex.Matrix.checkRank B c = true) : A.rank = c.rank :=
  hB ▸ checkRank_sound h

/-- The upper bound a checked certificate proves. -/
theorem rank_le_of_check (B : Hex.Matrix R n m) (c : Hex.Matrix.RankCert R n m)
    (A : Matrix (Fin n) (Fin m) R) (hB : matrixEquiv B = A)
    (h : Hex.Matrix.checkRank B c = true) {r : Nat} (hr : c.rank ≤ r) : A.rank ≤ r :=
  (rank_eq_of_check B c A hB h).le.trans hr

/-- The lower bound a checked certificate proves. -/
theorem le_rank_of_check (B : Hex.Matrix R n m) (c : Hex.Matrix.RankCert R n m)
    (A : Matrix (Fin n) (Fin m) R) (hB : matrixEquiv B = A)
    (h : Hex.Matrix.checkRank B c = true) {r : Nat} (hr : r ≤ c.rank) : r ≤ A.rank :=
  hr.trans (rank_eq_of_check B c A hB h).ge

namespace Rank

open Lean Meta Elab Hex.MatrixTactic Literal

/-- The comparison a rank target states between `A.rank` and the other side. -/
private meta inductive Rel where
  | eq
  | le
  | ge

/-- Recognize a Mathlib rank target: the matrix, the other side, the relation
from the rank's point of view, and whether an equality had the rank on the
right. -/
private meta def rankTarget? (target : Expr) : Option (Expr × Expr × Rel × Bool) := do
  let isRank (e : Expr) := e.getAppFn.isConstOf ``Matrix.rank
  if let some (rankE, other, reverse) := eqSides? target isRank then
    return (rankE.appArg!, other, .eq, reverse)
  match target.getAppFnArgs with
  | (``LE.le, #[_, _, a, b]) =>
      if isRank a then some (a.appArg!, b, .le, false)
      else if isRank b then some (b.appArg!, a, .ge, false)
      else none
  | (``GE.ge, #[_, _, a, b]) =>
      if isRank a then some (a.appArg!, b, .ge, false)
      else if isRank b then some (b.appArg!, a, .le, false)
      else none
  | _ => none

/-- The certificate of an input, reified, together with the reconstruction
proof; the certificate check itself is instantiated per adapter. -/
private meta def certificate (input : Input) : MetaM (Expr × Expr) := do
  let some rankCert := input.hex.rankCert? |
    throwError "rank: declined: the {input.model.name} model has no kernel-checkable exact quotient, so the domain rank certificate is unavailable"
  return (← rankCert, ← reconstructionProof "rank" input)

/-- Apply an adapter whose next hypothesis is the certificate check, proving
that check in the kernel. -/
private meta def withCheck (applied : Expr) : MetaM Expr := do
  return mkApp applied (← kernelDecideProof "rank" (← hypothesisType applied))

/-- The `rank% A` record for a Mathlib input: `Hex.MatrixTactic.Certified Matrix.rank A`. -/
public meta def rankCertified (e : Expr) : MetaM (Outcome Expr) := do
  let input ← match ← input? "rank" e with
    | .success input => pure input
    | .notApplicable => return .notApplicable
    | .declined msg => return .declined msg
    | .failure msg => return .failure msg
  let (cert, hB) ← certificate input
  let proof ← withCheck (← mkAppM ``rank_eq_of_check #[input.hex.literal, cert, input.expr, hB])
  let some (_, lhs, rhs) := (← inferType proof).eq? |
    throwError "rank: internal error: the adapter did not return an equality"
  -- `c.rank` reduces to the literal; state the value as that literal.
  let value ← whnfD rhs
  let proof ← mkExpectedTypeHint proof (← mkEq lhs value)
  return .success (← mkAppOptM ``Hex.MatrixTactic.Certified.mk
    #[none, none, some lhs.appFn!, some input.expr, some value, some proof])

/-- Prove a Mathlib rank equality or inequality target. -/
public meta def proveRankGoal (target : Expr) : MetaM (Outcome Expr) := do
  let target ← instantiateMVars target
  let some (A, other, rel, reverse) := rankTarget? target | return .notApplicable
  let input ← match ← input? "rank" A with
    | .success input => pure input
    | .notApplicable => return .notApplicable
    | .declined msg => return .declined msg
    | .failure msg => return .failure msg
  checkClosed "rank" "bound" other
  let (cert, hB) ← certificate input
  let proof ← match rel with
    | .eq =>
        let eq ← withCheck (← mkAppM ``rank_eq_of_check #[input.hex.literal, cert, input.expr, hB])
        -- `c.rank = other` is a closed natural-number equality checked in the kernel.
        let some (_, lhs, crank) := (← inferType eq).eq? |
          throwError "rank: internal error: the adapter did not return an equality"
        let value ← kernelDecideProof "rank" (← mkEq crank other)
        let proof ← mkEqTrans eq value
        let proof ← mkExpectedTypeHint proof (← mkEq lhs other)
        if reverse then mkEqSymm proof else pure proof
    | .le =>
        let applied ← withCheck (← mkAppM ``rank_le_of_check #[input.hex.literal, cert, input.expr, hB])
        let applied := mkApp applied other
        return .success (mkApp applied (← kernelDecideProof "rank" (← hypothesisType applied)))
    | .ge =>
        let applied ← withCheck (← mkAppM ``le_rank_of_check #[input.hex.literal, cert, input.expr, hB])
        let applied := mkApp applied other
        return .success (mkApp applied (← kernelDecideProof "rank" (← hypothesisType applied)))
  return .success proof

@[term_elab Hex.MatrixTactic.rankTerm]
public meta def elabRankTerm : Term.TermElab := fun stx expectedType? => do
  match stx with
  | `(rank% $t) =>
      let e ← elabArgument t
      let result ← (← rankCertified e).get "rank"
      Term.ensureHasType expectedType? result
  | _ => throwUnsupportedSyntax

@[tactic Hex.MatrixTactic.rankTac]
public meta def evalRankTac : Tactic.Tactic := fun _ => Tactic.withMainContext do
  let proof ← (← proveRankGoal (← Tactic.getMainTarget)).get "rank"
  Tactic.closeMainGoal `rank proof

end Rank

end HexMatrixTacticMathlib
