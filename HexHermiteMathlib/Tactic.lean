/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexHermiteMathlib.Remainder
public meta import HexHermiteMathlib.Remainder
public meta import Lean

public meta section

/-! Certified integer lattice membership and row bases through `hermite`. -/

namespace HexHermiteMathlib.Tactic

open Lean Meta Elab HexMatrixMathlib HexMatrixMathlib.Literal

deriving instance ToExpr for Hex.Matrix.HermiteWitness
deriving instance ToExpr for Hex.Matrix.HermiteRemainder

inductive Outcome (α : Type) where
  | notApplicable
  | declined (message : MessageData)
  | success (value : α)

structure Certificate where
  literal : Recognized
  rows : List (List Int)
  witness : Hex.Matrix.HermiteWitness

def certify (A : Expr) : MetaM (Outcome Certificate) := do
  let some (_, _, carrier) ← shape? (← inferType A) | return .notApplicable
  unless (← whnfR carrier).isConstOf ``Int do return .notApplicable
  let some lit ← literal? A |
    return .declined m!"the matrix must be a closed literal within the unfolding budget of {unfoldBudget}{indentExpr A}"
  let entries ← try evalEntries lit catch e => return .declined e.toMessageData
  let rows := entries.toList.map fun row => row.toList.map (·.num)
  let matrix : Hex.Matrix Int lit.n lit.m :=
    Hex.Matrix.ofFn fun i j => ((entries[i.val]!)[j.val]!).num
  let witness := Hex.Matrix.hermiteWitness matrix
  unless Hex.Matrix.checkHermiteList lit.n lit.m rows witness do
    throwError "hermite: failure: the producer's certificate fails its list check"
  if ← isTracingEnabledFor `HexMatrix.certificate then
    reportCertificate "hermite" (reprStr (rows, witness))
      ([rows, witness.form, witness.transform, witness.inverse].flatten.flatten)
      [] [("rank", toJson witness.rank), ("pivot_entries", toJson witness.pivots.length)]
  return .success ⟨lit, rows, witness⟩

partial def latticeInput? (e : Expr) (fuel : Nat := 32) : MetaM (Option Expr) := do
  if fuel == 0 then return none
  if e.isAppOfArity ``Set.range 3 then
    let A := e.appArg!
    let A := if A.getAppFn.isConstOf ``Matrix.row then A.appArg! else A
    if (← shape? (← inferType A)).isSome then return some A
  for arg in e.getAppArgs.reverse do
    if let some A ← latticeInput? arg (fuel - 1) then return some A
  if let some unfolded ← unfoldDefinition? e then
    return ← latticeInput? unfolded (fuel - 1)
  return none

/-- Check a conjunction once and return its opaque proof projections. -/
def checkProofs (proofs : Array Expr) : MetaM (Array Expr) := do
  let mut combined := proofs.back!
  for p in proofs.toList.dropLast.reverse do
    combined ← mkAppM ``And.intro #[p, combined]
  let mut checked ← try
      addClosedProof (← inferType combined) combined
    catch e => throwError "hermite: failure: the kernel rejected the certificate: {e.toMessageData}"
  let mut result := #[]
  for _ in [:proofs.size - 1] do
    result := result.push (← mkAppM ``And.left #[checked])
    checked ← mkAppM ``And.right #[checked]
  return result.push checked

def inputProofs (A : Expr) (c : Certificate) : MetaM (Array Expr) := do
  let rows := toExpr c.rows
  let w := toExpr c.witness
  let hA ← identification c.literal A rows
  let hc ← decideProof (← mkEq
    (← mkAppM ``Hex.Matrix.checkHermiteList #[mkNatLit c.literal.n, mkNatLit c.literal.m, rows, w])
    (mkConst ``Bool.true))
  return #[hA, hc]

def result (A : Expr) (c : Certificate) (freeze : Bool := true) : MetaM Expr := do
  let proofs ← inputProofs A c
  let proofs ← if freeze then checkProofs proofs else pure proofs
  let r ← mkAppM ``hermite_of_checkList #[A, toExpr c.rows, toExpr c.witness, proofs[0]!, proofs[1]!]
  let form ← mkAppM ``HexMatrixMathlib.ofLists
    #[mkNatLit c.literal.n, mkNatLit c.literal.m, toExpr c.witness.form]
  mkAppM ``HermiteResult.mk
    #[mkNatLit c.witness.rank, ← mkAppM ``HermiteResult.rank_le #[r], form, toExpr c.rows,
      proofs[0]!, toExpr c.witness, ← mkAppM ``HermiteResult.rank_eq #[r],
      ← mkAppM ``HermiteResult.form_eq #[r], proofs[1]!, ← mkAppM ``HermiteResult.hnf #[r],
      ← mkAppM ``HermiteResult.span #[r], ← mkAppM ``HermiteResult.basis #[r],
      ← mkAppM ``HermiteResult.basis_row #[r]]

def membership (A v : Expr) (negated : Bool) : MetaM (Outcome Expr) := do
  let c ← match ← certify A with
    | .success c => pure c
    | .notApplicable => return .notApplicable
    | .declined msg => return .declined msg
  let some vl ← vectorLiteral? v |
    return .declined m!"the lattice vector must be a closed vector literal{indentExpr v}"
  unless vl.size == c.literal.m && vl.carrier.isConstOf ``Int do return .notApplicable
  let values ← try vl.entries.mapM evalEntry catch e => return .declined e.toMessageData
  let vs := values.toList.map (·.num)
  let remainder := Hex.Matrix.hermiteRemainder vs c.witness
  unless Hex.Matrix.checkRemainder c.literal.m vs c.witness remainder do
    throwError "hermite: failure: the producer's remainder fails its list check"
  if ← isTracingEnabledFor `HexMatrix.certificate then
    reportCertificate "hermite_remainder" (reprStr (vs, remainder))
      (vs ++ remainder.coeffs ++ remainder.residual)
  let zero := remainder.isZero c.literal.m
  if zero == negated then
    if zero then throwError "hermite: the vector is a member; HNF coefficients {remainder.coeffs}"
    else throwError "hermite: the vector is not a member; nonzero residual {remainder.residual}"
  let hv ← vectorIdentification vl v (toExpr vs)
  let hr ← decideProof (← mkEq
    (← mkAppM ``Hex.Matrix.checkRemainder
      #[mkNatLit c.literal.m, toExpr vs, toExpr c.witness, toExpr remainder]) (mkConst ``Bool.true))
  let hz ← decideProof (← mkEq
    (← mkAppM ``Hex.Matrix.HermiteRemainder.isZero #[mkNatLit c.literal.m, toExpr remainder]) (toExpr zero))
  let ps := (← inputProofs A c) ++ #[hv, hr, hz]
  let theoremName := if negated then ``not_mem_of_checkList else ``mem_of_checkList
  let proof ← mkAppM theoremName
    #[A, toExpr c.rows, toExpr c.witness, ps[0]!, ps[1]!, v, toExpr vs, ps[2]!,
      toExpr remainder, ps[3]!, ps[4]!]
  return .success (← checkProofs #[proof])[0]!

def prove (target : Expr) : MetaM (Outcome Expr) := do
  let target ← instantiateMVars target
  let negated := target.isAppOfArity ``Not 1
  let member := if negated then target.appArg! else target
  if member.isAppOfArity ``Membership.mem 5 then
    let args := member.getAppArgs
    let some A ← latticeInput? args[3]! | return .notApplicable
    let some (_, _, carrier) ← shape? (← inferType A) | return .notApplicable
    unless (← whnfR carrier).isConstOf ``Int do return .notApplicable
    let span ← mkAppM ``Submodule.span #[mkConst ``Int, ← mkAppM ``Set.range #[A]]
    let expected ← mkAppM ``Membership.mem #[span, args[4]!]
    unless ← isDefEq expected member do return .notApplicable
    return ← membership A args[4]! negated
  let wrapped := target.getAppFn.isConstOf ``Nonempty
  let body ← whnfR (if wrapped then target.appArg! else target)
  unless body.getAppFn.isConstOf ``Module.Basis do return .notApplicable
  let some A ← latticeInput? body | return .notApplicable
  let some (_, _, carrier) ← shape? (← inferType A) | return .notApplicable
  unless (← whnfR carrier).isConstOf ``Int do return .notApplicable
  let rank ← mkFreshExprMVar (mkConst ``Nat)
  unless ← isDefEq (← mkAppM ``HermiteBasis #[A, rank]) body do return .notApplicable
  let rank ← instantiateMVars rank
  let some r ← (Meta.evalNat rank).run |
    return .declined m!"the basis rank must be closed{indentExpr rank}"
  let c ← match ← certify A with
    | .success c => pure c
    | .notApplicable => return .notApplicable
    | .declined msg => return .declined msg
  unless r == c.witness.rank do
    throwError "hermite: the basis dimension does not match: rank {c.witness.rank}"
  let basis ← mkAppM ``HermiteResult.basis #[← result A c (!wrapped)]
  if wrapped then
    let proof ← mkAppM ``Nonempty.intro #[basis]
    return .success (← checkProofs #[proof])[0]!
  return .success basis

syntax (name := hermiteTerm) "hermite% " term : term

@[term_elab hermiteTerm] def elabHermiteTerm : Term.TermElab := fun stx expected => do
  let `(hermite% $t) := stx | throwUnsupportedSyntax
  let A ← elabArgument t
  match ← certify A with
  | .success c => Term.ensureHasType expected (← result A c)
  | .notApplicable => throwError "hermite: the input must be an integer matrix"
  | .declined msg => throwError "hermite: declined: {msg}"

syntax (name := hermiteTac) &"hermite" : tactic

@[tactic hermiteTac] def evalHermite : Tactic.Tactic := fun _ => Tactic.withMainContext do
  match ← prove (← Tactic.getMainTarget) with
  | .success e => Tactic.closeMainGoal `hermite e
  | .notApplicable => throwError "hermite: expected integer row-lattice membership, nonmembership, or a row-lattice basis"
  | .declined msg => throwError "hermite: declined: {msg}"

end HexHermiteMathlib.Tactic
