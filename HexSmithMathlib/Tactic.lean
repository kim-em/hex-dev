/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexSmithMathlib.Kernel
public meta import HexSmithMathlib.Kernel
public meta import Lean

public meta section

/-! The integer `smith` frontend, using one kernel-checked auxiliary theorem. -/

namespace HexSmithMathlib.Tactic

open Lean Meta Elab HexMatrixMathlib HexMatrixMathlib.Literal

/-- Quote the literal fields of a checked Smith witness. -/
instance instToExprSmithWitness : ToExpr Hex.Matrix.SmithWitness where
  toExpr c := mkAppN (mkConst ``Hex.Matrix.SmithWitness.mk)
    #[toExpr c.rank, toExpr c.diag, toExpr c.left, toExpr c.leftInv,
      toExpr c.right, toExpr c.rightInv, toExpr c.intermediate]
  toTypeExpr := mkConst ``Hex.Matrix.SmithWitness

/-- The shared protocol's nonexceptional outcomes; rejected certificates throw. -/
inductive Outcome (α : Type) where
  | notApplicable
  | declined (message : MessageData)
  | success (value : α)

/-- Evaluated input and its rechecked list certificate. -/
structure Certificate where
  /-- The recognized matrix and its identification route. -/
  literal : Recognized
  /-- The evaluated integer input rows. -/
  rows : List (List Int)
  /-- The rechecked Smith certificate. -/
  witness : Hex.Matrix.SmithWitness

/-- Recognize an integer matrix and produce a rechecked list witness. -/
def certify (A : Expr) : MetaM (Outcome Certificate) := do
  let some (_, _, carrier) ← shape? (← inferType A) | return .notApplicable
  unless (← whnfR carrier).isConstOf ``Int do return .notApplicable
  let some lit ← literal? A |
    return .declined m!"the matrix must be a closed literal within the unfolding budget of {unfoldBudget}{indentExpr A}"
  let entries ← try evalEntries lit catch e => return .declined e.toMessageData
  let rows := entries.toList.map fun row => row.toList.map (·.num)
  let matrix : Hex.Matrix Int lit.n lit.m :=
    Hex.Matrix.ofFn fun i j => ((entries[i.val]!)[j.val]!).num
  let witness := Hex.Matrix.smithWitness matrix
  unless Hex.Matrix.checkSmithList lit.n lit.m rows witness do
    throwError "smith: failure: the producer's certificate fails its list check"
  if ← isTracingEnabledFor `HexMatrix.certificate then
    reportCertificate "smith" (reprStr (rows, witness))
      (rows.flatten ++ witness.diag ++
        [witness.left, witness.leftInv, witness.right, witness.rightInv, witness.intermediate].flatten.flatten)
      [] [("rank", toJson witness.rank)]
  return .success ⟨lit, rows, witness⟩

/-- Find the row family inside a quotient presentation, unfolding definitions
within a fixed search budget. Matrix recognition remains in the shared adapter. -/
partial def presentationInput? (e : Expr) (fuel : Nat := 32) : MetaM (Option Expr) := do
  if fuel == 0 then return none
  if e.getAppFn.isConstOf ``Set.range then
    let A := e.appArg!
    if (← shape? (← inferType A)).isSome then return some A
  for arg in e.getAppArgs.reverse do
    if let some A ← presentationInput? arg (fuel - 1) then return some A
  if let some unfolded ← unfoldDefinition? e then
    return ← presentationInput? unfolded (fuel - 1)
  return none

/-- Assemble and check the input and certificate propositions once. -/
def checked (A : Expr) (c : Certificate) (targetFactors? : Option (Expr × VectorLiteral) := none)
    (freeze : Bool := true) : MetaM Expr := do
  let rows := toExpr c.rows
  let w := toExpr c.witness
  let hA ← identification c.literal A rows
  let proposition ← mkEq
    (← mkAppM ``Hex.Matrix.checkSmithList #[mkNatLit c.literal.n, mkNatLit c.literal.m, rows, w])
    (mkConst ``Bool.true)
  let hc ← decideProof proposition
  let pair ← mkAppM ``And.intro #[hA, hc]
  let (proof, factors?) ← match targetFactors? with
    | none => pure (pair, none)
    | some (d, lit) =>
      let hd ← vectorIdentification lit d (toExpr c.witness.diag)
      pure (← mkAppM ``And.intro #[pair, hd], some d)
  let proof ← if freeze then
      try addClosedProof (← inferType proof) proof
      catch e => throwError "smith: failure: the kernel rejected the certificate: {e.toMessageData}"
    else pure proof
  match factors? with
  | none =>
      let result ← mkAppM ``smith_of_checkList
        #[A, rows, w, ← mkAppM ``And.left #[proof], ← mkAppM ``And.right #[proof]]
      let factors ← mkAppM ``HexMatrixMathlib.vecOfList
        #[mkNatLit c.witness.rank, toExpr c.witness.diag]
      mkAppM ``SmithResult.mk
        #[mkNatLit c.witness.rank, ← mkAppM ``SmithResult.rank_le #[result], factors,
          ← mkAppM ``SmithResult.positive #[result], ← mkAppM ``SmithResult.chain #[result],
          ← mkAppM ``SmithResult.equiv #[result]]
  | some d =>
      let pair ← mkAppM ``And.left #[proof]
      mkAppM ``smith_equiv_of_checkList
        #[A, rows, w, ← mkAppM ``And.left #[pair], ← mkAppM ``And.right #[pair],
          d, ← mkAppM ``And.right #[proof]]

/-- Recognize a canonical quotient goal and assemble its checked equivalence. -/
def prove (target : Expr) : MetaM (Outcome Expr) := do
  let target ← instantiateMVars target
  let (body, wrapped) := if target.getAppFn.isConstOf ``Nonempty then
    (target.appArg!, true) else (target, false)
  let body ← whnfR body
  unless body.getAppFn.isConstOf ``LinearEquiv do return .notApplicable
  let args := body.getAppArgs
  -- Argument 8 is the source module of `LinearEquiv`; the full type is checked below.
  let some domain := args[8]? | return .notApplicable
  let some A ← presentationInput? domain | return .notApplicable
  let some (_, _, carrier) ← shape? (← inferType A) | return .notApplicable
  unless (← whnfR carrier).isConstOf ``Int do return .notApplicable
  let rank ← mkFreshExprMVar (mkConst ``Nat)
  let factors ← mkFreshExprMVar
    (← mkArrow (mkApp (mkConst ``Fin) rank) (mkConst ``Int))
  let expected ← mkAppM ``SmithQuotient #[A, rank, factors]
  unless ← isDefEq expected body do return .notApplicable
  let rank ← instantiateMVars rank
  let factors ← instantiateMVars factors
  let some r ← (Meta.evalNat rank).run |
    return .declined m!"the stated rank must be closed{indentExpr rank}"
  let some factorsLit ← vectorLiteral? factors |
    return .declined m!"the factor function must be a closed vector literal{indentExpr factors}"
  let stated ← try factorsLit.entries.mapM evalEntry catch e => return .declined e.toMessageData
  let c ← match ← certify A with
    | .success c => pure c
    | .notApplicable => return .notApplicable
    | .declined msg => return .declined msg
  unless r == c.witness.rank && stated.toList == c.witness.diag.map (fun z => (z : Rat)) do
    throwError "smith: the target factors do not match: rank {c.witness.rank}, factors {c.witness.diag}"
  let e ← checked A c (some (factors, factorsLit)) (!wrapped)
  if wrapped then
    let proof ← mkAppM ``Nonempty.intro #[e]
    let proof ← try
        addClosedProof (← inferType proof) proof
      catch e => throwError "smith: failure: the kernel rejected the certificate: {e.toMessageData}"
    return .success proof
  return .success e

/-- Return the checked rank, canonical factors and quotient equivalence. -/
syntax (name := smithTerm) "smith% " term : term

/-- Final diagnostic after term elaborators have delegated unsupported carriers. -/
@[term_elab smithTerm]
def smithTermFallback : Term.TermElab := fun _ _ =>
  throwError "smith: the input must be an integer matrix"

/-- Elaborate the literal Smith result with all its proof fields. -/
@[term_elab smithTerm] def elabSmithTerm : Term.TermElab := fun stx expected => do
  let `(smith% $t) := stx | throwUnsupportedSyntax
  let A ← elabArgument t
  match ← certify A with
  | .success c => Term.ensureHasType expected (← checked A c)
  | .notApplicable => throwUnsupportedSyntax
  | .declined msg => throwError "smith: declined: {msg}"

/-- Construct a canonical integer row-presentation quotient equivalence. -/
syntax (name := smithTac) &"smith" : tactic

/-- Last-resort diagnostic, registered before the extensible numeric handler. -/
@[tactic smithTac, no_fallback]
def smithFallback : Tactic.Tactic := fun _ =>
  throwError "smith: expected an integer row-presentation quotient equivalence or its Nonempty wrapper"

/-- Discharge a Smith quotient goal or report the protocol outcome. -/
@[tactic smithTac, no_fallback] def evalSmith : Tactic.Tactic := fun _ => Tactic.withMainContext do
  match ← prove (← Tactic.getMainTarget) with
  | .success e => Tactic.closeMainGoal `smith e
  | .notApplicable => throwUnsupportedSyntax
  | .declined msg => throwError "smith: declined: {msg}"

end HexSmithMathlib.Tactic
