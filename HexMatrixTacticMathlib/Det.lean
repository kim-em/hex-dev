/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public meta import HexMatrixTacticMathlib.Literal
public import HexMatrixTacticMathlib.Literal
public import HexBareissMathlib
public meta import Mathlib.Tactic.NormDet
public import Mathlib.Tactic.NormDet

public section

/-!
The determinant frontend on Mathlib matrices: the certificate adapters that
compose a reconstruction proof, a kernel-replayed Bareiss value and the
producer correspondence `bareissWith_eq_mathlib_det`; the `det%` term form and
`det` tactic on Mathlib inputs; and the opt-in `hex_norm_det` simproc, which
tries the Hex frontend and falls back to Mathlib's `norm_det`.
-/

namespace HexMatrixTacticMathlib

open HexMatrixMathlib

universe u v

variable {n : Nat}

/-- Integer determinant from a reconstruction and a replayed Bareiss value. -/
theorem det_eq_of_bareiss (B : Hex.Matrix Int n n) (A : Matrix (Fin n) (Fin n) Int)
    (hB : matrixEquiv B = A) (d : Int)
    (h : Hex.Matrix.bareissReplay HexArith.Int.exactDiv B = d) : A.det = d := by
  rw [← hB, ← bareiss_eq_mathlib_det, Hex.Matrix.bareiss, Hex.Matrix.bareissWith_eq_replay, h]

/-- Determinant over a commutative ring with a certified exact quotient, from
a reconstruction and a replayed Bareiss value. -/
theorem det_eq_of_bareissWith {C : Type u} [CommRing C] [DecidableEq C] (quot : C → C → C)
    (hquot : ∀ a b : C, b ≠ 0 → quot (a * b) b = a) (B : Hex.Matrix C n n)
    (A : Matrix (Fin n) (Fin n) C) (hB : matrixEquiv B = A) (d : C)
    (h : Hex.Matrix.bareissReplay quot B = d) : A.det = d := by
  rw [← hB, ← bareissWith_eq_mathlib_det quot hquot, Hex.Matrix.bareissWith_eq_replay, h]

/-- `det_eq_of_bareissWith` through a ring homomorphism: the computation runs
in `C` and the target lives in `R`. -/
theorem det_eq_of_bareissWith_map {C : Type u} {R : Type v} [CommRing C] [CommRing R]
    [DecidableEq C] (quot : C → C → C) (hquot : ∀ a b : C, b ≠ 0 → quot (a * b) b = a)
    (B : Hex.Matrix C n n) (φ : C →+* R) (A : Matrix (Fin n) (Fin n) R)
    (hA : (matrixEquiv B).map φ = A) (d : C) (h : Hex.Matrix.bareissReplay quot B = d) :
    A.det = φ d := by
  rw [← hA, ← RingHom.mapMatrix_apply, ← RingHom.map_det,
    ← bareissWith_eq_mathlib_det quot hquot, Hex.Matrix.bareissWith_eq_replay, h]

/-- The exact-quotient law of `Hex.exactDiv` on the rationals. -/
theorem rat_exactDiv_law : ∀ a b : Rat, b ≠ 0 → Hex.exactDiv (a * b) b = a := by
  intro a b hb
  rw [Hex.exactDiv_eq_div_of_ne _ hb]
  exact mul_div_cancel_right₀ a hb

namespace Det

open Lean Meta Elab Hex.MatrixTactic Literal

/-- The exact-quotient law term for a carrier with a non-integer Bareiss
model, or `none`. -/
private meta def quotLaw? (carrier : Expr) : Option Expr :=
  if carrier.isConstOf ``Rat then some (mkConst ``rat_exactDiv_law) else none

/-- Prove `A.det = d` for a square Mathlib input from its Bareiss replay. -/
private meta def proveDet (input : Input) (d : Expr) : MetaM Expr := do
  let some quot := input.model.quot? |
    throwError "det: declined: the {input.model.name} model has no kernel-checkable exact quotient, so the Bareiss determinant is unavailable"
  let hB ← reconstructionProof "det" input
  let applied ←
    if input.carrier.isConstOf ``Int then
      mkAppM ``det_eq_of_bareiss #[input.hex.literal, input.expr, hB, d]
    else
      let some law := quotLaw? input.carrier |
        throwError "det: declined: no exact-quotient law is registered for the {input.model.name} model"
      mkAppM ``det_eq_of_bareissWith #[quot, law, input.hex.literal, input.expr, hB, d]
  let check ← kernelDecideProof "det" (← hypothesisType applied)
  return mkApp applied check

/-- Classify a square Mathlib input for the determinant. -/
private meta def squareInput? (e : Expr) : MetaM (Outcome Input) := do
  match ← input? "det" e with
  | .success input =>
      unless input.n = input.m do
        throwError "det: expected a square matrix, but got dimensions {input.n} × {input.m}"
      return .success input
  | .notApplicable => return .notApplicable
  | .declined msg => return .declined msg
  | .failure msg => return .failure msg

/-- The `det% A` record for a Mathlib input: `Hex.MatrixTactic.Certified Matrix.det A`. -/
public meta def detCertified (e : Expr) : MetaM (Outcome Expr) := do
  let input ← match ← squareInput? e with
    | .success input => pure input
    | .notApplicable => return .notApplicable
    | .declined msg => return .declined msg
    | .failure msg => return .failure msg
  let some bareiss := input.hex.bareiss? |
    return .declined m!"the {input.model.name} model has no kernel-checkable exact quotient, so the Bareiss determinant is unavailable"
  if h : input.n = input.m then
    let value ← bareiss h
    let proof ← proveDet input value
    let some (_, lhs, _) := (← inferType proof).eq? |
      throwError "det: internal error: the adapter did not return an equality"
    return .success (← mkAppOptM ``Hex.MatrixTactic.Certified.mk
      #[none, none, some lhs.appFn!, some input.expr, some value, some proof])
  else
    throwError "det: expected a square matrix, but got dimensions {input.n} × {input.m}"

/-- Prove a Mathlib determinant equality target in either orientation. -/
public meta def proveDetGoal (target : Expr) : MetaM (Outcome Expr) := do
  let target ← instantiateMVars target
  let isDet (e : Expr) := e.getAppFn.isConstOf ``Matrix.det
  let some (detE, rhs, reverse) := eqSides? target isDet | return .notApplicable
  let input ← match ← squareInput? detE.appArg! with
    | .success input => pure input
    | .notApplicable => return .notApplicable
    | .declined msg => return .declined msg
    | .failure msg => return .failure msg
  checkClosed "det" "right-hand side" rhs
  let proof ← proveDet input rhs
  return .success (← if reverse then mkEqSymm proof else pure proof)

@[term_elab Hex.MatrixTactic.detTerm]
public meta def elabDetTerm : Term.TermElab := fun stx expectedType? => do
  match stx with
  | `(det% $t) =>
      let e ← elabArgument t
      let result ← (← detCertified e).get "det"
      Term.ensureHasType expectedType? result
  | _ => throwUnsupportedSyntax

@[tactic Hex.MatrixTactic.detTac]
public meta def evalDetTac : Tactic.Tactic := fun _ => Tactic.withMainContext do
  let proof ← (← proveDetGoal (← Tactic.getMainTarget)).get "det"
  Tactic.closeMainGoal `det proof

/-- Rewrite `Matrix.det A` to its certified value when the Hex frontend
applies; `none` when it does not. -/
public meta def normDet? (e : Expr) : MetaM (Option Simp.Result) := withTransparency .default do
  let e ← instantiateMVars e
  unless e.getAppFn.isConstOf ``Matrix.det do return none
  match ← squareInput? e.appArg! with
  | .success input =>
      let some bareiss := input.hex.bareiss? | return none
      if h : input.n = input.m then
        let value ← bareiss h
        let proof ← proveDet input value
        return some { expr := value, proof? := some proof }
      else
        return none
  | _ => return none

end Det

end HexMatrixTacticMathlib

open Lean Meta in
/-- The `hex_norm_det` simproc rewrites the determinant of a closed matrix
literal to its value through the Hex Bareiss frontend, and falls back to
Mathlib's `norm_det` when the Hex frontend declines. -/
simproc_decl hex_norm_det (Matrix.det _) := fun e => do
  let hex? ← try HexMatrixTacticMathlib.Det.normDet? e catch _ => pure none
  match hex? with
  | some r => return .done r
  | none => norm_det e
