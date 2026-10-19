/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public meta import HexRCF.RealCoefficients.CommonTactic
public import HexRCF.RealCoefficients.Registration

public section

namespace Hex.RCF.RealCoefficients.AlgebraicBounds

open Hex.OrderedFn.Oracle

theorem contains_mkRat (ln un : Int) (ld ud : Nat)
    (ordered : mkRat ln ld ≤ mkRat un ud) (x : ℝ)
    (h : (((ln : ℚ) / (ld : ℚ) : ℚ) : ℝ) ≤ x ∧
      x ≤ (((un : ℚ) / (ud : ℚ) : ℚ) : ℝ)) :
    Contains ⟨mkRat ln ld, mkRat un ud, ordered⟩ x := by
  simpa only [Contains, Rat.mkRat_eq_div] using h

end Hex.RCF.RealCoefficients.AlgebraicBounds

public meta section

/-! Finite algebraic enclosures for composition with supplied constant bounds.
Approximation proposes endpoints; fixed-field literal replay proves containment.
The resulting proof contains no approximation or root-production call. -/

namespace Hex.RCF.RealCoefficients.AlgebraicBounds

open Hex Lean Meta Qq Hex.OrderedFn.Oracle

/-- Propose one enclosure and authenticate it through the existing finite
fixed-field checker. This bounded operation promises containment, not a width
or eventual success for every algebraic source presentation. -/
private meta def encloseCore (source : Expr) (request : Rat) : MetaM (Bounds × Expr) := do
  let general ← if RationalRoot.isNotation source || (← RationalRoot.isRealPower source) then
      match ← RationalRoot.parameters? source with
      | .ok (some _) => pure false
      | .ok none =>
          if ← RationalRoot.hasSyntax source then
            throwError "rcf: algebraic enclosure needs a supported selected-field presentation"
          pure true
      | .error error => throwError "rcf: {Hex.RealFormula.Reify.Error.toMessageData error}"
    else pure false
  let value ← if general then do
      -- Authenticate before interval production. Degree one gives the exact
      -- selected value without imposing positivity or discarding original guards.
      let x : Q(ℝ) ← pure source
      let authenticated ← match ← (AlgebraicRoot.identify q($x ^ (1 / 1 : ℝ))
          source 1 Coefficients.prepare
          (CommonTactic.rcf.algebraic.commonDegree.get (← getOptions))).run with
        | .ok identity => pure identity
        | .error error => throwError "rcf: {error.toMessageData}"
      pure authenticated.value
    else do
      let (_, _, value) ← FieldRuntime.coefficient source
      pure value
  let precision := request.den.log2 + 2
  let some interval := rootInterval value precision |
    throwError "rcf: algebraic coefficient enclosure proposal failed"
  let bounds : Bounds := ⟨interval.lower.toRat, interval.upper.toRat, by
    exact (Dyadic.toRat_lt_toRat_iff.mpr interval.lt).le⟩
  let ln : Q(ℤ) := mkIntLit bounds.lower.num
  let ld : Q(ℕ) := mkNatLit bounds.lower.den
  let un : Q(ℤ) := mkIntLit bounds.upper.num
  let ud : Q(ℕ) := mkNatLit bounds.upper.den
  let lower : Q(ℚ) := q(($ln : ℚ) / ($ld : ℚ))
  let upper : Q(ℚ) := q(($un : ℚ) / ($ud : ℚ))
  let x : Q(ℝ) := source
  let target : Q(Prop) := q(∀ _ : ℝ, ($lower : ℝ) ≤ $x ∧ $x ≤ ($upper : ℝ))
  -- Select the existing exact frontend before starting either producer.
  -- Decline, false, budget and replay failures do not start another solver.
  let proof ← if ← Tactic.handlesCoefficient source then
      match ← Tactic.handle target with
      | .proved proof => pure proof
      | .failed message => throwError message
      | .declined => throwError "rcf: selected algebraic enclosure frontend declined"
    else do
      let prepared ← match ← Coefficients.prepare target with
        | .ok prepared => pure prepared
        | .error (.unsupported _ _) =>
            throwError "rcf: algebraic enclosure needs a supported selected-field presentation"
        | .error error => throwError "rcf: {Hex.RealFormula.Reify.Error.toMessageData error}"
      prepared.proveReplay
  let ordered ← mkDecideProof (← mkAppM ``LE.le
    #[← mkAppM ``mkRat #[ln, ld], ← mkAppM ``mkRat #[un, ud]])
  return (bounds, ← mkAppM ``contains_mkRat #[ln, un, ld, ud, ordered, source,
    mkApp proof q((0 : ℝ))])

/-- Enclose transactionally. Successful proof auxiliaries survive, caller
metavariables do not change, and every failure restores the complete state.
The returned containment proof is checked by the ordinary kernel. -/
meta def enclose (source : Expr) (request : Rat) : MetaM (Bounds × Expr) := do
  let saved ← saveState
  let (result, _) ← tryFinally' (withNewMCtxDepth do
    let (bounds, proof) ← encloseCore source request
    let proof ← instantiateMVars proof
    let lower ← mkAppM ``mkRat #[mkIntLit bounds.lower.num, mkNatLit bounds.lower.den]
    let upper ← mkAppM ``mkRat #[mkIntLit bounds.upper.num, mkNatLit bounds.upper.den]
    let ordered ← mkDecideProof (← mkAppM ``LE.le #[lower, upper])
    let literal ← mkAppM ``Bounds.mk #[lower, upper, ordered]
    let target ← mkAppM ``Contains #[literal, source]
    return (bounds, ← Hex.RCF.checkProof `Hex.RCF.RealCoefficients.AlgebraicBounds
      target proof))
    (fun result => do
      match result with
      | some _ => modify fun state => {state with
          mctx := saved.meta.mctx, postponed := saved.meta.postponed,
          zetaDeltaFVarIds := saved.meta.zetaDeltaFVarIds}
      | none => saved.restore)
  return result

end Hex.RCF.RealCoefficients.AlgebraicBounds
