/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import HexRCF.FiniteMatrix.Data
namespace Hex.RCF.RealCoefficients.FiniteMatrixTests.Quote
open Hex.RealClosure.Algebraic Hex.RealClosure.Algebraic.KernelReplay
open Lean Meta Elab Command
set_option maxHeartbeats 8000000
set_option maxRecDepth 32768
/-- This fixed-packet fixture uses the public quotation API on a fresh source.
It does not supply an existential witness or a theorem of the source goal. -/
meta def prove (target : Expr) (guarded : Bool) : MetaM Expr := do
  let entries := mkConst ``Packings.facts
  let queries ← mkAppM ``Schema.queries #[entries]
  let guards ← mkAppM ``Schema.guards #[toExpr guarded, entries]
  let selected ← mkAppM ``Data.selected #[toExpr guarded]
  let checker ← mkAppM ``FiniteSigns.check
    #[mkConst ``FiniteJoint.next, guards, queries, selected, mkConst ``Schema.formula]
  let unit ← mkAppM ``Hex.RealClosure.Transport.Closed.read_one #[mkConst ``Semantics.closed]
  FiniteQuote.finish target checker (← mkAppM ``Data.accepted #[toExpr guarded])
    (mkConst ``Semantics.read) (mkConst ``Semantics.zero) unit
    (mkConst ``Data.descriptor) (← mkAppM ``Data.replay #[toExpr guarded])
    (mkConst ``Binding.valuation) (← mkAppM ``Binding.bind #[entries])
    (mkConst ``Binding.valuation_eq) (if guarded then #[mkConst ``Data.guardIdentity] else #[])

elab "#finite_matrix_quote" : command => liftTermElabM do
  for (name, guarded) in [("original", false), ("guarded", true)] do
    let sourceSyntax ← if guarded then
      `(∃ x : ℝ, x ^ 2 = Real.sqrt 2 ∧ 1 < x / (2 - 1) ∧ x < 2)
      else `(∃ x : ℝ, x ^ 2 = Real.sqrt 2 ∧ 1 < x ∧ x < 2)
    let target ← Term.elabType sourceSyntax
    Term.synthesizeSyntheticMVarsNoPostponing
    let target ← instantiateMVars target
    let proof ← prove target guarded
    addDecl (.thmDecl {
      name := Name.str `Hex.RCF.RealCoefficients.FiniteMatrixTests.Quote name,
      levelParams := [], type := target, value := proof})
#finite_matrix_quote
end Hex.RCF.RealCoefficients.FiniteMatrixTests.Quote
