/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import HexRCF.FiniteMatrix.Guards.Quotient.Binding
open Hex Hex.RealClosure Hex.RealClosure.Algebraic Hex.RealClosure.Algebraic.KernelReplay
open Hex.RCF.RealCoefficients Hex.RCF.RealCoefficients.FiniteMatrixTests
open Lean Meta Elab Command
namespace Hex.RCF.RealCoefficients.FiniteMatrixTests.Guards.Quotient.Quote
set_option maxHeartbeats 8000000
set_option maxRecDepth 32768

theorem accepted : FiniteSigns.check FiniteJoint.next (Guards.Schema.positive Packings.facts)
    (Guards.Schema.queries Packings.facts) Guards.Records.positive Source.formula =
    .ok true := by decide +kernel

run_meta do
  let type ← inferType (mkConst ``accepted)
  Hex.RCF.SelectedRootTests.KernelCheck.addChecked
    `Hex.RCF.RealCoefficients.FiniteMatrixTests.Guards.Quotient.Quote.decision type
    (← mkDecideProof type) #[``Hex.SignDet.Descriptor.validate, ``Hex.SignDet.Descriptor.ofReplay?]
    #[``FiniteSigns.Row.check]

meta def prove (target : Expr) : MetaM Expr := do
  let entries := mkConst ``Packings.facts
  let checker ← mkAppM ``FiniteSigns.check #[mkConst ``FiniteJoint.next,
    ← mkAppM ``Guards.Schema.positive #[entries],
    ← mkAppM ``Guards.Schema.queries #[entries], mkConst ``Guards.Records.positive,
    mkConst ``Source.formula]
  FiniteQuote.finish target checker (mkConst ``accepted)
    (mkConst ``Semantics.read) (mkConst ``Semantics.zero)
    (← mkAppM ``Transport.Closed.read_one #[mkConst ``Semantics.closed])
    (mkConst ``Hex.RCF.RealCoefficients.FiniteMatrixTests.Data.descriptor)
    (mkConst ``Guards.Data.replay) (mkConst ``Binding.valuation)
    (mkConst ``Binding.bind) (mkConst ``Binding.valuation_eq)
    #[mkConst ``Guards.Data.first, mkConst ``Guards.Data.second]

elab "#frozen_quotient_quote" : command => liftTermElabM do
  let target ← Term.elabType (← `(∃ x : ℝ,
    x ^ 2 + 1 = 1 / (Real.sqrt 2 - 1) + 0 / (-1 : ℝ) ∧ 1 < x ∧ x < 2))
  Term.synthesizeSyntheticMVarsNoPostponing
  let target ← instantiateMVars target
  let proof ← prove target
  addDecl (.thmDecl {
    name := `Hex.RCF.RealCoefficients.FiniteMatrixTests.Guards.Quotient.Quote.original
    levelParams := []
    type := target
    value := proof })
  logInfo "frozen nonzero quotient quoted through actual inverse-equation and matrix replay"
#frozen_quotient_quote
end Hex.RCF.RealCoefficients.FiniteMatrixTests.Guards.Quotient.Quote
