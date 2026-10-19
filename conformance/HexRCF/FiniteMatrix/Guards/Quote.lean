/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import HexRCF.FiniteMatrix.Guards.Data
open Hex Hex.RealClosure Hex.RealClosure.Algebraic Hex.RealClosure.Algebraic.KernelReplay
open Hex.RCF.RealCoefficients Hex.RCF.RealCoefficients.FiniteMatrixTests
open Lean Meta Elab Command
namespace Hex.RCF.RealCoefficients.FiniteMatrixTests.Guards.Quote
set_option maxHeartbeats 8000000
set_option maxRecDepth 32768
meta def prove (target : Expr) (identities : Array Expr) : MetaM Expr := do
  let entries := mkConst ``Hex.RCF.RealCoefficients.FiniteMatrixTests.Packings.facts
  let checker ← mkAppM ``FiniteSigns.check #[mkConst ``FiniteJoint.next,
    ← mkAppM ``Hex.RCF.RealCoefficients.FiniteMatrixTests.Guards.Schema.positive #[entries],
    ← mkAppM ``Hex.RCF.RealCoefficients.FiniteMatrixTests.Guards.Schema.queries #[entries], mkConst ``Hex.RCF.RealCoefficients.FiniteMatrixTests.Guards.Records.positive,
    mkConst ``Hex.RCF.RealCoefficients.FiniteMatrixTests.Guards.Schema.formula]
  let unit ← mkAppM ``Transport.Closed.read_one #[mkConst ``Semantics.closed]
  FiniteQuote.finish target checker (mkConst ``Hex.RCF.RealCoefficients.FiniteMatrixTests.Guards.Data.accepted)
    (mkConst ``Semantics.read) (mkConst ``Semantics.zero) unit (mkConst ``Hex.RCF.RealCoefficients.FiniteMatrixTests.Data.descriptor)
    (mkConst ``Hex.RCF.RealCoefficients.FiniteMatrixTests.Guards.Data.replay) (mkConst ``Hex.RCF.RealCoefficients.FiniteMatrixTests.Guards.Binding.valuation)
    (← mkAppM ``Hex.RCF.RealCoefficients.FiniteMatrixTests.Guards.Binding.bind #[entries])
    (mkConst ``Hex.RCF.RealCoefficients.FiniteMatrixTests.Guards.Binding.valuation_eq) identities

elab "#frozen_guard_quote" : command => liftTermElabM do
  let target ← Term.elabType (← `(∃ x : ℝ,
    x ^ 2 = Real.sqrt 2 + 0 / (Real.sqrt 2 - 1) + 0 / (-1 : ℝ) ∧ 1 < x ∧ x < 2))
  Term.synthesizeSyntheticMVarsNoPostponing
  let target ← instantiateMVars target
  let proof ← prove target #[mkConst ``Hex.RCF.RealCoefficients.FiniteMatrixTests.Guards.Data.first, mkConst ``Hex.RCF.RealCoefficients.FiniteMatrixTests.Guards.Data.second]
  addDecl (.thmDecl {name := `Hex.RCF.RealCoefficients.FiniteMatrixTests.Guards.Quote.original, levelParams := [], type := target, value := proof})
  logInfo "two original nontrivial signed guards quoted at one joint point"
#frozen_guard_quote
end Hex.RCF.RealCoefficients.FiniteMatrixTests.Guards.Quote
