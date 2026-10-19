/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module
public import HexRCF.RealCoefficients.CellRead
public meta import HexRCF.Tactic
public section
namespace Hex.RCF.RealCoefficients.CellReplayTests.ModuleCheck
open Hex Hex.RealClosure Hex.RealClosure.Tower
variable {registry : BaseContext.Registry} {parent : Tower.Context registry} {n : Nat}

/-- The complete checker and its interpreted conclusion are usable through
ordinary public module imports. -/
theorem sound (model : Model parent ℝ) (values : Fin n → parent.Value)
    (formula : RealFormula.QF (n+1)) (guards : List parent.Value)
    (cert : RadicalCert parent.Value Signature)
    (roots : RootReplay.Result cert.core .negInf .posInf)
    (rows : CellReplay.Evidence roots values formula) (quantifier : RealFormula.Quantifier)
    (accepted : CellReplay.check values formula guards cert roots rows quantifier = .ok true) :
    (RealFormula.Prenex.quant quantifier (.matrix formula)).toProp
      (fun i => model.value (values i)) :=
  CellReplay.check_sound model values formula guards cert roots rows quantifier accepted

/-- Acceptance authenticates every original supplied divisor in that model. -/
theorem domains (model : Model parent ℝ) (values : Fin n → parent.Value)
    (formula : RealFormula.QF (n+1)) (guards : List parent.Value)
    (cert : RadicalCert parent.Value Signature)
    (roots : RootReplay.Result cert.core .negInf .posInf)
    (rows : CellReplay.Evidence roots values formula) (quantifier : RealFormula.Quantifier)
    (verdict : Bool)
    (accepted : CellReplay.check values formula guards cert roots rows quantifier = .ok verdict) :
    ∀ d ∈ guards, model.value d ≠ 0 :=
  CellReplay.check_domains model values formula guards cert roots rows quantifier verdict accepted

open Lean Meta in
run_meta do
  for name in #[``sound, ``domains] do
    let .thmInfo info ← getConstInfo name | throwError "expected actual public cell proof body"
    let _ ← Hex.RCF.checkProof name info.type info.value
    let axioms ← collectAxioms name
    unless axioms.all (fun a => #[``propext, ``Classical.choice, ``Quot.sound].contains a) do
      throwError "unexpected public cell proof axiom"
end Hex.RCF.RealCoefficients.CellReplayTests.ModuleCheck
