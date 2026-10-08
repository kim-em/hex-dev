/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexRCF.SelectedRoot.Row
public import HexRCF.SelectedRoot.ReplayTools
public import Lean.Elab.Command

public section

meta section
namespace Hex.RCF.SelectedRootTests.RowTools
open Hex.RCF.SelectedRootTests
open Lean Meta Elab Command Hex Hex.RealClosure Hex.SignDet
open Hex.RealClosure.Algebraic

def rules : MetaM SimpTheorems := do
  let mut rules ← ReplayTools.rules
  for name in #[``Row.rowProgram, ``Row.rowResult, ``Row.packetRead, ``Row.evaluate, ``Row.evaluateAt, ``Row.rowProgramAt,
      ``Hex.RCF.RealCoefficients.SelectedFormula.checkRowWith, ``SignEvidence.codec,
      ``Context.readEvidenceWith?, ``Context.readEvidence?, ``SignEvidence.check?,
      ``Dag.selectedSigns?, ``Upper.context] do
    rules ← rules.addDeclToUnfold name
  for name in #[``Context.root_adjoin, ``Context.changeOps_root, ``Descriptor.changeOps_raw] do
    rules ← rules.addConst name
  rules ← rules.addConst ``Upper.raw_eq (inv := true)
  return rules

end Hex.RCF.SelectedRootTests.RowTools
