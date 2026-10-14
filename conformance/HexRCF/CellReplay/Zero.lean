/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import HexRCF.CellReplay.Check
import HexRCF.CellReplay.ZeroLiterals
open Hex Hex.RealClosure Hex.RealClosure.Tower Hex.SignDet
open Hex.RCF.SelectedRootTests Hex.RCF.RealCoefficients
open RootReplayConformance Hex.RCF.RealCoefficients.CellReplayTests.Schema
namespace Hex.RCF.RealCoefficients.CellReplayTests.Zero
set_option maxHeartbeats 12000000
set_option maxRecDepth 32768
def matrix : RealFormula.QF 1 := .atom ⟨0, .eq⟩
def radical : RadicalCert Data.base.Value Signature := ⟨Data.base.signature, 1, 1, 1, 0⟩
def packet : Codec.Json := .arr #[ZeroLiterals.sections, ZeroLiterals.sectors]
def restored := CellRead.read Data.base.codec [] constantResult values matrix packet
#root_check restored.toOption.isSome = true => accepted
def rows := restored.toOption.get accepted
#root_check CellReplay.check values matrix [] radical constantResult rows .forallReal = .ok true => all_checked
#root_check CellReplay.check values matrix [] radical constantResult rows .existsReal = .ok true => exists_checked
def falseMatrix : RealFormula.QF 1 := .atom ⟨0, .gt⟩
def falseRows : CellReplay.Evidence constantResult values falseMatrix :=
  ⟨rows.sections, rows.sectors, fun cut =>
    ⟨(rows.sectorRows cut).root, (rows.sectorRows cut).bound, (rows.sectorRows cut).signs⟩⟩
#root_check CellReplay.check values falseMatrix [] radical constantResult falseRows .forallReal = .ok false => all_false
#root_check CellReplay.check values falseMatrix [] radical constantResult falseRows .existsReal = .ok false => exists_false
#root_check CellReplay.check values matrix [0] radical constantResult rows .forallReal = .error .divisor => zero_guard
#root_check (match CellRead.read Data.base.codec [0] constantResult values matrix Codec.Json.Value.null
  with | .error .divisor => true | _ => false) = true => guard_before_constant
theorem source : ∀ x : ℝ, matrix.toProp (RealFormula.append (fun i => Data.rational.value (values i)) x) :=
  CellReplay.check_sound Data.rational values matrix [] radical constantResult rows .forallReal all_checked
end Hex.RCF.RealCoefficients.CellReplayTests.Zero
