/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import HexRCF.CellReplay.Schema
import HexRCF.RealCoefficients.CellRead
import HexRCF.CellReplay.Literals
open Hex Hex.RealClosure Hex.RealClosure.Tower Hex.SignDet
open Hex.RCF.SelectedRootTests Hex.RCF.RealCoefficients
open RootReplayConformance Hex.RCF.RealCoefficients.CellReplayTests.Schema
namespace Hex.RCF.RealCoefficients.CellReplayTests.Check
set_option maxHeartbeats 12000000
set_option maxRecDepth 32768

def packet : Codec.Json := .arr #[CellReplayTests.Literals.sections, CellReplayTests.Literals.sectors]
def restored := CellRead.read Data.base.codec [] wholeResult values formula packet
#root_check restored.toOption.isSome = true => accepted

def evidence := restored.toOption.get accepted
#root_check CellReplay.check values formula [] cert wholeResult evidence .existsReal = .ok true => exists_checked
#root_check CellReplay.check values formula [] cert wholeResult evidence .forallReal = .ok false => forall_false
#root_check CellReplay.check values formula [0] cert wholeResult evidence .existsReal = .error .divisor => zero_refused
#root_check (match CellRead.read Data.base.codec [0] wholeResult values formula
  Codec.Json.Value.null with | .error .divisor => true | _ => false) = true => zero_before_decode

def falseMatrix : RealFormula.QF 1 := .and formula .ff
def falseEvidence : CellReplay.Evidence wholeResult values falseMatrix :=
  ⟨evidence.sections, evidence.sectors, fun cut =>
    ⟨(evidence.sectorRows cut).root, (evidence.sectorRows cut).bound,
      (evidence.sectorRows cut).signs⟩⟩
#root_check CellReplay.check values falseMatrix [] cert wholeResult falseEvidence .existsReal = .ok false => exists_false
#root_check CellReplay.check values falseMatrix [] cert wholeResult falseEvidence .forallReal = .ok false => false_all

def trueMatrix : RealFormula.QF 1 := .or formula .tt
def trueEvidence : CellReplay.Evidence wholeResult values trueMatrix :=
  ⟨evidence.sections, evidence.sectors, fun cut =>
    ⟨(evidence.sectorRows cut).root, (evidence.sectorRows cut).bound,
      (evidence.sectorRows cut).signs⟩⟩
#root_check CellReplay.check values trueMatrix [] cert wholeResult trueEvidence .forallReal = .ok true => forall_checked

def sectionFields := (Codec.tuple 2 CellReplayTests.Literals.sections).toOption.get (by decide +kernel)
def sectorFields := (Codec.tuple 3 CellReplayTests.Literals.sectors).toOption.get (by decide +kernel)
def swappedSections : Codec.Json := .arr #[.arr #[sectionFields[1], sectionFields[0]], CellReplayTests.Literals.sectors]
def omittedSector : Codec.Json := .arr #[CellReplayTests.Literals.sections, .arr #[sectorFields[0], sectorFields[1]]]
#root_check (CellRead.read Data.base.codec [] wholeResult values formula swappedSections).toOption.isSome = false => wrong_sections
#root_check (CellRead.read Data.base.codec [] wholeResult values formula omittedSector).toOption.isSome = false => missing_sector

theorem guarded_checked : CellReplay.check values formula [-1] cert wholeResult evidence .existsReal = .ok true := by
  have same : CellReplay.check values formula [-1] cert wholeResult evidence .existsReal =
      CellReplay.check values formula [] cert wholeResult evidence .existsReal := by rfl
  exact same.trans exists_checked

theorem negative_guard : Data.rational.value (-1 : Data.base.Value) = (-1 : ℝ) := by
  rw [Data.rational.neg, Data.rational.one]

theorem source : ∃ x : ℝ, formula.toProp (RealFormula.append (fun i => Data.rational.value (values i)) x) :=
  CellReplay.check_sound Data.rational values formula [] cert wholeResult evidence .existsReal exists_checked
#print axioms source
end Hex.RCF.RealCoefficients.CellReplayTests.Check
