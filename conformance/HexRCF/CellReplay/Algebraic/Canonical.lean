/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import HexRCF.CellReplay.Algebraic.Convert
namespace Hex.RCF.RealCoefficients.CellReplayTests.Algebraic.Canonical
open Hex Hex.RealClosure Hex.RealClosure.Tower Hex.SignDet
open Hex.RCF.SelectedRootTests Hex.RCF.RealCoefficients Schema
set_option maxRecDepth 32768
set_option maxHeartbeats 12000000
abbrev facts := Read.facts
def data : Read.Sectors facts :=
  (Read.readAll facts).toOption.get Read.accepted
def roots := Convert.roots facts data
def evidence : CellReplay.Evidence roots values formula := Convert.evidence facts data
def cert : RadicalCert parent.Value Signature :=
  ⟨parent.signature, Inputs.polynomialAt facts,
    Inputs.polynomialAt facts, Inputs.polynomialAt facts, 1⟩
end Hex.RCF.RealCoefficients.CellReplayTests.Algebraic.Canonical
