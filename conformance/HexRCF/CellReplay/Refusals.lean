/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import HexRCF.CellReplay.Check
import HexRCF.CellReplay.Mutations
open Hex Hex.RealClosure Hex.RealClosure.Tower Hex.SignDet
open Hex.RCF.SelectedRootTests Hex.RCF.RealCoefficients
open RootReplayConformance Hex.RCF.RealCoefficients.CellReplayTests.Schema Hex.RCF.RealCoefficients.CellReplayTests.Check
namespace Hex.RCF.RealCoefficients.CellReplayTests.Refusals
set_option maxHeartbeats 12000000
set_option maxRecDepth 32768
def cut : Fin (wholeResult.roots.length+1) := ⟨1, by decide +kernel⟩
def sector (packet : Codec.Json) := SectorReplay.read Data.base.codec [] wholeResult cut values formula packet
#root_check (match sector CellReplayTests.Mutations.badPoint with | .error .binding => true | _ => false) = true => point_binding
#root_check (match sector CellReplayTests.Mutations.otherRoot with | .error .binding => true | _ => false) = true => root_binding
#root_check (match sector CellReplayTests.Mutations.cycle with | .error .evidence => true | _ => false) = true => cyclic_evidence
#root_check (match sector CellReplayTests.Mutations.stale with | .error .evidence => true | _ => false) = true => stale_context
#root_check (match sector CellReplayTests.Mutations.missingBasis with | .error .evidence => true | _ => false) = true => missing_basis

def lateCycle : Codec.Json := .arr #[CellReplayTests.Literals.sections,
  .arr #[sectorFields[0], CellReplayTests.Mutations.cycle, sectorFields[2]]]
#root_check (match CellRead.read Data.base.codec [] wholeResult values falseMatrix lateCycle with
  | .error .evidence => true | _ => false) = true => false_late_error
end Hex.RCF.RealCoefficients.CellReplayTests.Refusals
