/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import HexRCF.CellReplay.Check
import HexRCF.CellReplay.Mutations
import HexRCF.CellReplay.OutsideLiterals
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
def leftFields := (Codec.tuple 6 sectorFields[0]).toOption.get (by decide +kernel)
def middleFields := (Codec.tuple 6 sectorFields[1]).toOption.get (by decide +kernel)
def rightFields := (Codec.tuple 6 sectorFields[2]).toOption.get (by decide +kernel)
def nonnullLeft : Codec.Json := .arr (leftFields.toArray.set! 1 middleFields[1])
def nonnullRight : Codec.Json := .arr (rightFields.toArray.set! 2 middleFields[2])
def nullLeft : Codec.Json := .arr (middleFields.toArray.set! 1 Codec.Json.Value.null)
def nullRight : Codec.Json := .arr (middleFields.toArray.set! 2 Codec.Json.Value.null)
def swappedBounds : Codec.Json := .arr ((middleFields.toArray.set! 1 middleFields[2]).set! 2 middleFields[1])
/-- The middle sample and its complete row are valid at zero. The positive
root lies above zero, so it cannot be the lower boundary of this sample. -/
def outsideLeft : Codec.Json :=
  .arr ((middleFields.toArray.set! 1 middleFields[2]).set! 2 Codec.Json.Value.null)
def cutLeft : Fin (wholeResult.roots.length+1) := ⟨0, by decide +kernel⟩
def cutRight : Fin (wholeResult.roots.length+1) := ⟨2, by decide +kernel⟩
#root_check (match SectorReplay.read Data.base.codec [] wholeResult cutLeft values formula nonnullLeft with
  | .error .binding => true | _ => false) = true => absent_left
#root_check (match SectorReplay.read Data.base.codec [] wholeResult cutRight values formula nonnullRight with
  | .error .binding => true | _ => false) = true => absent_right
#root_check (match sector nullLeft with | .error .evidence => true | _ => false) = true => missing_left
#root_check (match sector nullRight with | .error .evidence => true | _ => false) = true => missing_right
#root_check (match sector swappedBounds with | .error .evidence => true | _ => false) = true => reversed_bounds
#root_check (match SectorReplay.read Data.base.codec [] wholeResult cutRight values formula outsideLeft with
  | .error .binding => true | _ => false) = true => outside_sample

def outsideRight : Codec.Json :=
  .arr ((rightFields.toArray.set! 1 Codec.Json.Value.null).set! 2 CellReplayTests.OutsideLiterals.right)
#root_check ((RowReplay.read Data.base.codec []
  (wholeResult.roots.get ⟨0, by decide +kernel⟩) [Isolation.pointQuery (2 : Data.base.Value)]
  CellReplayTests.OutsideLiterals.right).toOption.map fun signs => signs.values.toList) = some [-1] => upper_packet
#root_check (match SectorReplay.read Data.base.codec [] wholeResult cutLeft values formula outsideRight with
  | .error .binding => true | _ => false) = true => outside_upper

end Hex.RCF.RealCoefficients.CellReplayTests.Refusals
