/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import HexRCF.RealCoefficients.CellBuild
import HexRCF.RealCoefficients.RootBuild
import HexRCF.RealCoefficients.RowEncode
import HexRCF.CellReplay.Algebraic.Schema
import HexRCF.CellReplay.Algebraic.Literals
import HexRCF.RealCoefficients.RadicalBuild
import HexSignDet.Codec.Bytes
namespace Hex.RCF.RealCoefficients.CellBuildConformance
open Hex Hex.RealClosure Hex.RealClosure.Tower Hex.SignDet
open Hex.RCF.RealCoefficients Hex.RCF.SelectedRootTests
open CellReplayTests.Algebraic.Schema
local instance : Hashable parent.Value := RowEncode.hashable parent.codec
local instance : Hashable Signature := RowEncode.hashable Signature.codec
#eval (show IO Unit from do
  let prepared ← match CellBuild.prepare values [] formula with
    | .error e => throw (IO.userError s!"carrier/root construction failed: {repr e}")
    | .ok prepared => pure prepared
  let radical := prepared.1
  let roots := prepared.2
  unless roots.roots.length == 2 do throw (IO.userError "unexpected complete root count")
  let points (cut : Fin (roots.roots.length+1)) : parent.Value :=
    if cut.val = 0 then -2 else if cut.val = 1 then 0 else 2
  let cells ← match CellBuild.build roots values [] formula points with
    | .error e => throw (IO.userError s!"cell construction failed: {repr e}")
    | .ok cells => pure cells
  let rootGraph := Codec.graph parent.codec Signature.codec (Dag.encode roots.replay)
  let fresh ← match RootReplay.read parent.codec [] radical.core .negInf .posInf rootGraph with
    | .error e => throw (IO.userError s!"root replay failed: {repr e}")
    | .ok fresh => pure fresh
  let rows ← match CellRead.read parent.codec [] fresh values formula cells with
    | .error e => throw (IO.userError s!"cell replay failed: {repr e}")
    | .ok rows => pure rows
  unless (CellReplay.check values formula [] radical fresh rows .existsReal).toOption == some true do
    throw (IO.userError "constructed certificate rejected")
  let packet := Codec.Json.arr #[rootGraph,cells]
  let expected := Codec.Json.arr #[CellReplayTests.Algebraic.Literals.roots,
    .arr #[CellReplayTests.Algebraic.Literals.sections, CellReplayTests.Algebraic.Literals.sectors]]
  unless packet.writeBytes == expected.writeBytes do
    throw (IO.userError "native construction changed the complete kernel-checked fixture")
  unless (CellReplay.check values formula [] radical fresh rows .forallReal).toOption == some false do
    throw (IO.userError "false universal verdict changed")
  match CellBuild.prepare values [0] formula with
  | .error .divisor => pure ()
  | _ => throw (IO.userError "zero divisor reached carrier construction")
  match CellBuild.build roots values [0] formula points with
  | .error .divisor => pure ()
  | _ => throw (IO.userError "zero original divisor accepted")
  match CellBuild.build roots values [] formula (fun _ => 0) with
  | .error .boundary => pure ()
  | _ => throw (IO.userError "invalid exterior point accepted")
  match RootBuild.build (0 : parent.Poly) with
  | .error .domain => pure ()
  | _ => throw (IO.userError "zero carrier domain accepted")
  IO.println "specialization, radical, complete roots and all cell rows produced, frozen and independently replayed")
#eval (show IO Unit from do
  for comparison in [RealFormula.Cmp.eq, RealFormula.Cmp.gt] do
    let matrix : RealFormula.QF 2 := .atom ⟨0, comparison⟩
    let prepared ← match CellBuild.prepare values [] matrix with
      | .error e => throw (IO.userError s!"constant preparation failed: {repr e}")
      | .ok prepared => pure prepared
    let radical := prepared.1
    let roots := prepared.2
    unless roots.roots.isEmpty do throw (IO.userError "constant carrier has roots")
    let cells ← match CellBuild.build roots values [] matrix (fun _ => 0) with
      | .error e => throw (IO.userError s!"constant cells failed: {repr e}")
      | .ok cells => pure cells
    let rows ← match CellRead.read parent.codec [] roots values matrix cells with
      | .error e => throw (IO.userError s!"constant replay failed: {repr e}")
      | .ok rows => pure rows
    for quantifier in [RealFormula.Quantifier.existsReal, RealFormula.Quantifier.forallReal] do
      unless (CellReplay.check values matrix [] radical roots rows quantifier).toOption ==
          some (comparison == RealFormula.Cmp.eq) do
        throw (IO.userError "constant strict fold changed")
    match CellBuild.prepare values [0] matrix with
    | .error .divisor => pure ()
    | _ => throw (IO.userError "constant preparation erased the original guard")
  IO.println "zero atoms and constant carriers preserve both strict quantifiers and original guards")
end Hex.RCF.RealCoefficients.CellBuildConformance
