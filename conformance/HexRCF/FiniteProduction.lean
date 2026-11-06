/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module
public import HexRCF.RealCoefficients.FieldCellProgress
public import HexRCF.RealCoefficients.SquareTwo
public meta import HexRCF.RealCoefficients.FieldCellProgress
public meta import HexRCF.RealCoefficients.SquareTwo
public meta import Lean.Elab.Command
public section

namespace Hex.RCF.FiniteProduction
open RealCoefficients

private instance : SquareTwo.polynomial.CheckedIrreducible := SquareTwo.checked
private abbrev hw : atomWitness SquareTwo.polynomial SquareTwo.square := by decide
private abbrev hp : (mahlerPrec SquareTwo.polynomial : Int) ≤ SquareTwo.square.prec := by decide
private abbrev root := SimpleRoot.ofSquare SquareTwo.polynomial SquareTwo.square hw hp
private theorem real : SquareTwo.square.meetsRealAxis = true := by decide
private def values : Fin 1 → PolyQuot SquareTwo.polynomial root := fun _ =>
  SquareTwo.coordinate SquareTwo.square hw hp

private def further : RealFormula.QF 2 :=
  .and (.atom ⟨MvPoly.X 1 ^ 2 - MvPoly.X 0, .eq⟩)
    (.and (.atom ⟨1 - MvPoly.X 1, .lt⟩) (.atom ⟨MvPoly.X 1 - 2, .lt⟩))
private def input (formula : RealFormula.QF 2) (quantifier : RealFormula.Quantifier)
    (divisors : List (PolyQuot SquareTwo.polynomial root) := []) :
    Replay.Input SquareTwo.polynomial SquareTwo.square hw hp Unit 1 :=
  ⟨values, formula, quantifier, divisors, ()⟩

run_meta do
  -- Depth zero disables direct bisection: the complete owner-backed producer
  -- must still find the fourth roots over the original sqrt(2) field.
  let source := input (.and further further) .existsReal [values 0 - 4, values 0 - 4, values 0]
  let .ok certificate := Replay.buildCellsTotal source real 0 |
    throwError "complete fourth-root production failed"
  let .ok bounded := FieldBuild.produceWithin SquareTwo.polynomial SquareTwo.square hw hp real
      source.values source.formula source.context 0 10 source.divisors true |
    throwError "bounded fourth-root fallback failed"
  unless Replay.checkCells source ⟨source, bounded⟩ == .ok true do
    throwError "bounded grouped fourth-root evidence failed strict replay"
  unless certificate.data.isolation.isolations.intervals.size == 4 do
    throwError "complete fourth-root production omitted a carrier root"
  unless Replay.checkCells source certificate == .ok true do
    throwError "complete fourth-root certificate failed frozen replay"
  unless certificate.data.rootSigns.entries.length == 6 do
    throwError "complete production omitted repeated atom occurrences"
  unless certificate.data.radical.core.leadingCoeff == 1 do
    throwError "complete production did not normalize its carrier core"
  let universal := {source with quantifier := .forallReal}
  let .ok falseCertificate := Replay.buildCellsTotal universal real 0 |
    throwError "complete false-universal production failed"
  unless Replay.checkCells universal falseCertificate == .ok false do
    throwError "complete false universal lost its accepted verdict"
  let reordered := {source with divisors := source.divisors.reverse}
  unless Replay.checkCells reordered certificate == .error .binding do
    throwError "complete certificate accepted reordered original guards"
  let missing := {certificate.data.signs with entries := []}
  unless Replay.checkCells source
      {certificate with data := {certificate.data with signs := missing}} == .error .divisor do
    throwError "complete certificate accepted missing original guard signs"
  let rows := {certificate.data.rootSigns with entries := []}
  unless Replay.checkCells source
      {certificate with data := {certificate.data with rootSigns := rows}} == .error .evidence do
    throwError "complete certificate accepted missing atom rows"
  let originalRows := certificate.data.rootSigns
  let omitted := {originalRows with entries := originalRows.entries.take 3}
  let reorderedRows := {originalRows with entries := originalRows.entries.reverse}
  let corruptSecond := {originalRows with entries := originalRows.entries.mapIdx fun i row =>
    if i == 3 then
      {row with evidence := row.evidence.map fun query => {query with value := query.value + 1}}
    else row}
  for mutated in [omitted, reorderedRows, corruptSecond] do
    -- A find-first checker cannot detect these changes: its first occurrence
    -- of each atom still contains the original valid root queries.
    unless mutated.check (FieldQuery.cached certificate.data.signs) FieldDecision.point
        () certificate.data.radical.core certificate.data.isolation.isolations.intervals.toVector
        (RepresentationSpecialize.polynomial source.values) source.formula do
      throwError "duplicate-row control did not distinguish find-first from strict replay"
    unless Replay.checkCells source
        {certificate with data := {certificate.data with rootSigns := mutated}} == .error .evidence do
      throwError "strict replay accepted a missing, reordered or corrupt duplicate row"
  let changedValues := {source with values := fun _ => 0}
  unless Replay.checkCells changedValues {certificate with input := changedValues} ==
      .error .evidence do
    throwError "evidence accepted after coherently rebinding different coefficient values"
  let changedAtom := {source with formula :=
      (.atom ⟨MvPoly.X 1 ^ 2 + MvPoly.X 0, .eq⟩)}
  unless Replay.checkCells changedAtom {certificate with input := changedAtom} ==
      .error .evidence do
    throwError "evidence accepted after coherently rebinding a different atom"
  let .ok empty := Replay.buildCellsTotal (input .tt .forallReal) real 0 |
    throwError "complete empty-formula production failed"
  unless empty.data.isolation.isolations.intervals.isEmpty &&
      Replay.checkCells (input .tt .forallReal) empty == .ok true do
    throwError "complete empty-formula geometry or verdict is incorrect"
  match Replay.buildCellsTotal (input .tt .forallReal [0]) real 0 with
  | .error .divisor => pure ()
  | _ => throwError "complete empty-formula production ignored an original zero divisor"
  Lean.logInfo "FINITE_PRODUCTION: depth-zero fourth-root production; true/false, repeated guards, empty formula and missing-evidence refusal"

end Hex.RCF.FiniteProduction
