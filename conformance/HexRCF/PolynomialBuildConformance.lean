/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module
public import HexRCF.RealCoefficients.PolynomialBuild
public meta import HexRCF.RealCoefficients.PolynomialBuild
public meta import HexMvPoly.Ring
public meta import Lean.Elab.Command
public section

namespace Hex.RCF.PolynomialBuildConformance
open Hex RealCoefficients Hex.OrderedFn.Oracle Lean

run_meta withoutExporting do
  let t : RealFormula.Poly 2 := MvPoly.X (0 : Fin 2)
  let x : RealFormula.Poly 2 := MvPoly.X (1 : Fin 2)
  let equation : RealFormula.QF 2 := .atom ⟨Mono.powBySq x 2 - t, .eq⟩
  let formula : RealFormula.QF 2 := .and equation
    (.and (.atom ⟨x - 1, .gt⟩) (.atom ⟨x - 2, .lt⟩))
  let bounds := fun _ : Fin 1 =>
    (⟨mkRat 314159265358979323846 100000000000000000000,
      mkRat 314159265358979323847 100000000000000000000, by decide⟩ : Bounds)
  let some cert := PolynomialBuild.build bounds formula 64 |
    throwError "polynomial cell production failed on x^2=pi with 1<x<2"
  unless PolynomialBuild.check bounds formula cert &&
      cert.isolation.isolations.intervals.size == 4 &&
      PolynomialBuild.run formula .existsReal cert == some true &&
      PolynomialBuild.run formula .forallReal cert == some false do
    throwError "polynomial cell production changed complete coverage or a quantified verdict"
  unless !(PolynomialBuild.check bounds formula {cert with index := .empty}) &&
      !(PolynomialBuild.check bounds formula {cert with entries := #[]}) do
    throwError "polynomial cell replay accepted missing signs"
  let wrongRows := {cert.rows with entries := cert.rows.entries.map fun row =>
    {row with evidence := row.evidence.map fun evidence => {evidence with value := evidence.value + 1}}}
  unless !(PolynomialBuild.check bounds formula {cert with rows := wrongRows}) do
    throwError "polynomial cell replay trusted changed rows"
  -- The same ordered polynomials support a different Boolean sentence whose
  -- universal verdict is true. Reusing geometry must not reuse the old verdict.
  let covered : RealFormula.QF 2 := .or (.atom ⟨Mono.powBySq x 2 - t, .gt⟩)
    (.or (.atom ⟨x - 1, .gt⟩) (.atom ⟨x - 2, .lt⟩))
  unless PolynomialBuild.check bounds covered cert &&
      PolynomialBuild.run covered .forallReal cert == some true do
    throwError "polynomial cell replay trusted a stale Boolean verdict"
  let changed : RealFormula.QF 2 := .atom ⟨Mono.powBySq x 2 - t - 1, .eq⟩
  unless !(PolynomialBuild.check bounds changed cert) do
    throwError "polynomial cell replay accepted a changed atom inventory"
  let repeated := RealFormula.QF.and equation equation
  let some shared := PolynomialBuild.build bounds repeated 64 |
    throwError "polynomial cell production failed on repeated roots"
  unless shared.radical.core.natDegree == 2 && shared.rows.entries.length == 2 &&
      shared.isolation.isolations.intervals.size == 2 &&
      PolynomialBuild.run repeated .existsReal shared == some true do
    throwError "polynomial cell production lost common-root reduction or repeated atom rows"
  let broad := fun _ : Fin 1 => (⟨0, 4, by decide⟩ : Bounds)
  unless (PolynomialBuild.build broad formula 64).isNone do
    throwError "polynomial cell production accepted nonseparating coefficient bounds"
  match PolynomialBuild.buildResult bounds formula 0 with
  | .error .isolation => pure ()
  | _ => throwError "polynomial depth exhaustion lost its typed failure stage"
  Lean.logInfo m!"POLYNOMIAL_BUILD: pi root/inequality conjunction; roots=4; sign entries={cert.entries.size}; existential true/universal false; repeated roots and rows; missing/changed/unresolved evidence rejected"

end Hex.RCF.PolynomialBuildConformance
