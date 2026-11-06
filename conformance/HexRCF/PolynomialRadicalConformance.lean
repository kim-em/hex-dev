/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module
public import HexRCF.RealCoefficients.PolynomialRadical
public meta import HexRCF.RealCoefficients.PolynomialRadical
public meta import HexMvPoly.Ring
public meta import Lean.Elab.Command
public section

namespace Hex.RCF.PolynomialRadicalConformance
open Hex RealCoefficients Lean
private abbrev E := PolynomialBounds.Poly 1

run_meta withoutExporting do
  let t : E := MvPoly.X (0 : Fin 1)
  let x : DensePoly E := DensePoly.ofList [0, 1]
  let first := x - DensePoly.C t
  let cases := [
    (DensePoly.natPow first 2 * (x + 1), 2),
    (first * (x - 1) * first * (x - 2), 3),
    (DensePoly.C (Mono.powBySq t 5) * x, 1),
    (7, 0)]
  for (product, degree) in cases do
    let some cert := PolynomialRadical.build (7 : Nat) product |
      throwError "polynomial radical failed to propose a checked reduction"
    unless cert.check 7 product && cert.core.natDegree == degree do
      throwError "polynomial radical lost identities or retained repeated roots"
    unless !(cert.check 8 product) &&
        !({cert with cofactor := cert.cofactor + 1}.check 7 product) &&
        !({cert with exponent := product.natDegree + 1}.check 7 product) do
      throwError "polynomial radical accepted a changed context, identity or exponent"
  let content := Mono.powBySq t 5
  let contentProduct := DensePoly.C content * x
  let some cert := PolynomialRadical.build () contentProduct |
    throwError "polynomial radical failed on parameter content"
  unless cert.core.coeff 1 == content do
    throwError "polynomial radical removed parameter content needed by the degree bound"
  unless cert.exponent == 0 do
    throwError "polynomial radical retained an unnecessary power for a squarefree product"
  let some high := PolynomialRadical.build () (DensePoly.natPow first 4 * (x + 1)) |
    throwError "polynomial radical failed its upward exponent search"
  unless high.exponent == 2 do
    throwError "polynomial radical did not choose the least adequate exponent"
  unless (PolynomialRadical.build () (0 : DensePoly E)).isNone do
    throwError "polynomial radical accepted the zero carrier"
  Lean.logInfo "POLYNOMIAL_RADICAL: repeated/common roots reduced; full parameter content retained; constants accepted; zero, changed context, corrupt cofactor and excess exponent rejected"

end Hex.RCF.PolynomialRadicalConformance
