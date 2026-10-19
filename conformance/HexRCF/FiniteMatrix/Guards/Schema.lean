/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import HexRCF.FiniteMatrix.Data
namespace Hex.RCF.RealCoefficients.FiniteMatrixTests.Guards.Schema
open Hex Hex.RealClosure.Algebraic Hex.RealClosure.Algebraic.KernelReplay
open Hex.RCF.RealCoefficients
def positive (entries : List (Packing FiniteTower.first)) : List (Element FiniteTower.first) :=
  let one := @One.one _ (Element.replayOne inferInstance rfl entries)
  [@Sub.sub _ (Element.replaySub inferInstance rfl entries) FiniteTower.generator one,
    @Neg.neg _ (Element.replayNeg (inferInstance : Sub Rat) rfl entries) one]
def guards (zero : Bool) (entries : List (Packing FiniteTower.first)) :=
  if zero then (0 : Element FiniteTower.first) :: (positive entries).tail else positive entries

/-- The entire closed right-hand side occupies one source coordinate.
Both original divisor obligations remain in the separate guard list. -/
abbrev values := Hex.RCF.RealCoefficients.FiniteMatrixTests.Schema.values
abbrev formula := Hex.RCF.RealCoefficients.FiniteMatrixTests.Schema.formula
abbrev queries := Hex.RCF.RealCoefficients.FiniteMatrixTests.Schema.queries

def native := RepresentationSpecialize.prepare values formula

theorem queries_eq (entries : List (Packing FiniteTower.first)) : queries entries = native :=
  Hex.RCF.RealCoefficients.FiniteMatrixTests.Schema.queries_eq entries
def allQueries (zero : Bool) (entries : List (Packing FiniteTower.first)) :=
  (guards zero entries).map DensePoly.C ++ queries entries
end Hex.RCF.RealCoefficients.FiniteMatrixTests.Guards.Schema
