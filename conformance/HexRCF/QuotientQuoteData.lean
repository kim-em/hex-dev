/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module
public import HexRealFormula
public import HexRCF.RealCoefficients
public section
namespace Hex.RCF.QuotientQuote

@[expose] def polynomial : Hex.RealFormula.Poly 2 := Hex.MvPoly.X 1 ^ 2 - Hex.MvPoly.X 0

@[expose] def reader : Option Nat :=
  if polynomial.termsList.length == 2 then some 7 else none

@[expose] def different : Option Nat :=
  if polynomial.termsList.length == 3 then some 7 else none

end Hex.RCF.QuotientQuote
