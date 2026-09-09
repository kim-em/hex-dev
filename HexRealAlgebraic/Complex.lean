/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module
public import HexRealAlgebraic.Basic
public section

/-! Real and imaginary components of canonical complex algebraic numbers. -/
namespace Hex.AlgebraicNumber

/-- Include a real algebraic number in the complex algebraic numbers. -/
@[expose] def ofReal (a : RealAlgebraicNumber) : AlgebraicNumber := a.toAlgebraic

instance : Coe RealAlgebraicNumber AlgebraicNumber := ⟨ofReal⟩

/-- The exact real part. General inputs use `(a + conj a) / 2`; real inputs
return their existing canonical value without arithmetic. -/
@[expose] def re (a : AlgebraicNumber) : RealAlgebraicNumber :=
  if h : a.isReal = true then RealAlgebraicNumber.ofAlgebraic a h
  else RealAlgebraicNumber.Internal.pack ((a + a.conj) / 2)

/-- The exact imaginary part, represented as a real algebraic number.
General inputs use `(a - conj a) / (2 * I)`. -/
@[expose] def im (a : AlgebraicNumber) : RealAlgebraicNumber :=
  if a.isReal then 0
  else RealAlgebraicNumber.Internal.pack ((a - a.conj) / (2 * I))

end Hex.AlgebraicNumber
