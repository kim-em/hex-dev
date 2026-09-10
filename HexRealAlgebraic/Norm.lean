/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module
public import HexRealAlgebraic.Complex
public import HexRealAlgebraic.Roots
public section

/-! Real-valued squared norm and modulus of complex algebraic numbers. -/
namespace Hex.AlgebraicNumber

/-- The squared complex norm, represented as a real algebraic number. -/
@[expose] def normSq (a : AlgebraicNumber) : RealAlgebraicNumber :=
  RealAlgebraicNumber.Internal.pack (a * a.conj)

/-- The complex modulus. Real inputs reuse their real absolute value; general
inputs take the nonnegative square root of the squared norm. -/
@[expose] def abs (a : AlgebraicNumber) : RealAlgebraicNumber :=
  if h : a.isReal = true then (RealAlgebraicNumber.ofAlgebraic a h).abs
  else match a.normSq.sqrt? with
    | some value => value
    | none => Hex.panicWith 0 "AlgebraicNumber.abs: nonnegative square root failed"

end Hex.AlgebraicNumber
