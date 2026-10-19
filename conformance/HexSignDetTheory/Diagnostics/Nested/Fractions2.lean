/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexSignDetTheory.Diagnostics.Nested.Fractions
public meta import HexRationalFn.Basic
public meta import HexRationalFn.Arithmetic
public meta import HexRationalFn.Field

public section

namespace Hex.SignDetTheory.Diagnostics.Nested.Fractions2
open Hex.SignDet
open scoped Hex

local instance : NatCast (RationalFn Rat) := Lean.Grind.Semiring.natCast

/-- Embed a supplied literal predecessor polynomial, with denominator one. -/
@[expose] def coeff (xs : Array Rat) : RationalFn Rat :=
  RationalFn.ofPoly (DensePoly.ofCoeffs xs)

/-- The predecessor generator is ε₁+ε₁²; the current variable is ε₂. -/
@[expose] def firstCert : RationalFn.Cert (RationalFn Rat) :=
  ⟨#p[0, coeff #[0, 1, 1], 1], #p[1, coeff #[0, 1, 1], 1], #p[-1], #p[1]⟩

@[expose] def secondCert : RationalFn.Cert (RationalFn Rat) :=
  ⟨#p[0, coeff #[0, 1, 1], 1], #p[2, coeff #[0, 1, 1], 1],
    #p[coeff #[-1/2]], #p[coeff #[1/2]]⟩

@[expose] def squareCert : RationalFn.Cert (RationalFn Rat) :=
  ⟨#p[0, 0, coeff #[0, 0, 1, 2, 1], coeff #[0, 2, 2], 1],
    #p[1, coeff #[0, 2, 2], coeff #[2, 0, 1, 2, 1], coeff #[0, 2, 2], 1],
    #p[3, coeff #[0, 2, 2], 2], #p[1, coeff #[0, -2, -2], -2]⟩

@[expose] def sumCert : RationalFn.Cert (RationalFn Rat) :=
  ⟨#p[0, coeff #[0, 3, 3], coeff #[3, 0, 2, 4, 2], coeff #[0, 4, 4], 2],
    #p[2, coeff #[0, 3, 3], coeff #[3, 0, 1, 2, 1], coeff #[0, 2, 2], 1],
    #p[coeff #[-5/2], coeff #[0, -3/2, -3/2], coeff #[-3/2]],
    #p[coeff #[1/2], coeff #[0, 3, 3], 3]⟩

@[expose] def first : RationalFn (RationalFn Rat) :=
  RationalFn.ofCert firstCert.num firstCert.den firstCert (by decide +kernel)

@[expose] def second : RationalFn (RationalFn Rat) :=
  RationalFn.ofCert secondCert.num secondCert.den secondCert (by decide +kernel)

@[expose] def square : RationalFn (RationalFn Rat) :=
  RationalFn.ofCert squareCert.num squareCert.den squareCert (by decide +kernel)

@[expose] def sum : RationalFn (RationalFn Rat) :=
  RationalFn.ofCert sumCert.num sumCert.den sumCert (by decide +kernel)

/-- The same literal graph over two actual rational-function field levels. -/
@[expose] def check (badProduct : Bool := false) : Bool :=
  letI : NatCast (RationalFn (RationalFn Rat)) := Lean.Grind.Semiring.natCast
  let evidence := Nested.graph first (if badProduct then second else square)
  evidence.check (OrderedFn.Infinitesimal.sign
      (OrderedFn.Infinitesimal.sign Sturm.orderSign))
    7 Nested.head .negInf .posInf [DensePoly.C first, DensePoly.C first]

end Hex.SignDetTheory.Diagnostics.Nested.Fractions2
