/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexSignDetTheory.Diagnostics.Nested.Inputs
public meta import HexRationalFn.Basic
public meta import HexRationalFn.Arithmetic
public meta import HexRationalFn.Field

public section

namespace Hex.SignDetMathlib.Diagnostics.Nested.Fractions
open Hex.SignDet
open scoped Hex

/-- Supplied ε(1+ε)/(1+ε+ε²), with a literal Bezout witness. -/
@[expose] def firstCert : RationalFn.Cert Rat :=
  ⟨#p[0, 1, 1], #p[1, 1, 1], #p[-1], #p[1]⟩

/-- Supplied ε(1+ε)/(2+ε+ε²), with a literal Bezout witness. -/
@[expose] def secondCert : RationalFn.Cert Rat :=
  ⟨#p[0, 1, 1], #p[2, 1, 1], #p[-1/2], #p[1/2]⟩

/-- Supplied square of the first fraction; no normalization producer runs. -/
@[expose] def squareCert : RationalFn.Cert Rat :=
  ⟨#p[0, 0, 1, 2, 1], #p[1, 2, 3, 2, 1], #p[3, 2, 2], #p[1, -2, -2]⟩

/-- Supplied sum of fractions with distinct nonunit denominators. -/
@[expose] def sumCert : RationalFn.Cert Rat :=
  ⟨#p[0, 3, 5, 4, 2], #p[2, 3, 4, 2, 1], #p[-5/2, -3/2, -3/2], #p[1/2, 3, 3]⟩

@[expose] def first : RationalFn Rat :=
  RationalFn.ofCert firstCert.num firstCert.den firstCert (by decide +kernel)

@[expose] def second : RationalFn Rat :=
  RationalFn.ofCert secondCert.num secondCert.den secondCert (by decide +kernel)

@[expose] def square : RationalFn Rat :=
  RationalFn.ofCert squareCert.num squareCert.den squareCert (by decide +kernel)

@[expose] def sum : RationalFn Rat :=
  RationalFn.ofCert sumCert.num sumCert.den sumCert (by decide +kernel)

/-- Replay with nonunit coefficient denominators. The product forgery supplies
another positive fraction as the square, leaving all reported signs unchanged. -/
@[expose] def check (badProduct : Bool := false) : Bool :=
  letI : NatCast (RationalFn Rat) := Lean.Grind.Semiring.natCast
  let evidence := Nested.graph first (if badProduct then second else square)
  evidence.check (OrderedFn.Infinitesimal.sign Sturm.orderSign)
    7 Nested.head .negInf .posInf [DensePoly.C first, DensePoly.C first]

end Hex.SignDetMathlib.Diagnostics.Nested.Fractions
