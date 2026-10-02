/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexSignDet
public import HexRationalFn
public import HexOrderedFn.Infinitesimal
public meta import HexRationalFn
public meta import HexOrderedFn.Infinitesimal

public section

/-! Exact infinitesimal conformance using the ordered-function library.
The outer indeterminate is positive and smaller than every positive base-field element. -/
namespace Hex.SignDet.Infinitesimal

/-- A fraction's sign is the product of its numerator and denominator signs. -/
abbrev sign := @OrderedFn.Infinitesimal.sign

abbrev First := RationalFn Rat
abbrev Second := RationalFn First

def firstSign : First → Int := sign Sturm.orderSign
def secondSign : Second → Int := sign firstSign

def epsilon : First := RationalFn.X
def delta : Second := RationalFn.X
def lift (a : First) : Second := RationalFn.C a

def x {K : Type} [Zero K] [One K] [DecidableEq K] : DensePoly K :=
  DensePoly.ofCoeffs #[0, 1]

/-- The corrected de Moura–Passmore example. -/
def passmore : DensePoly First :=
  (DensePoly.C epsilon * x.natPow 2 - 1) * (DensePoly.C epsilon * x.natPow 3 - 1)

/-- Three nested-level roots, in the order δ, ε, ε+δ. -/
def nested : DensePoly Second :=
  (x - DensePoly.C delta) * (x - DensePoly.C (lift epsilon)) *
    (x - DensePoly.C (lift epsilon + delta))

#guard firstSign 0 = 0
#guard firstSign (epsilon - 1) = -1
#guard firstSign (epsilon / (epsilon - 1)) = -1
#guard firstSign ((epsilon * epsilon - 1) / (epsilon - 1)) = 1
#guard firstSign (epsilon - epsilon) = 0
#guard secondSign (lift epsilon - delta) = 1
#guard secondSign (delta - lift (epsilon * epsilon)) = -1

end Hex.SignDet.Infinitesimal
