/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexSignDet
public import HexRationalFn
public meta import HexRationalFn

public section

/-! Test coefficient providers for exact infinitesimal conformance. The outer
indeterminate is positive and smaller than every positive base-field element.
These use the existing rational-function field operations, with an explicit
sign callback. They do not register ordered-function or real-closure providers. -/
namespace Hex.SignDet.Infinitesimal

/-- The first nonzero coefficient determines a polynomial's sign at a positive
infinitesimal. The base callback is itself exact, including at nested levels. -/
def lowestSign {K : Type} [Zero K] [DecidableEq K]
    (sign : K → Int) (p : DensePoly K) : Int :=
  match p.toArray.toList.find? (fun c => c != 0) with
  | none => 0
  | some c => sign c

/-- A fraction's sign is the product of its numerator and denominator signs. -/
def sign {K : Type} [Lean.Grind.Field K] [DecidableEq K]
    (baseSign : K → Int) (f : RationalFn K) : Int :=
  lowestSign baseSign f.num * lowestSign baseSign f.den

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
