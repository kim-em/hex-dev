/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

import all HexMvHensel.Lift
public meta import HexMvHensel.Lift
public meta import HexMvHensel.Shift
public meta import HexMvPoly.Mono
public meta import HexMvPoly.Basic
public meta import HexMvPoly.Operations
public meta import HexMvPoly.Query
public meta import HexMvPoly.Recursive
public meta import HexMvPoly.Ring
public meta import HexBasic.ExtTreeMap

section

namespace Hex.MvHensel.CertTests

open Hex
open Hex.MvPoly
open scoped Hex

def prime5 : ZMod64.Prime where
  m := 5
  bounds := { pPos := by omega, pLtR := by decide }
  prime := Hex.Nat.isPrimeTrial_isPrime (by decide)

def point0 : Fin 0 → Int := fun j => nomatch j

abbrev P0 := MvPoly 1 Int Mono.lex
abbrev L0 := MvPoly 0 Int Mono.lex

def x0 : P0 := X 0
def ux : ZPoly := DensePoly.ofCoeffs #[0, 1]
def uxPlusOne : ZPoly := DensePoly.ofCoeffs #[1, 1]
def twoX : ZPoly := DensePoly.ofCoeffs #[0, 2]

def setup0 : Setup 0 :=
  { main := 0, point := point0, prime := prime5, exponent := 1 }

def good : Input 0 Mono.lex Mono.lex :=
  { setup := setup0
    target := x0
    images := [ux]
    leading := [(1 : L0)]
    witness := [1] }

#guard valid good

def arityInput : Input 0 Mono.lex Mono.lex :=
  { good with leading := [] }

#guard failure? arityInput == some .arity

def imageProductInput : Input 0 Mono.lex Mono.lex :=
  { good with images := [uxPlusOne] }

#guard failure? imageProductInput == some .imageProduct

def leadingProductInput : Input 0 Mono.lex Mono.lex :=
  { good with leading := [(2 : L0)] }

#guard failure? leadingProductInput == some .leadingProduct

def leadingImageInput : Input 0 Mono.lex Mono.lex :=
  { setup := setup0
    target := (2 : P0) * x0 ^ 2
    images := [twoX, ux]
    leading := [(1 : L0), (2 : L0)]
    witness := [0, 0] }

#guard failure? leadingImageInput == some (.leadingImage 0)

def primeDividesInput : Input 0 Mono.lex Mono.lex :=
  { setup := setup0
    target := (5 : P0) * x0
    images := [DensePoly.ofCoeffs #[0, 5]]
    leading := [(5 : L0)]
    witness := [1] }

#guard failure? primeDividesInput == some (.primeDividesLc 0)

def notCoprimeInput : Input 0 Mono.lex Mono.lex :=
  { setup := setup0
    target := x0 ^ 2
    images := [ux, ux]
    leading := [(1 : L0), (1 : L0)]
    witness := [0, 0] }

#guard failure? notCoprimeInput == some .notCoprime

def unreducedWitness : ZPoly :=
  DensePoly.ofCoeffs #[1, 5]

def witnessDegreeInput : Input 0 Mono.lex Mono.lex :=
  { setup := setup0
    target := x0 * (x0 + 1)
    images := [ux, uxPlusOne]
    leading := [(1 : L0), (1 : L0)]
    witness := [unreducedWitness, -1] }

#guard failure? witnessDegreeInput == some (.witnessDegree 0)

/- Degree drop needs a genuine second variable: `y*x + 1` becomes the
constant `1` at `y = 0`. -/
abbrev P1 := MvPoly 2 Int Mono.lex
abbrev L1 := MvPoly 1 Int Mono.lex

def x1 : P1 := X 0
def y1 : P1 := X 1
def ly : L1 := X 0
def pointZero : Fin 1 → Int := fun _ => 0

def degreeDropInput : Input 1 Mono.lex Mono.lex :=
  { setup :=
      { main := 0, point := pointZero, prime := prime5, exponent := 1 }
    target := y1 * x1 + 1
    images := [ux]
    leading := [ly]
    witness := [1] }

#guard failure? degreeDropInput == some .degreeDrop

/- The public route preserves every validation diagnostic rather than
collapsing malformed inputs to one generic failure. -/
def reported0 (inp : Input 0 Mono.lex Mono.lex) : Option Failure :=
  match lift inp with
  | .error failure => some failure
  | .ok _ => none

def reported1 (inp : Input 1 Mono.lex Mono.lex) : Option Failure :=
  match lift inp with
  | .error failure => some failure
  | .ok _ => none

#guard reported0 arityInput == some .arity
#guard reported0 imageProductInput == some .imageProduct
#guard reported0 leadingProductInput == some .leadingProduct
#guard reported0 leadingImageInput == some (.leadingImage 0)
#guard reported0 primeDividesInput == some (.primeDividesLc 0)
#guard reported0 notCoprimeInput == some .notCoprime
#guard reported0 witnessDegreeInput == some (.witnessDegree 0)
#guard reported1 degreeDropInput == some .degreeDrop

def goodCert : Cert 0 Mono.lex := { factors := [x0] }

#guard check good goodCert

example : check good { factors := [] } = false := by
  decide +kernel

end Hex.MvHensel.CertTests
