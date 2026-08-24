/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

import all HexMvHensel.Lift
public meta import HexMvHensel.Lift
public meta import HexMvHensel.Shift
public meta import HexBasic.ExtTreeMap
import all HexMvPoly.Mono
import all HexMvPoly.Basic
import all HexMvPoly.Operations
import all HexMvPoly.Query
import all HexMvPoly.Recursive
import all HexMvPoly.Ring
import all HexPoly.Dense
import all HexPoly.Operations
import all HexPoly.Euclid.DivGcd
import all HexPoly.Euclid.MulRing
import all HexPolyFp.Field
import all HexModArith.Residue
import all HexModArith.Ring
import all HexModArith.Prime
import all HexArith.ExtGcd
import all HexModular.SymMod

section

namespace Hex.MvHensel.LiftTests

open Hex
open Hex.MvPoly
open scoped Hex

#check applyCorrections_frame
#check seedTuple_stage
#check liftStage_spec
#check liftShifted_some

def prime5 : ZMod64.Prime where
  m := 5
  bounds := { pPos := by omega, pLtR := by decide }
  prime := Hex.Nat.isPrimeTrial_isPrime (by decide)

abbrev P := MvPoly 2 Int Mono.lex
abbrev L := MvPoly 1 Int Mono.lex

def x : P := X 0
def y : P := X 1
def uxPlusTwo : ZPoly := DensePoly.ofCoeffs #[2, 1]
def uxPlusOne : ZPoly := DensePoly.ofCoeffs #[1, 1]
def ux : ZPoly := DensePoly.ofCoeffs #[0, 1]

def pointTwo : Fin 1 → Int := fun _ => 2
def pointZero : Fin 1 → Int := fun _ => 0

/- Multivariate complements use the same linear prefix/suffix construction. -/
#guard mvComplements [x] == [1]
#guard mvComplements [x, y, x + y] ==
  [y * (x + y), x * (x + y), x * y]

/- A nonzero evaluation point exercises both coordinate transforms. -/
def successInput : Input 1 Mono.lex Mono.lex :=
  { setup :=
      { main := 0, point := pointTwo, prime := prime5, exponent := 1 }
    target := (x + y) * (x + 1)
    images := [uxPlusTwo, uxPlusOne]
    leading := [(1 : L), (1 : L)]
    witness := [-1, 1] }

def successCert : Cert 1 Mono.lex :=
  { factors := [x + y, x + 1] }

#guard valid successInput
def successWorks : Bool :=
  match lift successInput with
  | .ok cert => cert.factors == successCert.factors
  | .error _ => false

#guard successWorks
#guard check successInput successCert

/- The next route requires the stage to install a nonconstant prescribed
leading coefficient before solving the lower-degree correction. -/
def leadingInput : Input 1 Mono.lex Mono.lex :=
  { setup :=
      { main := 0, point := pointZero, prime := prime5, exponent := 1 }
    target := ((y + 1) * x + y) * (x + 1)
    images := [ux, uxPlusOne]
    leading := [(X 0 + 1 : L), (1 : L)]
    witness := [1, -1] }

def leadingWorks : Bool :=
  match lift leadingInput with
  | .ok cert => cert.factors == [((y + 1) * x + y), x + 1]
  | .error _ => false

#guard leadingWorks

/- Two non-main variables exercise the outer stage fold as well as the
recursive diophantine solver used inside each stage. -/
abbrev P2 := MvPoly 3 Int Mono.lex
abbrev L2 := MvPoly 2 Int Mono.lex

def x2 : P2 := X 0
def y2 : P2 := X 1
def z2 : P2 := X 2
def pointZero2 : Fin 2 → Int := fun _ => 0

def twoStageInput : Input 2 Mono.lex Mono.lex :=
  { setup :=
      { main := 0, point := pointZero2, prime := prime5, exponent := 1 }
    target := (x2 + y2 + z2) * (x2 + 1)
    images := [ux, uxPlusOne]
    leading := [(1 : L2), (1 : L2)]
    witness := [1, -1] }

def twoStagesWork : Bool :=
  match lift twoStageInput with
  | .ok cert => cert.factors == [x2 + y2 + z2, x2 + 1]
  | .error _ => false

#guard twoStagesWork

/- The point `y = -1` splits `x^2+y` into `x-1` and `x+1`, although no
compatible integer factorization exists.  Full box precision therefore ends
in the distinct reconstruction failure. -/
def pointNegOne : Fin 1 → Int := fun _ => -1
def uxMinusOne : ZPoly := DensePoly.ofCoeffs #[-1, 1]

def reconstructInput : Input 1 Mono.lex Mono.lex :=
  { setup :=
      { main := 0, point := pointNegOne, prime := prime5, exponent := 1 }
    target := x ^ 2 + y
    images := [uxMinusOne, uxPlusOne]
    leading := [(1 : L), (1 : L)]
    witness := [DensePoly.C (-2), DensePoly.C 2] }

#guard valid reconstructInput
def reconstructionFails : Bool :=
  match lift reconstructInput with
  | .error (.reconstruct 5) => true
  | _ => false

#guard reconstructionFails

/- A coefficient `3` is reconstructed as `-2` modulo five, but correctly
after one exponent doubling to modulus twenty-five. -/
def retryInput : Input 1 Mono.lex Mono.lex :=
  { setup :=
      { main := 0, point := pointZero, prime := prime5, exponent := 1 }
    target := (x + 3 * y) * (x + 1)
    images := [ux, uxPlusOne]
    leading := [(1 : L), (1 : L)]
    witness := [1, -1] }

def retryCert : Cert 1 Mono.lex :=
  { factors := [x + 3 * y, x + 1] }

def firstRetryFails : Bool :=
  match lift retryInput with
  | .error (.reconstruct 5) => true
  | _ => false

def retryWorks : Bool :=
  match liftWith { doublings := 1 } retryInput with
  | .ok cert => cert.factors == retryCert.factors
  | .error _ => false

#guard firstRetryFails
#guard retryWorks

def exponentDoubles : Bool :=
  (raiseExponent? retryInput).map (fun inp => inp.setup.exponent) == some 2

#guard exponentDoubles

end Hex.MvHensel.LiftTests
