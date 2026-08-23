/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

import all HexMvHensel.Complete
public meta import HexMvHensel.Complete
public meta import HexBasic.ExtTreeMap
import all HexMvPoly.Mono
import all HexMvPoly.Basic
import all HexMvPoly.Operations
import all HexMvPoly.Query
import all HexMvPoly.Structural
import all HexMvPoly.Ring
import all HexPoly.Dense
import all HexModArith.Prime

section

namespace Hex.MvHensel.CompleteTests

open Hex
open Hex.MvPoly
open scoped Hex

def prime5 : ZMod64.Prime where
  m := 5
  bounds := { pPos := by omega, pLtR := by decide }
  prime := Hex.Nat.isPrimeTrial_isPrime (by decide)

abbrev P := MvPoly 2 Int Mono.lex
abbrev L := MvPoly 1 Int Mono.lex

def x : P := X 0
def y : P := X 1
def pointZero : Fin 1 → Int := fun _ => 0
def pointTen : Fin 1 → Int := fun _ => 10

def dummyInput (point : Fin 1 → Int) (target : P) :
    Input 1 Mono.lex Mono.lex :=
  { setup := { main := 0, point := point, prime := prime5, exponent := 1 }
    target := target
    images := []
    leading := []
    witness := [] }

/- The first side-variable weight contains the main-variable radix. -/
#guard kroneckerWeight 1 (fun _ : Fin 1 => 2) 0 == 2
#guard kroneckerWeight 1 (fun j : Fin 2 => if j.val = 0 then 2 else 3) 1 == 6

/- The upper corner of the full degree box maps to one below its radix size. -/
#guard kroneckerExponent 0 2
    (fun j : Fin 2 => if j.val = 0 then 1 else 2) #v[2, 1, 2] == 17

def noDegrees : Fin 0 → Nat := fun j => nomatch j

/- With no side variables, the weight table is empty and the main exponent is
unchanged. -/
#guard kroneckerWeights 4 noDegrees == [1]
#guard kroneckerExponent 0 4 noDegrees #v[4] == 4

example (a b : Mono 1) (ha : Mono.degreeOf 0 a ≤ 4)
    (hb : Mono.degreeOf 0 b ≤ 4)
    (h : kroneckerExponent 0 4 noDegrees a =
      kroneckerExponent 0 4 noDegrees b) : a = b :=
  kroneckerExponent_inj 0 4 noDegrees
    ⟨ha, fun j => nomatch j⟩ ⟨hb, fun j => nomatch j⟩ h

/- Hence `x` and the first side variable receive distinct exponents. -/
#guard kroneckerExponent 0 1 (fun _ : Fin 1 => 1) #v[1, 0] == 1
#guard kroneckerExponent 0 1 (fun _ : Fin 1 => 1) #v[0, 1] == 2

/- For `x + y`, the Kronecker image is `z + z^2`, its norm bound is two,
and the central binomial factor is two. -/
def linearInput : Input 1 Mono.lex Mono.lex :=
  dummyInput pointZero (x + y)

#guard coeffBound linearInput == 4

/- Bounds are computed after shifting.  At `y = 10`, the target below has
the amplified coefficients `20` and `100`; the executable bound must see
them, rather than reuse the much smaller origin bound. -/
def amplifiedTarget : P := (x + y ^ 2) * (x + 1)
def originInput : Input 1 Mono.lex Mono.lex :=
  dummyInput pointZero amplifiedTarget
def shiftedInput : Input 1 Mono.lex Mono.lex :=
  dummyInput pointTen amplifiedTarget

#guard coeffBound originInput == 70
#guard coeffBound shiftedInput == 5075
#guard coeffBound originInput < coeffBound shiftedInput

/- The exact norm computation remains sparse and includes every stored
coefficient once. -/
#guard mvCoeffNormSq (x + 3 * y + 4) == 26

end Hex.MvHensel.CompleteTests
