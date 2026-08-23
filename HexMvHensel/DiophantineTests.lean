/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

import all HexMvHensel.Diophantine
public meta import HexMvHensel.Diophantine
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
import all HexModular.SymMod

section

/-!
Executable route checks for every depth of the multivariate recursion, plus
small kernel checks for its exact slicing and length-failure primitives.
-/

namespace Hex.MvHensel.DiophantineTests

open Hex
open Hex.MvPoly
open scoped Hex

def ux : ZPoly := DensePoly.ofCoeffs #[0, 1]
def uxPlusOne : ZPoly := DensePoly.ofCoeffs #[1, 1]
def images : List ZPoly := [ux, uxPlusOne]
def witness : List ZPoly := [1, -1]

/-! # No non-main variables -/

abbrev P0 := MvPoly 1 Int Mono.lex

def x0 : P0 := X 0
def d0 : Fin 0 → Nat := fun j => nomatch j

#guard diophantine 5 (0 : Fin 1) Mono.lex d0
    [x0 + 1, x0] images witness (1 : P0) ==
  some ([1, -1] : List P0)

/-! # One non-main variable -/

abbrev P1 := MvPoly 2 Int Mono.lex

def x1 : P1 := X 0
def y1 : P1 := X 1
def d1 : Fin 1 → Nat := fun _ => 1

/- `1*(x+1) + (-1+y)*x = 1 + y*x`. -/
#guard diophantine 5 (0 : Fin 2) Mono.lex d1
    [x1 + 1, x1] images witness (1 + y1 * x1) ==
  some ([1, -1 + y1] : List P1)

/-! # Multiple non-main variables -/

abbrev P2 := MvPoly 3 Int Mono.lex

def x2 : P2 := X 0
def y2 : P2 := X 1
def z2 : P2 := X 2
def d2 : Fin 2 → Nat := fun _ => 1

/- This exercises two nested correction loops, including the mixed `y*z`
coefficient. -/
#guard diophantine 5 (0 : Fin 3) Mono.lex d2
    [x2 + 1, x2] images witness
      (1 + y2 * x2 + z2 * (x2 + 1) + y2 * z2) ==
  some ([1 + z2 + y2 * z2, -1 + y2 - y2 * z2] : List P2)

/-! # Required failures -/

/- The image product has main degree two, so a nonzero `x^2` right-hand side
is outside the degree-bounded partial-fraction map. -/
#guard (diophantine 5 (0 : Fin 1) Mono.lex d0
    [x0 + 1, x0] images witness (x0 * x0)).isNone

/- A missing base is rejected rather than silently pairing only the common
tuple prefix. -/
#guard (diophantine 5 (0 : Fin 1) Mono.lex d0
    [x0 + 1] images witness (1 : P0)).isNone

/- The zero slice is valid, but the `y*x^3` term in the first base creates
the SPEC's load-bearing `hbdeg` trap at the next coefficient. -/
#guard (diophantine 5 (0 : Fin 2) Mono.lex d1
    [x1 + 1 + y1 * (x1 ^ 3), x1] images witness (1 : P1)).isNone

/-! # Kernel checks -/

example : tupleAdd? ([] : List P0) [0] = none := by
  rfl

example : sliceVar (1 : Fin 2) 1 (1 + y1 * x1) = x1 := by
  decide +kernel

example : embedPower (1 : Fin 2) 2 x1 = x1 * y1 ^ 2 := by
  decide +kernel

end Hex.MvHensel.DiophantineTests
