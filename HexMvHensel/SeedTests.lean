/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

import all HexMvHensel.Seed
public meta import HexMvHensel.Seed
public meta import HexMvPoly.Mono
public meta import HexMvPoly.Basic
public meta import HexMvPoly.Operations
public meta import HexMvPoly.Query
public meta import HexMvPoly.Recursive
public meta import HexMvPoly.Ring
public meta import HexBasic.ExtTreeMap

section

namespace Hex.MvHensel.SeedTests

open Hex
open Hex.MvPoly
open scoped Hex

#check lcIn_setLc
#check degreeOf_setLc
#check imageAt_setLc
#check prefixVars_min
#check prefixNonMain_min

abbrev P := MvPoly 2 Int Mono.lex
abbrev L := MvPoly 1 Int Mono.lex

def x : P := X 0
def y : P := X 1
def ly : L := X 0
def image : ZPoly := DensePoly.ofCoeffs #[2, 3]

#guard seed (cmp := Mono.lex) (0 : Fin 2) Mono.lex (ly + 1) image ==
  2 + (y + 1) * x

#guard setLc (cmp := Mono.lex) (0 : Fin 2) Mono.lex (ly + 1)
    (x ^ 2 + y * x + 1) == (y + 1) * x ^ 2 + y * x + 1

#guard prefixVars 1 ((ly + 1) * ly) == (ly + 1) * ly
#guard prefixVars 0 ((ly + 1) * ly) == 0

example :
    seedTuple? (cmp := Mono.lex) (0 : Fin 2) Mono.lex [image] [] = none := by
  rfl

example : Config.default.doublings = 6 := by
  rfl

end Hex.MvHensel.SeedTests
