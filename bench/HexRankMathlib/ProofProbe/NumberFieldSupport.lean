/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import HexRankMathlib.NumberFieldTactic

open Hex
open scoped Hex.PolyQuot.QAdjoinField

namespace RankProbe

def p : ZPoly := DensePoly.ofList [-2, 0, 1]
def square : DyadicSquare := ⟨Dyadic.ofIntWithPrec 181 7, 0, 8⟩
def root : SimpleRoot p := SimpleRoot.ofSquare p square
instance : ZPoly.CheckedIrreducible p :=
  ⟨(ZPoly.isIrreducible_iff p).mpr (by irreducibility), by decide⟩
abbrev K := PolyQuot p root
def α : K := PolyQuot.Rank.generator p root

end RankProbe
