/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module
public import HexRankMathlib.NumberFieldTactic

public section

open Hex
open scoped Hex.PolyQuot.QAdjoinField

namespace RankProbe

@[expose] def p : ZPoly := DensePoly.ofList [-2, 0, 1]
@[expose] def square : DyadicSquare := ⟨Dyadic.ofIntWithPrec 181 7, 0, 8⟩
@[expose] def root : SimpleRoot p := SimpleRoot.ofSquare p square
instance : ZPoly.CheckedIrreducible p :=
  ⟨(ZPoly.isIrreducible_iff p).mpr (by irreducibility), by decide⟩
abbrev K := PolyQuot p root
@[expose] def α : K := PolyQuot.Rank.generator p root

end RankProbe
