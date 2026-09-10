/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexDeterminantalIdeal.Choose
public import HexDeterminantalIdeal.Minors
public import HexDeterminantalIdeal.Rank
public import HexDeterminantalIdeal.MvPoly

public section

/-!
The `HexDeterminantalIdeal` library: executable minors and determinantal-ideal
generators of a matrix over a commutative ring (`Minors`), the theorem that a
matrix over a field has rank below `r` exactly when every `r × r` minor
vanishes (`Rank`), and the specialisation of a polynomial matrix at a point
with its rank-drop locus (`MvPoly`).
-/
