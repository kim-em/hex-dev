/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexPolyZ.Core
public import HexPolyZ.Rational
public import HexPolyZ.Decomposition
public import HexPolyZ.Mignotte

public section

/-!
The `HexPolyZ` library specializes the generic dense polynomial library to
integer coefficients, exposing the `ZPoly` alias together with congruence,
content, primitive-part, and conservative executable Mignotte-bound APIs used
by the factoring pipeline.
-/
