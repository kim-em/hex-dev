/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexResultantTheory.Basic
public import HexResultantTheory.PseudoDivMod
public import HexResultantTheory.Chain
public import HexResultantTheory.Sylvester
public import HexResultantTheory.Specialize
public import HexResultantTheory.Roots
public import HexResultantTheory.Discriminant

public section

/-!
The `HexResultantTheory` library connects executable Brown subresultants,
resultants, and discriminants to Mathlib polynomials. It also exposes
bivariate specialization and root-product APIs used by the number-field
companions.
-/
