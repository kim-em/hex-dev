/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexPoly.Dense
public import HexPoly.Euclid
public import HexPoly.Operations

public section

/-! Dense polynomial support for the Hex project. The library exposes the normalized
array-backed representation together with basic constructors, structural queries, arithmetic,
Euclidean-algorithm helpers, and CRT/content operations. -/
