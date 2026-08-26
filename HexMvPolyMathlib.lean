/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexMvPolyMathlib.Aeval
public import HexMvPolyMathlib.Correspondence
public import HexMvPolyMathlib.Equiv
public import HexMvPolyMathlib.Recursive

public section

/-!
The Mathlib correspondence layer for `Hex.MvPoly`.

It provides exact representation, recursive-view, and algebra equivalences,
algebra-hom evaluation, and correspondence lemmas for the executable semantic
operations.
-/
