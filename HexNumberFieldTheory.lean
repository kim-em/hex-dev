/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexNumberFieldTheory.Roots
public import HexNumberFieldTheory.ComponentRoots
public import HexNumberFieldTheory.AlgebraicRoots
public import HexNumberFieldTheory.Field
public import HexNumberFieldTheory.IntegerRoots
public import HexNumberFieldTheory.Nearest
public import HexNumberFieldTheory.CommonField
public import HexNumberFieldTheory.Order
public import HexNumberFieldTheory.Conjugate
public import HexNumberFieldTheory.AlgebraicallyClosed
public import HexNumberFieldTheory.Radical
public import HexNumberFieldTheory.RootOrder

public import HexNumberFieldTheory.RealSign

public section

/-!
The `HexNumberFieldTheory` library interprets the executable number-field
types in Mathlib and states the semantic contracts for exactification, lazy
arithmetic, and algebraic root finding.
-/
