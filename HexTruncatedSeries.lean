/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexTruncatedSeries.Defs
public import HexTruncatedSeries.Ring
public import HexTruncatedSeries.Classes
public import HexTruncatedSeries.Precision
public import HexTruncatedSeries.Newton
public import HexTruncatedSeries.Inverse
public import HexTruncatedSeries.Sqrt
public import HexTruncatedSeries.ExpLog
public import HexTruncatedSeries.Comp
public import HexTruncatedSeries.Revert
public import HexTruncatedSeries.ModuleBoundaryTests

public section

/-!
Fixed-precision truncated power series over a lightweight commutative ring.

The umbrella exposes the coefficient-vector representation, executable
truncated commutative-ring operations, precision changes, and the localized
algebraic capability classes used by higher series algorithms.
-/
