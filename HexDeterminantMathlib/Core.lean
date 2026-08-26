/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexDeterminantMathlib.CoreTransport
public import HexDeterminantMathlib.CorePlucker

public section

/-!
Mathlib-side determinant bridge for `hex-matrix-mathlib`, split by subject:
the permutation-sign bridge and ordered `nMatrix`/four-row transport helpers
(`CoreTransport`), and the four-row / double-row Plücker and Desnanot-Jacobi
assembly (`CorePlucker`). This module re-exports both.
-/
