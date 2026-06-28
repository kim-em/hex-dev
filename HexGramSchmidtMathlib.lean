/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexGramSchmidtMathlib.Basic
public import HexGramSchmidtMathlib.Int
public import HexGramSchmidtMathlib.Update

public section

/-!
The `HexGramSchmidtMathlib` library states the rowwise correspondence between
the executable dense-matrix Gram-Schmidt surface and Mathlib's `gramSchmidt`,
together with the Cramer/Bareiss equality for the integral scaled
coefficient matrix.
-/
