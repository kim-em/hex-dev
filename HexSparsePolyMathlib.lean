/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexSparsePolyMathlib.Equiv

public section

/-!
The Mathlib correspondence layer for `Hex.SparsePoly`.

It identifies the executable canonical sparse representation with
Mathlib's `Polynomial R` through the ring equivalences `denseEquiv` and
`equiv`, and provides one correspondence lemma per public core
operation.
-/
