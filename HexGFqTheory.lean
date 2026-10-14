/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexGFqTheory.Basic
public import HexGFqTheory.GF2q
public import HexGFqTheory.Subfield
public import HexGFqTheory.Embeddings
public import HexGFqTheory.Primitivity

public section

/-!
Mathlib-side correspondence lemmas for the canonical finite-field convenience
constructors.

The executable `HexGFq` layer keeps `GFq` and optimized `GF2q` separate so the
representation choice stays explicit.  This module packages the existing
`HexGF2Theory` packed-to-generic ring equivalence as the public
equivalence between the optimized binary Conway field and the generic Conway
field.
-/
