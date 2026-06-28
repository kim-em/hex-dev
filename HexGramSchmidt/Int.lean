/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexGramSchmidt.Int.Core
public import HexGramSchmidt.Int.Scaled
public import HexGramSchmidt.Int.Canonical
public import HexGramSchmidt.Int.Invariant
public import HexGramSchmidt.Int.Correspondence
public import HexGramSchmidt.Int.Combination

public section

/-!
Executable Gram-determinant and scaled-coefficient surface for
`hex-gram-schmidt`, split by subject across `HexGramSchmidt/Int/*`: array/loop
machinery (`Core`), the scaled-coefficient and Gram-determinant surface
(`Scaled`), the canonical-coefficient predicate (`Canonical`), its Bareiss
row-invariant proofs (`Invariant`), the scaledCoeffRows correspondence
(`Correspondence`), and the integer row-combination support (`Combination`).
This module re-exports them.
-/
