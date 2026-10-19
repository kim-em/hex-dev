/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexHenselTheory.CoprimeLift
public import HexHenselTheory.HenselLemmas

public section

/-!
The `HexHenselTheory` library transfers the executable `HexHensel` surface to
Mathlib's `Polynomial ℤ` API.

It provides coprimality-lifting results together with Hensel correctness and
uniqueness theorems used by integer-factorization proofs.
-/
