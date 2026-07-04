/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexBerlekampZassenhaus.Basic
public import HexBerlekampZassenhaus.CrossCheck
public import HexBerlekampZassenhaus.SmallModSingleton

public section

/-!
The `HexBerlekampZassenhaus` library exposes the executable integer
Berlekamp-Zassenhaus factorization pipeline: normalization, good-prime
selection, Hensel-lift packaging, LLL-based recombination, bounded/default
factor entry points, and the integer irreducibility certificate checker.

The library root also imports `HexBerlekampZassenhaus.Conformance` for
Phase 3 core checks and `HexBerlekampZassenhaus.CrossCheck`, the
SPEC-sanctioned LLL-vs-exhaustive recombination cross-check.
-/
