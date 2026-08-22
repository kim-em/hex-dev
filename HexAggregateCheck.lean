/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexBasic
public import HexArith
public import HexPoly
public import HexMvPoly
public import HexModArith
public import HexPolyMathlib
public import HexMvPolyMathlib
public import HexPolyFp
public import HexPolyZ
public import HexModArithMathlib
public import HexPolyFpMathlib
public import HexGFqRing
public import HexHensel
public import HexPolyZMathlib
public import HexHenselMathlib
public import HexRoots
public import HexRealRoots
public import HexRootsMathlib
public import HexRealRootsMathlib
public import HexMatrix
public import HexRowReduce
public import HexBerlekamp
public import HexConway
public import HexGFqField
public import HexGF2
public import HexGF2Mathlib
public import HexGFq
public import HexGFqMathlib
public import HexDeterminant
public import HexBareiss
public import HexCharPoly
public import HexMatrixMathlib
public import HexRowReduceMathlib
public import HexDeterminantMathlib
public import HexCharPolyMathlib
public import HexBareissMathlib
public import HexBerlekampMathlib
public import HexGramSchmidt
public import HexGramSchmidtMathlib
public import HexLLL
public import HexBerlekampZassenhaus
public import HexLLLMathlib
public import HexBerlekampZassenhausMathlib

/-!
Mirror of the released aggregate's umbrella.

`leanprover/hex` is a module-system umbrella that `public import`s every
released library. A module may not import a non-module module, so a library
that never adopted the module system breaks the aggregate's build -- and
nothing else does, because every consumer inside this monorepo either is that
library or reaches it through a non-module conformance or bench driver, both of
which may import anything.

This module reproduces that constraint here, where it is cheap to check: it
imports the same umbrellas the aggregate does, in the same order, so a
non-module library fails `lake build` in this repository rather than after the
publish-out sync has already pushed it.

The import list is the `pins:` of the `leanprover/hex` entry in
`scripts/release/released.yml`, mapped through each entry's `lib:`.
`scripts/release/check_released_manifest.py` compares the two and fails when
they drift, so publishing a new library updates this file rather than silently
skipping it.
-/
