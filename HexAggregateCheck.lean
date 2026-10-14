/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexBasic
public import HexArith
public import HexPrimality
public import HexECPP
public import HexPrimalityTheory
public import HexECPPTheory
public import HexPoly
public import HexMvPoly
public import HexModArith
public import HexSparsePoly
public import HexPolyTheory
public import HexSparsePolyTheory
public import HexMvPolyTheory
public import HexPolyFp
public import HexPolyZ
public import HexModArithTheory
public import HexPolyFpTheory
public import HexGFqRing
public import HexHensel
public import HexPolyZTheory
public import HexHenselTheory
public import HexRoots
public import HexRealRoots
public import HexRootsTheory
public import HexRealRootsTheory
public import HexMatrix
public import HexRowReduce
public import HexBerlekamp
public import HexConway
public import HexGFqField
public import HexGF2
public import HexGF2Theory
public import HexGFq
public import HexGFqTheory
public import HexDeterminant
public import HexBareiss
public import HexMatrixTheory
public import HexRowReduceTheory
public import HexDeterminantTheory
public import HexBareissTheory
public import HexBerlekampTheory
public import HexGramSchmidt
public import HexGramSchmidtTheory
public import HexLLL
public import HexBerlekampZassenhaus
public import HexLLLTheory
public import HexBerlekampZassenhausTheory
public import HexPermGroup
public import HexPermGroupTheory
public import HexGraphIso
public import HexGraphIsoTheory
public import HexResultant
public import HexResultantTheory
public import HexNumberField
public import HexNumberFieldTheory
public import HexNumberFieldTower
public import HexNumberFieldTowerTheory
public import HexRCF
public import HexTruncatedSeries
public import HexTruncatedSeriesTheory
public import HexModular
public import HexPolyFast

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
