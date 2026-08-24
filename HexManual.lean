/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import VersoManual

-- Released libraries (dependency order).
import HexManual.Chapters.HexBasic
import HexManual.Chapters.HexArith
import HexManual.Chapters.HexPoly
import HexManual.Chapters.HexMvPoly
import HexManual.Chapters.HexModArith
import HexManual.Chapters.HexPolyFp
import HexManual.Chapters.HexPolyZ
import HexManual.Chapters.HexGFqRing
import HexManual.Chapters.HexHensel
import HexManual.Chapters.HexRoots
import HexManual.Chapters.HexRealRoots
import HexManual.Chapters.HexMatrix
import HexManual.Chapters.HexRowReduce
import HexManual.Chapters.HexBerlekamp
import HexManual.Chapters.HexGF2
import HexManual.Chapters.HexGFqField
import HexManual.Chapters.HexConway
import HexManual.Chapters.HexGFq
import HexManual.Chapters.HexDeterminant
import HexManual.Chapters.HexBareiss
import HexManual.Chapters.HexCharPoly
import HexManual.Chapters.HexGramSchmidt
import HexManual.Chapters.HexLLL
import HexManual.Chapters.HexBerlekampZassenhaus
import HexManual.Chapters.FactorTactics
-- Unreleased libraries (dependency order).
import HexManual.Chapters.HexPrimality
import HexManual.Chapters.HexModular
import HexManual.Chapters.HexResultant
import HexManual.Chapters.HexPolyZGcd
import HexManual.Chapters.HexMvGcd
import HexManual.Chapters.HexMvHensel
import HexManual.Chapters.HexMvFactor
import HexManual.Chapters.HexSparsePoly
import HexManual.Chapters.HexRCF
import HexManual.Chapters.HexNumberField
import HexManual.Chapters.HexNumberFieldTower
import HexManual.Chapters.HexMinPoly
-- Tutorials (application-first capstone pages, see SPEC/tutorials.md).
import HexManual.Tutorials.AESField
import HexManual.Tutorials.AESModulus
import HexManual.Tutorials.PrimeSplitting
import HexManual.Tutorials.Coppersmith

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

set_option pp.rawOnError true

/-!
The `HexManual` Verso aggregator. Each per-library reference chapter
lives at `HexManual/Chapters/<LibraryName>.lean` and is included
below. Chapters are ordered as a topological sort of the library
dependency DAG, released libraries first.

Which chapters count as released is not a judgement call: it follows
`scripts/release/released.yml`, and `scripts/release/check_manual_split.py`
fails CI when a chapter sits on the wrong side of the split.
-/

#doc (Manual) "Hex" =>
%%%
authors := ["The hex project"]
shortTitle := "hex"
%%%

`hex` is executable computer algebra for Lean 4: finite and number fields,
polynomial factorization, root isolation, and lattice reduction. The
computational core is Mathlib-free; Mathlib companions state correspondence
contracts and, for mature libraries, supply their proofs.

{include 0 HexManual.Chapters.HexBasic}

{include 0 HexManual.Chapters.HexArith}

{include 0 HexManual.Chapters.HexPoly}

{include 0 HexManual.Chapters.HexMvPoly}

{include 0 HexManual.Chapters.HexSparsePoly}

{include 0 HexManual.Chapters.HexModArith}

{include 0 HexManual.Chapters.HexPolyFp}

{include 0 HexManual.Chapters.HexPolyZ}

{include 0 HexManual.Chapters.HexGFqRing}

{include 0 HexManual.Chapters.HexHensel}

{include 0 HexManual.Chapters.HexRoots}

{include 0 HexManual.Chapters.HexRealRoots}

{include 0 HexManual.Chapters.HexMatrix}

{include 0 HexManual.Chapters.HexRowReduce}

{include 0 HexManual.Chapters.HexBerlekamp}

{include 0 HexManual.Chapters.HexGF2}

{include 0 HexManual.Chapters.HexGFqField}

{include 0 HexManual.Chapters.HexConway}

{include 0 HexManual.Chapters.HexGFq}

{include 0 HexManual.Chapters.HexDeterminant}

{include 0 HexManual.Chapters.HexBareiss}

{include 0 HexManual.Chapters.HexGramSchmidt}

{include 0 HexManual.Chapters.HexLLL}

{include 0 HexManual.Chapters.HexBerlekampZassenhaus}

{include 0 HexManual.Chapters.FactorTactics}

# Tutorials
%%%
tag := "tutorials"
%%%

The reference chapters above document each library on its own terms. The
tutorials here are application-first: each leads with a problem a reader
already cares about and shows the libraries carrying a recognizable
end-to-end workflow, with every code snippet checked as part of this
build.

{include 2 HexManual.Tutorials.AESField}

{include 2 HexManual.Tutorials.AESModulus}

{include 2 HexManual.Tutorials.PrimeSplitting}

{include 2 HexManual.Tutorials.Coppersmith}

# Draft sections for unreleased libraries
%%%
tag := "unreleased"
%%%

These libraries are still incubating in the
[`hex-dev`](https://github.com/kim-em/hex-dev) monorepo and have not been
split out for release yet, so their APIs may still change. They are grouped
here to keep the reference chapters above focused on the released libraries.

{include 2 HexManual.Chapters.HexPrimality}

{include 2 HexManual.Chapters.HexModular}

{include 2 HexManual.Chapters.HexCharPoly}

{include 2 HexManual.Chapters.HexResultant}

{include 2 HexManual.Chapters.HexPolyZGcd}

{include 2 HexManual.Chapters.HexMvGcd}

{include 2 HexManual.Chapters.HexMvHensel}

{include 2 HexManual.Chapters.HexMvFactor}

{include 2 HexManual.Chapters.HexRCF}

{include 2 HexManual.Chapters.HexNumberField}

{include 2 HexManual.Chapters.HexNumberFieldTower}

{include 2 HexManual.Chapters.HexMinPoly}
