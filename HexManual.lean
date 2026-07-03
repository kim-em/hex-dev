/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import VersoManual

-- Released libraries (dependency order).
import HexManual.Chapters.HexMatrix
import HexManual.Chapters.HexRowReduce
import HexManual.Chapters.HexDeterminant
import HexManual.Chapters.HexBareiss
import HexManual.Chapters.HexGramSchmidt
import HexManual.Chapters.HexLLL
-- Unreleased libraries (dependency order).
import HexManual.Chapters.HexArith
import HexManual.Chapters.HexModArith
import HexManual.Chapters.HexPoly
import HexManual.Chapters.HexPolyZ
import HexManual.Chapters.HexPolyFp
import HexManual.Chapters.HexGF2
import HexManual.Chapters.HexHensel
import HexManual.Chapters.HexGFqRing
import HexManual.Chapters.HexGFqField
import HexManual.Chapters.HexConway
import HexManual.Chapters.HexGFq
-- Tutorials (application-first capstone pages, see SPEC/tutorials.md).
import HexManual.Tutorials.Coppersmith

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

set_option pp.rawOnError true

/-!
The `HexManual` Verso aggregator. Each per-library reference chapter
lives at `HexManual/Chapters/<LibraryName>.lean` and is included
below. Chapters are ordered as a topological sort of the library
dependency DAG, released libraries first.
-/

#doc (Manual) "Hex" =>
%%%
authors := ["The hex project"]
shortTitle := "hex"
%%%

`hex` is executable, verified computer algebra for Lean 4: finite
fields, polynomial factorization, and lattice reduction. The
computational core is Mathlib-free; each chapter documents one library
and, where there is one, its correspondence with Mathlib.

{include 0 HexManual.Chapters.HexMatrix}

{include 0 HexManual.Chapters.HexRowReduce}

{include 0 HexManual.Chapters.HexDeterminant}

{include 0 HexManual.Chapters.HexBareiss}

{include 0 HexManual.Chapters.HexGramSchmidt}

{include 0 HexManual.Chapters.HexLLL}

{include 0 HexManual.Chapters.HexArith}

{include 0 HexManual.Chapters.HexModArith}

{include 0 HexManual.Chapters.HexPoly}

{include 0 HexManual.Chapters.HexPolyZ}

{include 0 HexManual.Chapters.HexPolyFp}

{include 0 HexManual.Chapters.HexGF2}

{include 0 HexManual.Chapters.HexHensel}

{include 0 HexManual.Chapters.HexGFqRing}

{include 0 HexManual.Chapters.HexGFqField}

{include 0 HexManual.Chapters.HexConway}

{include 0 HexManual.Chapters.HexGFq}

# Tutorials
%%%
tag := "tutorials"
%%%

The reference chapters above document each library on its own terms. The
tutorials here are application-first: each leads with a problem a reader
already cares about and shows the libraries carrying a recognizable
end-to-end workflow, with every code snippet checked as part of this
build.

{include 1 HexManual.Tutorials.Coppersmith}

