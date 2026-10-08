/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import VersoManual

-- Library reference chapters; the released split and inclusion order are below.
public import HexManual.Chapters.HexBasic
public import HexManual.Chapters.HexArith
public import HexManual.Chapters.HexPrimality
public import HexManual.Chapters.HexECPP
public import HexManual.Chapters.HexPoly
public import HexManual.Chapters.HexMvPoly
public import HexManual.Chapters.HexModArith
public import HexManual.Chapters.HexPolyFp
public import HexManual.Chapters.HexPolyZ
public import HexManual.Chapters.HexGFqRing
public import HexManual.Chapters.HexHensel
public import HexManual.Chapters.HexRoots
public import HexManual.Chapters.HexRealRoots
public import HexManual.Chapters.HexMatrix
public import HexManual.Chapters.HexRowReduce
public import HexManual.Chapters.HexBerlekamp
public import HexManual.Chapters.HexGF2
public import HexManual.Chapters.HexGFqField
public import HexManual.Chapters.HexConway
public import HexManual.Chapters.HexGFq
public import HexManual.Chapters.HexDeterminant
public import HexManual.Chapters.HexBareiss
public import HexManual.Chapters.HexCharPoly
public import HexManual.Chapters.HexGramSchmidt
public import HexManual.Chapters.HexLLL
public import HexManual.Chapters.HexBerlekampZassenhaus
public import HexManual.Chapters.FactorTactics
public import HexManual.Chapters.HexRCF
public import HexManual.Chapters.HexResultant
public import HexManual.Chapters.HexNumberField
public import HexManual.Chapters.HexNumberFieldTower
public import HexManual.Chapters.HexRealAlgebraic
public import HexManual.Chapters.HexTruncatedSeries
public import HexManual.Chapters.HexReflect
public import HexManual.Chapters.HexRealFormula
public import HexManual.Chapters.HexPolyFast
public import HexManual.Chapters.HexRationalFn
public import HexManual.Chapters.HexOrderedFn
public import HexManual.Chapters.HexSturm
public import HexManual.Chapters.HexSignDet
public import HexManual.Chapters.HexRealClosure
public import HexManual.Chapters.HexLatticeEnum
public import HexManual.Chapters.HexIntFactor
public import HexManual.Chapters.HexModular
public import HexManual.Chapters.HexPolyZGcd
public import HexManual.Chapters.HexMvGcd
public import HexManual.Chapters.HexMvHensel
public import HexManual.Chapters.HexMvFactor
public import HexManual.Chapters.HexPolySmith
public import HexManual.Chapters.HexSmith
public import HexManual.Chapters.HexSparsePoly
public import HexManual.Chapters.HexMinPoly
public import HexManual.Chapters.HexPermGroup
public import HexManual.Chapters.HexGraphIso
public import HexManual.Chapters.NautyAlgorithm
-- Tutorials (application-first capstone pages, see SPEC/tutorials.md).
public import HexManual.Tutorials.AESField
public import HexManual.Tutorials.AESModulus
public import HexManual.Tutorials.PrimeSplitting
public import HexManual.Tutorials.Coppersmith
public import HexManual.Tutorials.FieldPrimes
public import HexManual.Tutorials.RubiksCube

public section

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

{include 0 HexManual.Chapters.HexTruncatedSeries}

{include 0 HexManual.Chapters.HexArith}

{include 0 HexManual.Chapters.HexModular}

{include 0 HexManual.Chapters.HexPrimality}
{include 0 HexManual.Chapters.HexECPP}

{include 0 HexManual.Chapters.HexPoly}

{include 0 HexManual.Chapters.HexPolyFast}

{include 0 HexManual.Chapters.HexMvPoly}

{include 0 HexManual.Chapters.HexSparsePoly}

{include 0 HexManual.Chapters.HexModArith}

{include 0 HexManual.Chapters.HexPolyFp}

{include 0 HexManual.Chapters.HexPolyZ}

{include 0 HexManual.Chapters.HexGFqRing}

{include 0 HexManual.Chapters.HexHensel}

{include 0 HexManual.Chapters.HexRoots}

{include 0 HexManual.Chapters.HexRealRoots}

{include 0 HexManual.Chapters.HexRCF}

{include 0 HexManual.Chapters.HexMatrix}

{include 0 HexManual.Chapters.HexRowReduce}

{include 0 HexManual.Chapters.HexBerlekamp}

{include 0 HexManual.Chapters.HexGF2}

{include 0 HexManual.Chapters.HexGFqField}

{include 0 HexManual.Chapters.HexConway}

{include 0 HexManual.Chapters.HexGFq}

{include 0 HexManual.Chapters.HexDeterminant}

{include 0 HexManual.Chapters.HexBareiss}

{include 0 HexManual.Chapters.HexResultant}

{include 0 HexManual.Chapters.HexGramSchmidt}

{include 0 HexManual.Chapters.HexLLL}

{include 0 HexManual.Chapters.HexBerlekampZassenhaus}

{include 0 HexManual.Chapters.FactorTactics}

{include 0 HexManual.Chapters.HexNumberField}

{include 0 HexManual.Chapters.HexNumberFieldTower}

{include 0 HexManual.Chapters.HexPermGroup}

{include 0 HexManual.Chapters.HexGraphIso}

{include 0 HexManual.Chapters.NautyAlgorithm}

# Tutorials
%%%
tag := "tutorials"
%%%

The reference chapters above document each library on its own terms. The
tutorials here are application-first: each leads with a problem a reader
already cares about and shows the libraries carrying a recognizable
end-to-end workflow. Lean examples are checked by the manual build or their
linked conformance targets.

{include 2 HexManual.Tutorials.AESField}

{include 2 HexManual.Tutorials.AESModulus}

{include 2 HexManual.Tutorials.PrimeSplitting}

{include 2 HexManual.Tutorials.Coppersmith}

{include 2 HexManual.Tutorials.FieldPrimes}

{include 2 HexManual.Tutorials.RubiksCube}

# Draft sections for unreleased libraries
%%%
tag := "unreleased"
%%%

These libraries are still incubating in the
[`hex-dev`](https://github.com/kim-em/hex-dev) monorepo and have not been
split out for release yet, so their APIs may still change. They are grouped
here to keep the reference chapters above focused on the released libraries.

{include 2 HexManual.Chapters.HexRealAlgebraic}

{include 2 HexManual.Chapters.HexReflect}

{include 2 HexManual.Chapters.HexRealFormula}

{include 2 HexManual.Chapters.HexRationalFn}

{include 2 HexManual.Chapters.HexOrderedFn}

{include 2 HexManual.Chapters.HexSturm}

{include 2 HexManual.Chapters.HexSignDet}

{include 2 HexManual.Chapters.HexRealClosure}

{include 2 HexManual.Chapters.HexLatticeEnum}

{include 2 HexManual.Chapters.HexIntFactor}

{include 2 HexManual.Chapters.HexCharPoly}

{include 2 HexManual.Chapters.HexPolyZGcd}

{include 2 HexManual.Chapters.HexMvGcd}

{include 2 HexManual.Chapters.HexMvHensel}

{include 2 HexManual.Chapters.HexMvFactor}

{include 2 HexManual.Chapters.HexPolySmith}

{include 2 HexManual.Chapters.HexSmith}

{include 2 HexManual.Chapters.HexMinPoly}
