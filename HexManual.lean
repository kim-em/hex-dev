import VersoManual

import HexManual.Chapters.HexGFqRing
import HexManual.Chapters.HexGFqMathlib
import HexManual.Chapters.HexModArith
import HexManual.Chapters.HexModArithMathlib
import HexManual.Chapters.HexPoly
import HexManual.Chapters.HexPolyZ
import HexManual.Chapters.HexGramSchmidt

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

set_option pp.rawOnError true

/-!
The `HexManual` Verso aggregator. Each per-library reference chapter
lives at `HexManual/Chapters/<LibraryName>.lean` and is included
below. As additional libraries clear Phase 6 their chapters get
added to this aggregator.
-/

#doc (Manual) "Hex" =>
%%%
authors := ["The hex project"]
shortTitle := "hex"
%%%

`hex` is a Mathlib-free executable computational algebra stack
covering finite fields, polynomial factorization, and lattice
reduction, together with a separately maintained Mathlib-side
correspondence layer that re-exports the executable theory as theorems
about the corresponding Mathlib structures. This manual collects per-library
reference chapters for the libraries that have reached the
documentation phase of the development plan.

{include 0 HexManual.Chapters.HexGFqRing}

{include 0 HexManual.Chapters.HexGFqMathlib}

{include 0 HexManual.Chapters.HexModArith}

{include 0 HexManual.Chapters.HexModArithMathlib}

{include 0 HexManual.Chapters.HexPoly}

{include 0 HexManual.Chapters.HexPolyZ}

{include 0 HexManual.Chapters.HexGramSchmidt}
