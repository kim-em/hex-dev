/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexRCF.Language
public import HexRCF.LanguageTests
public import HexRCF.SturmReplay
public import HexRCF.SturmBuilder
public import HexRCF.SturmBuilderTests

public section

/-!
The `HexRCF` library defines the reflected language used by a
certificate-producing decision procedure for univariate real-closed-field
sentences.

The reflected language supports Boolean combinations of integer-polynomial
comparisons under one universal or existential quantifier, either over the real
line or over a half-open dyadic interval. Multiplication-only generalized Sturm
replays provide the certified literal root counts used by the decision
pipeline.
-/
