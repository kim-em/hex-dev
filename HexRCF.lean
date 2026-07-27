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
public import HexRCF.Carrier
public import HexRCF.CarrierTests
public import HexRCF.Isolations
public import HexRCF.IsolationsTests
public import HexRCF.Separation
public import HexRCF.SeparationTests
public import HexRCF.Cells
public import HexRCF.CellsTests

public section

/-!
The `HexRCF` library defines the reflected language used by a
certificate-producing decision procedure for univariate real-closed-field
sentences.

The reflected language supports Boolean combinations of integer-polynomial
comparisons under one universal or existential quantifier, either over the real
line or over a half-open dyadic interval. Multiplication-only generalized Sturm
replays provide the certified literal root counts used by the decision
pipeline. Multiplication-checkable carrier identities connect those counts to
the sentence's atom roots. Raw generalized isolations are refined into
strictly separated intervals, and exact replay counts classify their roots
against bounded-domain endpoints. The checked roots induce an alternating,
size-indexed partition into root and open cells with exact dyadic samples and
exact guarded intersection tests for half-open bounded domains.
-/
