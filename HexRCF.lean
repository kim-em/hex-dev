/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexRCF.Syntax
public import HexRCF.Language
public import HexRCF.LanguageTests
public import HexRCF.SturmCheck
public import HexRCF.SturmReplay
public import HexRCF.SturmBuilder
public import HexRCF.SturmBuilderTests
public import HexRCF.CarrierCheck
public import HexRCF.Carrier
public import HexRCF.CarrierTests
public import HexRCF.IsolationCheck
public import HexRCF.Isolations
public import HexRCF.IsolationsTests
public import HexRCF.SeparationCheck
public import HexRCF.Separation
public import HexRCF.SeparationTests
public import HexRCF.CellsCheck
public import HexRCF.Cells
public import HexRCF.CellsTests
public import HexRCF.CommonRootCheck
public import HexRCF.CommonRoot
public import HexRCF.CommonRootTests
public import HexRCF.SignMatrixCheck
public import HexRCF.SignMatrix
public import HexRCF.SignMatrixTests
public import HexRCF.Builder
public import HexRCF.BuilderTests
public import HexRCF.Certificate
public import HexRCF.Soundness
public import HexRCF.CertificateTests
public import HexRCF.DecisionCheck
public import HexRCF.Decision
public import HexRCF.DecisionTests
public import HexRCF.Reify
public import HexRCF.Tactic
public import HexRCF.ReifyTests

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
Checked common-root packages cache one multiplication-only gcd witness and
generalized replay per distinct nonconstant atom, with exact root-cell queries.
The sign-matrix layer then recomputes guarded open and root signs, validates
coefficient-equality package alignment, and reflects every Boolean formula
to one exact truth value on each semantic cell.
Compiled arithmetic preparation constructs checker-retained carrier witnesses
and one aligned common-root package per distinct nonconstant atom, using exact
rational arithmetic and denominator clearing outside kernel replay.
The top-level certificate replay handles empty domains, constants, root-free
carriers, and positive-root cell decompositions as distinct fail-closed
branches. Strict option-valued folds propagate malformed active cells, and
the soundness theorem lifts every accepted verdict to the quantified sentence.
Compiled decision assembly runs isolation, strict separation, endpoint
classification, and arithmetic preparation outside the kernel, retains only
well-formed replay verdicts, and returns `true` only after the proof-producing
certificate checker accepts.
The `rcf` tactic reifies singly quantified real polynomial goals, clears exact
rational denominators with kernel-checked positive scaling, runs certificate
construction as compiled meta code, and embeds only literal evidence accepted
by the Boolean checker. Its generated proof transports `check_sound` through a
kernel-checked equivalence with the source goal; false verdicts remain
cell-specific diagnostics.
-/
