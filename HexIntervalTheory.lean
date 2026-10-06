/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module


public import HexIntervalTheory.Interval
public import HexIntervalTheory.Addition
public import HexIntervalTheory.Subtraction
public import HexIntervalTheory.MinMax
public import HexIntervalTheory.Absolute
public import HexIntervalTheory.Multiplication
public import HexIntervalTheory.Power
public import HexIntervalTheory.Split
public import HexIntervalTheory.Inverse
public import HexIntervalTheory.Division
public import HexIntervalTheory.Driver
public import HexIntervalTheory.Controller
public import HexIntervalTheory.Regularize
public import HexIntervalTheory.Program
public import HexIntervalTheory.Proof
public import HexIntervalTheory.RuntimeProof
public import HexIntervalTheory.RuntimeTerminal
public import HexIntervalTheory.RuntimeRule
public import HexIntervalTheory.RuntimeEmit
public import HexIntervalTheory.RuntimeRuleEmit
public import HexIntervalTheory.Rule
public import HexIntervalTheory.Frontend
public import HexIntervalTheory.Tactic

public section

/-!
`HexIntervalTheory` supplies Mathlib semantics and proof-facing theorems for
the supported `Hex.Interval` operations, including resource-checked addition,
subtraction, and multiplication, exact minimum/maximum images, absolute value,
natural power, outward regularization, and closed-left/strict-right
transactional splitting, plus precision-indexed reciprocal and division
enclosures. It also supplies the function-agnostic semantics of supported
programs and the chronological, package-owned proof-replay boundary.
`HexIntervalTheory.RuntimeProof` transactionally converts sealed typed runtime
transition chains into those proof events without trusting raw quotations.
`HexIntervalTheory.RuntimeTerminal` binds target and refutation settlement to
the same sealed runtime/search lineage, theorem registry, and immutable proof
input; general split settlement remains blocked by the runtime/proof child
equality-arena mismatch documented by that module.
`HexIntervalTheory.RuntimeEmit` quotes only a sealed one-node target lineage
into an exactly checked `Proof.Evidence` expression through package-owned
transparent theorem handles. `HexIntervalTheory.RuntimeRuleEmit` jointly
assembles those handles with the executable and theorem views of the twelve
built-in arithmetic rules. Refutation and split expression emission are not
supported.
`HexIntervalTheory.Rule` supplies a checked built-in arithmetic package whose
schemas recompute checked public operations before producing proof evidence.
`HexIntervalTheory.RuntimeRule` supplies the aligned executable half: its
callbacks recompute those operations into typed fact batches, and its combined
builder seals exact replay-format/schema coverage while admitting explicitly
paired packages for configured opaque operations.
`HexIntervalTheory.Controller` supplies explicit stable application-table,
runtime/proof-registry alignment and bounded deterministic policy iteration
over the sealed retained tree, including caller-measured caps on each retained
policy state. Automatic package discovery and public split-search tactic
integration remain separate.
`HexIntervalTheory.Frontend` supplies bounded recursive arithmetic reification,
source-driven version-zero facts, and flat programmatic replay/closure
combinators.
`HexIntervalTheory.Tactic` supplies the first supported Lean-expression,
local-hypothesis, runtime-authentication, and transactional tactic bridge for
forward arithmetic bounds. Its bare tactics use the `2⁻¹⁶` dyadic grid.
-/
