/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module


public import HexIntervalMathlib.Interval
public import HexIntervalMathlib.Addition
public import HexIntervalMathlib.Subtraction
public import HexIntervalMathlib.MinMax
public import HexIntervalMathlib.Absolute
public import HexIntervalMathlib.Multiplication
public import HexIntervalMathlib.Power
public import HexIntervalMathlib.Split
public import HexIntervalMathlib.Inverse
public import HexIntervalMathlib.Division
public import HexIntervalMathlib.Driver
public import HexIntervalMathlib.Controller
public import HexIntervalMathlib.Regularize
public import HexIntervalMathlib.Program
public import HexIntervalMathlib.Proof
public import HexIntervalMathlib.RuntimeProof
public import HexIntervalMathlib.RuntimeTerminal
public import HexIntervalMathlib.RuntimeRule
public import HexIntervalMathlib.Rule
public import HexIntervalMathlib.Frontend
public import HexIntervalMathlib.Tactic

public section

/-!
`HexIntervalMathlib` supplies Mathlib semantics and proof-facing theorems for
the supported `Hex.Interval` operations, including resource-checked addition,
subtraction, and multiplication, exact minimum/maximum images, absolute value,
natural power, outward regularization, and closed-left/strict-right
transactional splitting, plus precision-indexed reciprocal and division
enclosures. It also supplies the function-agnostic semantics of supported
programs and the chronological, package-owned proof-replay boundary.
`HexIntervalMathlib.RuntimeProof` transactionally converts sealed typed runtime
transition chains into those proof events without trusting raw quotations.
`HexIntervalMathlib.RuntimeTerminal` binds target and refutation settlement to
the same sealed runtime/search lineage, theorem registry, and immutable proof
input; general split settlement remains blocked by the runtime/proof child
equality-arena mismatch documented by that module.
`HexIntervalMathlib.Rule` supplies a checked built-in arithmetic package whose
schemas recompute checked public operations before producing proof evidence.
`HexIntervalMathlib.RuntimeRule` supplies the aligned executable half: its
callbacks recompute those operations into typed fact batches, and its combined
builder seals exact replay-format/schema coverage while admitting explicitly
paired packages for configured opaque operations.
`HexIntervalMathlib.Controller` supplies explicit stable application-table,
runtime/proof-registry alignment and bounded deterministic policy iteration
over the sealed retained tree, including caller-measured caps on each retained
policy state. Automatic package discovery and public split-search tactic
integration remain separate.
`HexIntervalMathlib.Frontend` supplies bounded recursive arithmetic reification,
source-driven version-zero facts, and flat programmatic replay/closure
combinators.
`HexIntervalMathlib.Tactic` supplies the first supported Lean-expression,
local-hypothesis, runtime-authentication, and transactional tactic bridge for
forward arithmetic bounds. Its bare tactics use the `2⁻¹⁶` dyadic grid.
-/
