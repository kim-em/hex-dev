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
public import HexIntervalMathlib.Regularize
public import HexIntervalMathlib.Program
public import HexIntervalMathlib.Proof
public import HexIntervalMathlib.Rule
public import HexIntervalMathlib.Frontend

public section

/-!
`HexIntervalMathlib` supplies Mathlib semantics and proof-facing theorems for
the supported `Hex.Interval` operations, including resource-checked addition,
subtraction, and multiplication, exact minimum/maximum images, absolute value,
natural power, outward regularization, and closed-left/strict-right
transactional splitting, plus precision-indexed reciprocal and division
enclosures. It also supplies the function-agnostic semantics of supported
programs and the chronological, package-owned proof-replay boundary.
`HexIntervalMathlib.Rule` supplies a checked built-in arithmetic package whose
schemas recompute checked public operations before producing proof evidence.
`HexIntervalMathlib.Frontend` supplies bounded recursive arithmetic reification,
exact source binding, and flat programmatic replay/closure combinators.
-/
