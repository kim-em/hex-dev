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

public section

/-!
`HexIntervalMathlib` supplies Mathlib semantics and proof-facing theorems for
the supported `Hex.Interval` operations, including resource-checked addition,
subtraction, and multiplication, exact minimum/maximum images, and absolute
value.
-/
