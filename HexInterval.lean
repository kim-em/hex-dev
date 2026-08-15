/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexInterval.Interval
public import HexInterval.Multiplication

public section

/-!
`HexInterval` is the Mathlib-free computational kernel for exact interval
data, propagation search, and replayable derivations.

The public implementation exposes canonical exact intervals through a sealed
representation, resource-safe smart constructors, and resource-checked
intersection, hull, negation, addition, subtraction, multiplication, minimum,
maximum, and absolute value. The arithmetic resource layer preflights product
growth, direct-power retained growth, and exponent work independently of
exact comparison work; public interval power remains future work. Raw cuts
remain visible as the explicit decoder and inspection boundary; D2 propagation
and replay experiments still live outside this supported umbrella.
-/
