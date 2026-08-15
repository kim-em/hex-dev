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
maximum, absolute value, natural power, outward regularization, and
transactional splitting at a dyadic cut. The arithmetic resource layer
preflights product growth, direct-power retained growth, exponent work,
rational-backed precision/quotient work, and Core directed-rounding work
independently of exact comparison work. The reciprocal operation is a
precision-indexed connected outward enclosure. Division exposes direct outward
cuts for two nonzero finite singletons, exact empty and total-zero cases, and a
sound whole-line fallback for every other nonempty shape. Raw cuts remain
visible as the explicit decoder and inspection boundary; D2 propagation and
replay experiments still live outside this supported umbrella.
-/
