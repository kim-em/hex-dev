/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexInterval.Canonical

public section

/-!
`HexInterval` is the Mathlib-free computational kernel for exact interval
data, propagation search, and replayable derivations.

The public implementation exposes canonical exact intervals through a sealed
representation and resource-safe smart constructors.  Raw cuts remain visible
as the explicit decoder and inspection boundary; D2 propagation and replay
experiments still live outside this supported umbrella.
-/
