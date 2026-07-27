/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexInterval.Basic

public section

/-!
`HexInterval` is the Mathlib-free computational kernel for exact interval
data, propagation search, and replayable derivations.

The initial public implementation exposes only the representation-independent
raw cut layer. D2 experiments live outside this supported umbrella while they
select the opaque interval representation and proof-facing encoding.
-/
