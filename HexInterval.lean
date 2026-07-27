/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexInterval.Basic
public import HexInterval.Experiment.Representation
public import HexInterval.Experiment.Rational

public section

/-!
`HexInterval` is the Mathlib-free computational kernel for exact interval
data, propagation search, and replayable derivations.

The initial implementation exposes only the representation-independent raw
cut layer.  D2 experiments select the opaque public interval representation
before the wider arithmetic and search API is frozen.
-/
