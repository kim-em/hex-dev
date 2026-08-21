/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexInterval.Interval
public import HexInterval.Multiplication
public import HexInterval.Action
public import HexInterval.State
public import HexInterval.Trace
public import HexInterval.Policy
public import HexInterval.Search

public section

/-!
`HexInterval` is the Mathlib-free computational kernel for exact interval
data, propagation search, and replayable derivations.

The public implementation exposes canonical exact intervals through a sealed
representation, resource-safe smart constructors, and resource-checked
intersection, hull, negation, addition, subtraction, multiplication, minimum,
maximum, absolute value, natural power, outward regularization, reciprocal,
division, and
transactional splitting at a dyadic cut. The arithmetic resource layer
preflights product growth, direct-power retained growth, exponent work,
rational-backed precision/quotient work, and Core directed-rounding work
independently of exact comparison work. The reciprocal operation is a
precision-indexed connected outward enclosure. Division exposes direct outward
cuts for two nonzero finite singletons, exact empty and total-zero cases, and a
sound whole-line fallback for every other nonempty shape. Raw cuts remain
visible as the explicit decoder and inspection boundary. The public structural
contracts also cover checked typed SSA programs, versioned fact projections,
registrations, scoped bindings, actions, immutable package requests, checked
immutable branch state, dependency/work queues, authoritative chronology, and
bounded diagnostics. The public policy contract exposes bounded immutable
offers, exact echoed decisions, and fail-closed revalidation without selecting
a default policy. The public search contract authenticates selected actions, transactionally
checks untrusted callback deltas, and supplies bounded stable branch-frontier
accounting. Concrete callbacks and proposals, offer generation, policy
implementations, split semantics, proof replay, and measurement-selected
storage remain experimental.
-/
