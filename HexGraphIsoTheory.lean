/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexGraphIsoTheory.Basic
public import HexGraphIsoTheory.Encode
public import HexGraphIsoTheory.Sparse.Encode
public import HexGraphIsoTheory.Sparse.Canonical
public import HexGraphIsoTheory.Sparse.Automorphism
public import HexGraphIsoTheory.Automorphism
public import HexGraphIsoTheory.AutTactic
public import HexGraphIsoTheory.TacticSupport
public import HexGraphIsoTheory.Tactic

public section

/-!
`HexGraphIsoTheory` relates the executable coloured graphs of
`HexGraphIso` to Mathlib's `SimpleGraph`: Mathlib-facing coloured graphs
and isomorphisms, the finite encoding with its correspondence theorems,
and the `graph_iso` extension to closed `SimpleGraph` goals.
-/
