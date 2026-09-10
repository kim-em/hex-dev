/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexGraph.Basic

public section

/-!
`HexGraph` provides finite simple undirected graphs on `Fin n` with
executable symmetric irreflexive adjacency, a checked edge-list builder,
neighbour arrays, and relabelling. The library is Mathlib-free.
-/
