/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

-- Public operations, automorphism groups, and the closed-graph tactic.
public import HexGraphIso.Sparse.Tactic
public import HexGraphIso.Sparse.UncoloredAutos

-- Additional refinement and search theorems beyond the API's dependencies.
public import HexGraphIso.Nauty.Sparse.RefineLiteral
public import HexGraphIso.Nauty.Sparse.Recover
public import HexGraphIso.Nauty.Sparse.ReferenceResult
public import HexGraphIso.Nauty.Sparse.RootHistory
public import HexGraphIso.Nauty.Sparse.OrderStep
public import HexGraphIso.Nauty.Sparse.CodeResult
public import HexGraphIso.Nauty.Sparse.CanonCover

/-!
Native sparse coloured graphs, checked transporters, and total sparse-nauty
result extraction. The production search and parser are total, and the
canonical forms and complete decisions satisfy their declarative contracts.
-/
