/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexRootsTheory.ArgumentPrinciple
public import HexRootsTheory.ArgumentTopology
public import HexRootsTheory.Basic
public import HexRootsTheory.Bisection
public import HexRootsTheory.Cauchy
public import HexRootsTheory.Conjugate
public import HexRootsTheory.Certificate
public import HexRootsTheory.CircleIntegralLemmas
public import HexRootsTheory.Completeness.DriverCompleteness
public import HexRootsTheory.Completeness.NKConverse
public import HexRootsTheory.Completeness.NKDepth
public import HexRootsTheory.Completeness.NKRecertification
public import HexRootsTheory.Completeness.NewtonContraction
public import HexRootsTheory.Completeness.PelletConverse
public import HexRootsTheory.Completeness.PelletDyadic
public import HexRootsTheory.Completeness.PelletTail
public import HexRootsTheory.Completeness.RootFreeConverse
public import HexRootsTheory.Completeness.RefinementCompleteness
public import HexRootsTheory.Completeness.SurvivorComponent
public import HexRootsTheory.Component
public import HexRootsTheory.Driver
public import HexRootsTheory.Geometry
public import HexRootsTheory.Glue
public import HexRootsTheory.HasOnlySimpleRoots
public import HexRootsTheory.Isolate
public import HexRootsTheory.IsolateTotal
public import HexRootsTheory.Kantorovich
public import HexRootsTheory.KantorovichPoly
public import HexRootsTheory.Loop
public import HexRootsTheory.MahlerPrec
public import HexRootsTheory.NKCertify
public import HexRootsTheory.NKDriver
public import HexRootsTheory.NKWitness
public import HexRootsTheory.Pellet
public import HexRootsTheory.Refinement
public import HexRootsTheory.RootFree
public import HexRootsTheory.Rouche
public import HexRootsTheory.RoucheHomotopy
public import HexRootsTheory.SimpleRoot
public import HexRootsTheory.Taylor

public section

/-!
The `HexRootsTheory` library is the theory companion for the executable
complex-root isolation library `HexRoots`.

It connects exact dyadic witnesses to Mathlib's real and complex geometry and
proves soundness and completeness of the atom-path isolation driver. Its
correspondence modules connect the exact executable witnesses to unique roots,
root counts, coverage, separation, and refinement semantics. The completeness
layer proves that every atom strategy succeeds on nonzero squarefree input and
that one-atom refinement succeeds under the default mixed strategy from local
simplicity alone.
-/
