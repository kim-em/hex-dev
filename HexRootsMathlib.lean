/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexRootsMathlib.ArgumentPrinciple
public import HexRootsMathlib.ArgumentTopology
public import HexRootsMathlib.Basic
public import HexRootsMathlib.Bisection
public import HexRootsMathlib.Cauchy
public import HexRootsMathlib.Certificate
public import HexRootsMathlib.CircleIntegralLemmas
public import HexRootsMathlib.Completeness.DriverCompleteness
public import HexRootsMathlib.Completeness.NKConverse
public import HexRootsMathlib.Completeness.NKDepth
public import HexRootsMathlib.Completeness.NKRecertification
public import HexRootsMathlib.Completeness.NewtonContraction
public import HexRootsMathlib.Completeness.PelletConverse
public import HexRootsMathlib.Completeness.PelletDyadic
public import HexRootsMathlib.Completeness.PelletTail
public import HexRootsMathlib.Completeness.RootFreeConverse
public import HexRootsMathlib.Completeness.SurvivorComponent
public import HexRootsMathlib.Component
public import HexRootsMathlib.Driver
public import HexRootsMathlib.Geometry
public import HexRootsMathlib.Glue
public import HexRootsMathlib.HasOnlySimpleRoots
public import HexRootsMathlib.Isolate
public import HexRootsMathlib.Kantorovich
public import HexRootsMathlib.KantorovichPoly
public import HexRootsMathlib.Loop
public import HexRootsMathlib.MahlerPrec
public import HexRootsMathlib.NKCertify
public import HexRootsMathlib.NKDriver
public import HexRootsMathlib.NKWitness
public import HexRootsMathlib.Pellet
public import HexRootsMathlib.Refinement
public import HexRootsMathlib.RootFree
public import HexRootsMathlib.Rouche
public import HexRootsMathlib.RoucheHomotopy
public import HexRootsMathlib.SimpleRoot
public import HexRootsMathlib.Taylor

public section

/-!
The `HexRootsMathlib` library is the Mathlib companion for the executable
complex-root isolation library `HexRoots`.

It connects exact dyadic witnesses to Mathlib's real and complex geometry and
proves soundness and completeness of the atom-path isolation driver. Its
correspondence modules connect the exact executable witnesses to unique roots,
root counts, coverage, separation, and refinement semantics. The completeness
layer proves that every atom strategy succeeds on nonzero squarefree input.
-/
