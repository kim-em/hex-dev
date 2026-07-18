/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexRealRootsMathlib.SturmChainDefs
public import HexRealRootsMathlib.SturmTheorem
public import HexRealRootsMathlib.Hadamard
public import HexRealRootsMathlib.Discr
public import HexRealRootsMathlib.Separation
public import HexRealRootsMathlib.ChainCorrespond
public import HexRealRootsMathlib.Isolations
public import HexRealRootsMathlib.Drivers
public import HexRealRootsMathlib.SimpleRealRoot
public import HexRealRootsMathlib.TwoCircle
public import HexRealRootsMathlib.DescartesParity
public import HexRealRootsMathlib.TwoCircleRegion

public section

/-!
The `HexRealRootsMathlib` library is the Mathlib companion for the executable
real-root isolation library `HexRealRoots`.

The **self-contained Sturm slice** — the zero-skipping sign-variation count
`Sturm.sturmVar`, the generalised-chain predicate `Sturm.IsSturmChain`, and the
counting/line forms of Sturm's theorem over `Polynomial ℝ` — is deliberately
free of any `HexRealRoots` dependence, so it can be contributed to Mathlib
(which does not yet have Sturm's theorem) once exercised here.

The executable-correspondence and consequence files build on it:
`ChainCorrespond` connects `Hex.sturmChain`, `Hex.sturmCount`, and `Hex.rootCount`
to the abstract development; `Separation`/`Discr`/`Hadamard` supply the Mahler
separation bound; `Isolations` and `Drivers` prove isolation soundness, run
completeness, driver completeness, and refinement; `SimpleRealRoot` proves the
root-identity theorems (overlap classes are the real roots); and `TwoCircle`
states the single deferred theorem — Descartes-engine termination — behind its
Obreshkoff two-circle prerequisite, the one intentional `sorry` in the library.
-/
