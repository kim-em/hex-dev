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
public import HexRealRootsMathlib.SquareFreeCore
public import HexRealRootsMathlib.Isolations
public import HexRealRootsMathlib.IsolateRoots
public import HexRealRootsMathlib.IsolateRootsTests
public import HexRealRootsMathlib.Drivers
public import HexRealRootsMathlib.SimpleRealRoot
public import HexRealRootsMathlib.TwoCircle
public import HexRealRootsMathlib.DescartesParity
public import HexRealRootsMathlib.TwoCircleRegion
public import HexRealRootsMathlib.TwoCircleSector
public import HexRealRootsMathlib.MobiusCorrespond

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
to the abstract development; `Separation` supplies the Mahler separation bound,
using `HexPolyZMathlib.MahlerSeparation` and the analysis re-exported by the
`Discr`/`Hadamard` compatibility modules; `Isolations` and `Drivers` prove
isolation soundness, run
completeness, driver completeness, and refinement; `SimpleRealRoot` proves the
root-identity theorems (overlap classes are the real roots); and `TwoCircle`
proves Descartes-engine termination (`isolateDescartes?_isSome`) behind its
Obreshkoff two-circle prerequisite (the λ-graded sector bound in
`TwoCircleSector`, the region geometry in `TwoCircleRegion`, and the Descartes
parity in `DescartesParity`). Every theorem in the library is now proven; there
are no `sorry`s.
-/
