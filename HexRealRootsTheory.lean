/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexRealRootsTheory.TarskiSoundness
public import HexRealRootsTheory.TarskiMod
public import HexRealRootsTheory.TarskiReal
public import HexRealRootsTheory.RealClosed
public import HexRealRootsTheory.TarskiInterpret
public import HexRealRootsTheory.TarskiGcd
public import HexRealRootsTheory.TarskiCompare
public import HexRealRootsTheory.TarskiCount
public import HexRealRootsTheory.TarskiSum
public import HexRealRootsTheory.TarskiSigns
public import HexRealRootsTheory.TarskiInteger
public import HexRealRootsTheory.TarskiDomain
public import HexRealRootsTheory.SturmChainDefs
public import HexRealRootsTheory.SturmTheorem
public import HexRealRootsTheory.SturmCertificate
public import HexRealRootsTheory.RealRootCount
public import HexRealRootsTheory.Hadamard
public import HexRealRootsTheory.Discr
public import HexRealRootsTheory.Separation
public import HexRealRootsTheory.Sign
public import HexRealRootsTheory.ChainCorrespond
public import HexRealRootsTheory.LiteralChain
public import HexRealRootsTheory.LiteralIsolations
public import HexRealRootsTheory.LiteralChainTests
public import HexRealRootsTheory.SquareFreeCore
public import HexRealRootsTheory.Isolations
public import HexRealRootsTheory.IsolateRoots
public import HexRealRootsTheory.IsolateRootsElab
public import HexRealRootsTheory.Drivers
public import HexRealRootsTheory.SimpleRealRoot
public import HexRealRootsTheory.TwoCircle
public import HexRealRootsTheory.DescartesParity
public import HexRealRootsTheory.TwoCircleRegion
public import HexRealRootsTheory.TwoCircleSector
public import HexRealRootsTheory.MobiusCorrespond

public section

/-!
The `HexRealRootsTheory` library is the theory companion for the executable
real-root isolation library `HexRealRoots`.

The Sturm development includes the zero-skipping sign-variation count
{name}`Sturm.sturmVar`, the generalised-chain predicate
{name}`Sturm.IsSturmChain`, and the counting and line forms of Sturm's theorem
over `Polynomial ℝ`, independently of the executable `HexRealRoots` types.

`SturmCertificate` assembles root-count certificates from identities between
Mathlib polynomials. `RealRootCount` uses them to provide `by real_root_count`
and the term form `real_root_count p`, with Hex supplying the candidate chain.

The executable correspondence builds on these results:
`ChainCorrespond` connects {name}`Hex.ZPoly.sturmChain`,
{name}`Hex.ZPoly.sturmCount`, and
{name}`Hex.ZPoly.rootCount` to the abstract development; `LiteralChain` proves the
corresponding theorem
for a supplied positive-scaled recurrence, and `LiteralIsolations` states
isolation semantics for its supplied counts; `Separation` supplies the Mahler
separation bound, using `HexPolyZTheory.MahlerSeparation` and the analysis
re-exported by the `Discr`/`Hadamard` modules; `Isolations` and `Drivers` prove
isolation soundness, run
completeness, driver completeness, and refinement; `SimpleRealRoot` proves the
root-identity theorems (overlap classes are the real roots); and `TwoCircle`
proves Descartes-engine termination
({name}`HexRealRootsTheory.isolateDescartes?_isSome`) behind its
Obreshkoff two-circle prerequisite (the λ-graded sector bound in
`TwoCircleSector`, the region geometry in `TwoCircleRegion`, and the Descartes
parity in `DescartesParity`).
-/
