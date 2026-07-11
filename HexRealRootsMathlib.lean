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

public section

/-!
The `HexRealRootsMathlib` library is the Mathlib companion for the executable
real-root isolation library `HexRealRoots`.

This umbrella currently exposes only the **self-contained Sturm slice**: the
zero-skipping sign-variation count `Sturm.sturmVar`, the generalised-chain
predicate `Sturm.IsSturmChain`, and the five-step statement of Sturm's theorem
over `Polynomial ℝ`. The slice is deliberately free of any `HexRealRoots`
dependence, so it can be contributed to Mathlib (which does not yet have
Sturm's theorem) once exercised here.

The executable-correspondence files — connecting `Hex.sturmChain`,
`Hex.sturmCount`, and the isolation drivers to this abstract development, and
the isolation-soundness and driver-completeness theorems — arrive in later PRs.
-/
