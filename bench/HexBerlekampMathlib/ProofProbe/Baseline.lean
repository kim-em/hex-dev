/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public meta import HexBerlekamp.IrreducibilityElab
public meta import HexBerlekampMathlib.FactorTactic
public import HexBerlekamp.IrreducibilityElab
public import HexBerlekampMathlib.FactorTactic

public section

/-!
Matched import-only baseline for the `factor_poly`/`irreducibility`
fresh-module probes.

This is a build-only proof-elaboration probe. It is deliberately not a
`lean-bench` registration or executable.
-/
