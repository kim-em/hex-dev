/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexRealRoots.Basic
public import HexRealRoots.Chain
public import HexRealRoots.Prec
public import HexRealRoots.Refine
public import HexRealRoots.Var
public import HexRealRoots.Cert
public import HexRealRoots.IsolateSturm
public import HexRealRoots.Mobius
public import HexRealRoots.IsolateDescartes
public import HexRealRoots.Isolate
public import HexRealRoots.SimpleRealRoot
public import HexRealRoots.ReplayTest

public section

/-!
The `HexRealRoots` library certifies the isolation of the real roots of
integer-coefficient polynomials. A real root isolation is a half-open
dyadic interval `(lower, upper]` together with a witness, dischargeable
by `decide`, that exactly one real root of `p ∈ ℤ[x]` lies in it. The
witness is a Sturm count: the sign-variation difference of the Sturm
chain of `p` evaluated at the two endpoints, which counts the roots in
the interval exactly.

Isolation runs two engines over the same output type — a fast Descartes
search and a provably terminating Sturm search — and every emitted
isolation carries a Sturm-count witness regardless of which engine found
it. `ZPoly` values are evaluated at dyadic points by exact Horner
arithmetic, so the sign of `p(x)` at a dyadic `x` is exact: no floats,
no interval arithmetic, no error budget.

This is the Mathlib-free computational layer; the correctness and
completeness theorems live in the companion `HexRealRootsMathlib`.
-/
