/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexBerlekamp.Basic
public import HexBerlekamp.DelayedKernel
public import HexBerlekamp.DistinctDegree
public import HexBerlekamp.Factor
public import HexBerlekamp.Irreducibility
public import HexBerlekamp.IrreducibleDecide
public import HexBerlekamp.RabinSoundness

public section

/-!
`HexBerlekamp` exposes the executable Berlekamp-matrix surface for factoring
over `F_p`, centered on the Frobenius matrix `Q_f`, its fixed-space kernel, and
the first irreducibility-facing, split-step factoring, and distinct-degree
factorization tests built from that data.
-/
