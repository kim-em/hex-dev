/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexRootsMathlib.Basic
public import HexRootsMathlib.Bisection
public import HexRootsMathlib.Cauchy
public import HexRootsMathlib.Component
public import HexRootsMathlib.Geometry
public import HexRootsMathlib.Kantorovich
public import HexRootsMathlib.KantorovichPoly
public import HexRootsMathlib.Loop
public import HexRootsMathlib.MahlerPrec
public import HexRootsMathlib.NKCertify
public import HexRootsMathlib.NKDriver
public import HexRootsMathlib.NKWitness
public import HexRootsMathlib.RootFree
public import HexRootsMathlib.Taylor

public section

/-!
The `HexRootsMathlib` library is the Mathlib companion for the executable
complex-root isolation library `HexRoots`.

It connects exact dyadic witnesses to Mathlib's real and complex geometry and
will prove soundness of the atom-path isolation driver. The initial modules
supply the exact casts and geometric bounds used by every later correspondence
proof. The separation layer certifies the exact executable `mahlerPrec`
formula against distinct complex roots.
-/
