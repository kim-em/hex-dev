/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexRootsMathlib.Basic

public section

/-!
The `HexRootsMathlib` library is the Mathlib companion for the executable
complex-root isolation library `HexRoots`.

It connects exact dyadic witnesses to Mathlib's real and complex geometry and
will prove soundness of the atom-path isolation driver. The first module
supplies the exact casts used by every later correspondence proof.
-/
