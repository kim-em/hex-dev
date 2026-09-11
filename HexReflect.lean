/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexReflect.Budget
public import HexReflect.Result
public import HexReflect.Convert
public import HexReflect.Provider
public import HexReflect.Proof
public import HexReflect.State
public import HexReflect.Session

public section

/-!
Shared algebraic reflection for symbolic Hex frontends.

`HexReflect` is the only Hex library that imports `Lean.Meta.Sym.Arith`. It
reifies a batch of commutative-ring expressions over one sealed variable
environment, converts each reflected expression directly to `Hex.MvPoly`, and
proves that the conversion preserves interpretation. It also defines the
provider outcomes, conditions, result records, budgets, and decline reasons
shared by symbolic frontends.
-/
