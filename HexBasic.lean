/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexBasic.ArrayDecEq
public import HexBasic.ExtTreeMap
public import HexBasic.Fold
public import HexBasic.ModuleBoundaryTests
public import HexBasic.OfFn
public import HexBasic.ListShim
public import HexBasic.Vector.Modify

public section

/-!
`HexBasic` is the lowest Mathlib-free `hex` library: a home for small,
general-purpose helpers that clearly belong in the standard library and are
reproduced here so the library remains Mathlib-free. It provides reusable
`ExtTreeMap` merge/traversal operations, the shared
`List.foldl` algebra (`HexBasic.Fold`), the `Batteries` list lemmas reproduced
in `HexBasic.ListShim`, the `Vector.modify` update helper, and
kernel-reducible `Array`/`Vector` equality (`HexBasic.ArrayDecEq`) and
`ofFn` (`HexBasic.OfFn`).
-/
