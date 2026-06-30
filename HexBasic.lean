/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexBasic.Fold
public import HexBasic.ListShim
public import HexBasic.Vector.Modify

public section

/-!
`HexBasic` is the lowest Mathlib-free `hex` library: a home for small,
general-purpose helpers that clearly belong in the standard library and are
reproduced here only until they migrate up to lean4. It provides the shared
`List.foldl` algebra (`HexBasic.Fold`), the `Batteries` list lemmas reproduced
in `HexBasic.ListShim`, and the `Vector.modify` update helper.
-/
