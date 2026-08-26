/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexBasic.ArrayDecEq
public import HexBasic.Conditional
public import HexBasic.ExactDiv
public import HexBasic.ExtTreeMap
public import HexBasic.Fold
public import HexBasic.List
public import HexBasic.ModuleBoundaryTests
public import HexBasic.OfFn
public import HexBasic.Rand
public import HexBasic.Vector.Modify

public section

/-!
`HexBasic` is the lowest Mathlib-free `hex` library: a home for small,
general-purpose helpers that clearly belong in the standard library and are
reproduced here so the library remains Mathlib-free. It provides reusable
`ExtTreeMap` merge/traversal operations, the shared
`List.foldl` algebra (`HexBasic.Fold`), reusable list lemmas (`HexBasic.List`),
the `Batteries` list lemmas reproduced in `HexBasic.ListShim`, the
`Vector.modify` update helper, and
kernel-reducible `Array`/`Vector` equality (`HexBasic.ArrayDecEq`) and
`ofFn` (`HexBasic.OfFn`), plus conditional reduction lemmas with names stable
across supported Lean versions (`HexBasic.Conditional`).

It also holds the shared exact-division contract (`HexBasic.ExactDiv`): the
total `exactDiv` wrapper with deterministic division by zero, the
`ExactDivLaws` package, and the coefficient-independent cancellation lemmas
that the fraction-free algorithms in `hex-resultant`, `hex-mv-gcd` and
`hex-poly-smith` share. (`hex-bareiss` solves the same problem one layer down,
against `HexArith.Int.exactDiv` on a fixed carrier, and does not depend on this
library.)
-/
