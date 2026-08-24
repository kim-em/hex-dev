/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import VersoManual

import HexBasic

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

set_option pp.rawOnError true

#doc (Manual) "HexBasic: shared dependency-free utilities" =>
%%%
tag := "hex-basic"
%%%

# Introduction
%%%
tag := "hex-basic-intro"
%%%

`HexBasic` is the lowest computational library in Hex. It collects small,
general-purpose definitions that several otherwise independent libraries
need, while importing only Lean and Std. Keeping these utilities here avoids
both duplicated implementations and dependencies between unrelated algebra
libraries.

The library supplies kernel-reducible array and vector construction,
reusable list-fold algebra, deletion-capable ordered-map merges, a shared
exact-division contract, deterministic bounded randomness, and small
compatibility lemmas. Everything is Mathlib-free and executable in Lean.

# Kernel-reducible containers
%%%
tag := "hex-basic-containers"
%%%

Lean's standard array tabulator is efficient in compiled code, but one of its
implementation helpers is opaque across module boundaries. The primed Hex
versions use an exposed list tabulation for kernel reduction and redirect
compiled code back to the standard implementations with `@[csimp]`.

{docstring Hex.Array.ofFn'}

{docstring Hex.Vector.ofFn'}

The accompanying simplification lemmas identify the primed constructors with
their standard counterparts, so ordinary container lemmas remain available.
`HexBasic` also provides kernel-reducible equality for arrays and vectors and
the usual pointwise laws for {name}`Vector.modify`.

# Ordered-map traversal and merging
%%%
tag := "hex-basic-tree-maps"
%%%

The additions to {name}`Std.ExtTreeMap` are representation-independent
building blocks used by sparse polynomial and other canonical-map code.

{docstring Std.ExtTreeMap.foldl₂}

{docstring Std.ExtTreeMap.mergeWith?}

`foldl₂` presents left-only, shared, and right-only entries in key order.
`mergeWith?` retains unmatched entries and lets the collision callback update
or delete a shared key. Its lookup theorem is the public specification, so
callers do not need to unfold the tree traversal.

{docstring Std.ExtTreeMap.getElem?_mergeWith?}

# Exact division
%%%
tag := "hex-basic-exact-division"
%%%

Fraction-free algorithms need a coefficient-independent way to say that a
division operation cancels a known nonzero factor. The law package isolates
that assumption from the executable wrapper.

{docstring Hex.ExactDivLaws}

{docstring Hex.exactDiv}

The zero denominator has a deterministic value, while the nonzero branch is
the carrier's ordinary division. Integers and lightweight fields provide the
standard instances.

```lean
open Hex

#guard exactDiv (21 : Int) 3 = 7
#guard exactDiv (21 : Int) 0 = 0
```

# Deterministic bounded randomness
%%%
tag := "hex-basic-randomness"
%%%

{docstring Hex.Rand}

{docstring Hex.Rand.next}

{docstring Hex.Rand.nat}

The state is explicit and reproducible. Bounded draws use rejection sampling,
return the advanced state, and consume explicit fuel; they never introduce
global randomness or an unbounded search. The generator is suitable for Las
Vegas algorithm scheduling, not cryptography.

```lean
open Hex

namespace HexBasicChapter

#guard (Rand.ofSeed 0).next.1 = 0xe220a8397b1dcdaf
#guard ((Rand.ofSeed 1).nat 10 8).isOk

end HexBasicChapter
```

# Fold and compatibility lemmas
%%%
tag := "hex-basic-folds"
%%%

The `List.foldl` lemmas expose algebraic transformations used repeatedly by
coefficient convolutions and finite sums: congruence, permutation invariance,
distribution over addition and subtraction, and bounds for additive or
maximum folds. Small conditional and list lemmas carry stable Hex names where
the supported Lean versions differ.

# Verification boundary
%%%
tag := "hex-basic-verification"
%%%

All correctness statements are proved in Lean. The module-boundary tests
exercise array construction, vector updates, tree-map operations, exact
division, and deterministic randomness after importing the public umbrella,
so accidental opacity is caught by the ordinary build. `HexBasic` uses no
external oracle and introduces no native runtime dependency.
