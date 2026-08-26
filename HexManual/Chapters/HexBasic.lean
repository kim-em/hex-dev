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

Hex certificate checking runs `decide +kernel` over concrete arrays and
vectors, so the kernel has to reduce both array construction and array
equality. Under Lean's module system it does not, for three separate reasons.
{name}`Array.ofFn` delegates to an unexposed `ofFn.go`; core's
{name}`Array.instDecidableEq` delegates to an unexposed
{name}`Array.instDecidableEqImpl`; and {name}`Vector` gets its equality from
`deriving DecidableEq`, whose generated `decEq` is likewise unexposed. In each
case the callee's body is unavailable downstream, so reduction stalls on a term
the kernel can see but cannot unfold.

The workaround is the same in all three cases. Route through {name}`List`,
which is fully exposed and does reduce, and attach a `@[csimp]` lemma sending
compiled code back to the core definition. The list detour is then paid only in
the kernel, which is the one place it buys anything: {name}`Array.toList` is an
`O(n)` conversion that allocates in full and gives up early exit, so it is the
wrong shape for compiled code.

{docstring Hex.Array.ofFn'}

{docstring Hex.Vector.ofFn'}

The accompanying simplification lemmas identify the primed constructors with
their standard counterparts, so ordinary container lemmas remain available.

{docstring Hex.instDecidableEqArray}

{docstring Hex.instDecidableEqVector}

Both instances are `scoped`, so they take effect under `open scoped Hex` and
nowhere else, and never leak into a consumer that has not asked for them. A
module that forgets to open the scope gets a stuck `decide`, which is a loud
failure rather than a silent change of meaning.

These four definitions are shims, not API this library wants to own. When
[leanprover/lean4#14270](https://github.com/leanprover/lean4/pull/14270)
lands and the toolchain moves past it, core's own `ofFn` and equality reduce
in the kernel, the primed constructors and the priority instances go away, and
callers move back to the standard names. `HexBasic.ModuleBoundaryTests` is
what makes that removal checkable: it sits in a *separate* module from the
definitions it exercises, because a same-module test passes whether or not the
workaround is present and so proves nothing.

`HexBasic` also supplies an entrywise vector update with the pointwise read
law its callers reason with.

{docstring Vector.modify}

{docstring Vector.getElem_modify}

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

Nearly every library above this one reduces a list with a single operation:
`xs.foldl (fun acc x => acc + f x) z` for a coefficient convolution or a finite
sum, and its multiplicative twin for a product. A Mathlib-free library cannot
reach for `Finset.sum`, and the core lemmas about associative folds require
`Std.Associative` and `Std.LawfulIdentity` instances that a bare
`Lean.Grind.Semiring` does not carry. `HexBasic.Fold` supplies those instances
file-locally and states the algebra the libraries actually use, so the same
rearrangement is proved once rather than in each consumer.

The two most-used shapes pull the running accumulator out of a fold and factor
a scalar through one.

{docstring List.foldl_add_eq_add_foldl}

{docstring List.foldl_add_mul_left}

Reordering and reassociation matter because a sum indexed by an ordered map's
keys has no canonical order, and because coefficient convolutions are naturally
written as nested sums.

{docstring List.foldl_add_perm}

{docstring List.foldl_add_comm}

Bounds on `Nat` folds carry the degree and size arguments that termination and
size reasoning need.

{docstring List.le_foldl_max_of_mem}

```lean
namespace HexBasicFolds

-- The fold shape the lemmas above talk about.
def sum2 (z : Int) (xs : List Int) : Int :=
  xs.foldl (fun a i => a + 2 * i) z

-- The sum itself.
#guard sum2 0 [1, 2, 3] = 12
-- Reordering the list does not change it.
#guard sum2 0 [3, 1, 2] = 12
-- A nonzero start shifts it by exactly that much.
#guard sum2 5 [1, 2, 3] = 17

end HexBasicFolds
```

The conditional lemmas are naming rather than mathematics:
{name}`Hex.ite_eq_left` and its siblings give `if`-reduction stable Hex names
across the Lean versions the project supports, so an upstream rename is
absorbed here instead of rippling through the algebra libraries. `HexBasic`
also carries the handful of duplicate-freeness and lexicographic-comparison
list lemmas that the canonical-form libraries share.

# Verification boundary
%%%
tag := "hex-basic-verification"
%%%

All correctness statements are proved in Lean. The module-boundary tests
exercise array construction, vector updates, tree-map operations, exact
division, and deterministic randomness after importing the public umbrella,
so accidental opacity is caught by the ordinary build. `HexBasic` uses no
external oracle and introduces no native runtime dependency.

# Cross-references
%%%
tag := "hex-basic-cross-references"
%%%

`HexBasic` has no dependencies: it imports only Lean and Std, and sits at the
root of the library graph. Nothing depends on all of it, which is the point;
each consumer takes the one or two modules it needs.

* The {name}`Std.ExtTreeMap` merges are what
  {ref "hex-mv-poly"}[`HexMvPoly`] builds its canonical sparse representation
  on, with `HexMvHensel` reusing the same traversals.
* The kernel-reducible containers are taken by the libraries whose
  certificates are checked by `decide +kernel` over concrete arrays:
  {ref "hex-mv-poly"}[`HexMvPoly`],
  {ref "hex-sparse-poly"}[`HexSparsePoly`],
  {ref "hex-berlekamp-zassenhaus"}[`HexBerlekampZassenhaus`], and
  {ref "hex-real-roots"}[`HexRealRoots`].
* The exact-division contract is shared by the fraction-free algorithms:
  {ref "hex-resultant"}[`HexResultant`], `HexMvGcd`, and
  {ref "hex-poly-smith"}[`HexPolySmith`] each cancel a known nonzero factor
  through {name}`Hex.ExactDivLaws` rather than carrying their own division
  hypothesis. {ref "hex-bareiss"}[`HexBareiss`] solves the same problem one
  layer down, against `HexArith.Int.exactDiv` on a fixed carrier.
* The fold algebra travels with the multivariate stack, where sums are indexed
  by a map's keys: {ref "hex-mv-poly"}[`HexMvPoly`], `HexMvGcd`,
  `HexMvHensel`, and {ref "hex-resultant"}[`HexResultant`].
* `HexBasic` has no Mathlib companion, and needs none. Nothing here states a
  correspondence: these are Lean and Std facts that happen not to be upstream
  yet. The Mathlib bridges live in the consuming libraries' `*Mathlib`
  counterparts, which import both this library and Mathlib.
