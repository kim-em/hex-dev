/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import VersoManual

import HexLLL.Basic

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

set_option pp.rawOnError true

#doc (Manual) "HexLLL: lattice basis reduction" =>
%%%
tag := "hex-lll"
%%%

# Introduction
%%%
tag := "hex-lll-intro"
%%%

Released as [hex-lll](https://github.com/leanprover/hex-lll), with the
Mathlib correspondence in
[hex-lll-mathlib](https://github.com/leanprover/hex-lll-mathlib).

`HexLLL` reduces an integer lattice basis. Given the rows of a
{name}`Hex.Matrix` over `Int`, it produces a new basis for the same
lattice made of short, nearly orthogonal vectors (the LLL guarantee).
Its first row is a provably short lattice vector, which is what the
{ref "hex-lll-cross-references"}[downstream factorization path] consumes:
the BHKS van Hoeij recombination step in `hex-berlekamp-zassenhaus`
reconstructs true factors from short vectors of a knapsack lattice.

On adversarial worst-case input the payoff of the design is stark. These are the
five benchmarked reducers on fplll's Ajtai-style `gen_trg` bases, whose steeply
decreasing profile forces a `Θ(d² log B)` swap count:

![HexLLL reducers on Ajtai-style worst-case bases](https://kim-em.github.io/hex-dev/figures/hex-lll-comparator-ajtai.svg)

The exact integer reducers (Lean's `lllNative` and the verified Isabelle
extraction) blow up `~d⁷`, while the certified path — an `fpLLL` candidate
checked by a verified Lean checker — stays cheap, near raw floating-point speed.
The {ref "hex-lll-performance"}[performance comparison] below walks through every
curve and all six input families.

The library splits computation from proof. The public reducer can
accelerate through an optional external `fpLLL` provider — fast, untrusted
numerics — but no proof depends on those numerics being correct. Every
external candidate is fed through a verified integer checker; only a basis
the checker accepts is returned, and the checker's soundness theorem
(proved on the Mathlib side) turns that acceptance into the mathematical
guarantee. When no external candidate certifies, the exact all-integer
reducer `lllNative` runs directly, and its guarantee is proved outright.

`HexLLL` is Mathlib-free. It takes the Gram-Schmidt machinery underlying
both the predicates and the checkers from
{ref "hex-lll-cross-references"}[`HexGramSchmidt`], which computes the
leading integer Gram determinants by fraction-free (Bareiss) elimination and
so rests in turn on `HexBareiss`, `HexDeterminant`, and `HexRowReduce`.

# Lattices and reducedness
%%%
tag := "hex-lll-predicates"
%%%

A lattice is the set of integer combinations of the basis rows. Membership
and independence are the two structural predicates; both are propositions
about the exact integer data, never about the numerics.

{docstring Hex.Matrix.memLattice}

{docstring Hex.Matrix.independent}

The central specification is the `(δ, η)`-reducedness predicate. It is the
classical LLL definition phrased over the exact rational Gram-Schmidt
coefficients of the integer `GramSchmidt.Int` representation: a
size-reduction bound `η` on every below-diagonal coefficient, together with
the Lovász condition at each adjacent pair, controlled by the parameter
`δ`.

{docstring Hex.isLLLReduced}

Reducedness in this squared-coefficient form relaxes monotonically as the
size bound `η` grows.

{docstring Hex.Internal.isLLLReduced.mono_η}

The payoff theorem is the short-vector bound: in a reduced basis the first
row is within an explicit `δ`/`η`-dependent factor of the shortest nonzero
lattice vector. This is the property downstream callers actually rely on.

{docstring Hex.short_vector_bound_of_size_bound}

# Verified integer checkers
%%%
tag := "hex-lll-checkers"
%%%

The predicates above mention rational Gram-Schmidt data; deciding them
directly would require rational (or interval) arithmetic. The checkers
instead work over the scaled integer Gram-Schmidt representation (the
leading Gram determinants `d` and the integer scaled coefficients `ν`),
so a `Bool` answer needs only exact integer comparisons. The base checker
clears denominators in both the size-reduced and Lovász clauses.

{docstring Hex.lllReducedInt}

For larger inputs an unverified fixed-precision interval pass is usually
faster; the dispatching checker uses a size predictor to choose it, but
always keeps the exact integer checker as a mandatory fallback when the
interval pass is indecisive, so completeness stays structural rather than
numerical.

{docstring Hex.lllReducedCheck}

The same-lattice side of an external candidate is certified separately. A
pair of integer transforms `U`, `V` witnessing `U·B = B'` and `V·B' = B`
proves the two bases generate the same lattice; the certificate is a
denominator-free `Bool` check with an overflow-safe packed-row comparison.

{docstring Hex.Matrix.sameLatticeCert}

{docstring Hex.Matrix.sameLatticeCert_sound}

The full external-candidate check composes the same-lattice certificate
with the reducedness checker.

{docstring Hex.certCheck}

# The reduction entry points
%%%
tag := "hex-lll-reduction"
%%%

The reducer state is the proof-facing {name}`Hex.Internal.LLLState`, which holds
the exact integer basis together with the scaled Gram-Schmidt data, and a
separate {name}`Hex.Internal.LLLState.Valid` predicate relates that data to the
`GramSchmidt.Int` representation, keeping the state updates computational while
letting the Mathlib side reason about them.

{docstring Hex.Internal.LLLState}

{docstring Hex.Internal.LLLState.Valid}

The exact all-integer reducer {name}`Hex.lllNative` drives the standard LLL
outer loop — integer size-reduction and adjacent Lovász swaps — from that exact
`d`/`ν` data alone. Its size-reduction step produces exact `|μ| ≤ 1/2`, so it
carries the classical `η = 1/2` contract and is the direct `1/4 < δ` entry
point.

{docstring Hex.lllNative}

The public entry point hides all of this behind one signature. Given a
basis with independent rows and `δ` in the classical range, it returns a
reduced basis generating the same lattice; the short-vector and same-lattice
post-conditions are identical on every internal path, so callers and proofs
never see the dispatch.

{docstring Hex.lll}

The canonical consumer surface reads short vectors off the reduced basis.
{name}`Hex.lll.firstShortVector` is the single short vector wanted by
recombination; {name}`Hex.lll.shortVectors` exposes the whole reduced
basis as an ordered candidate list. Each has a proof-free `Unchecked`
variant that drops the independence hypothesis for quick experimentation.

{docstring Hex.lll.firstShortVector}

{docstring Hex.lll.shortVectors}

# Certified external dispatch
%%%
tag := "hex-lll-dispatch"
%%%

When an external `fpLLL` provider is linked in, {name}`Hex.Internal.LLLProvider.dispatch`
asks it for a reduced basis and validates the answer with {name}`Hex.certCheck`
before trusting it. A rejected or absent provider yields `none`, and the
caller falls through to the native path, so the foreign reducer can speed
things up but can never compromise correctness.

{docstring Hex.Internal.LLLProvider.dispatch}

An accepted dispatch result comes with the integer transforms witnessing
its certificate, the single fact the certified-dispatch path of
{name}`Hex.lll` depends on.

{docstring Hex.Internal.LLLProvider.dispatch_some_certCheck}

# Performance comparison
%%%
tag := "hex-lll-performance"
%%%

`HexLLL` is benchmarked against the verified Isabelle `LLL_Basis_Reduction`
extraction and the unverified floating-point `fpLLL`, across six input families
that each stress a different cost. Here is `harsh-cubic`, where the entry
bit-length grows with the dimension:

![HexLLL harsh-cubic comparator](https://kim-em.github.io/hex-dev/figures/hex-lll-comparator-harsh-cubic.svg)

## The five curves

Each plot is log-scale wall-time per reduction against the family dimension:

* `fpLLL` — the raw floating-point reducer, unverified; the speed baseline.
* `Lean native` — `Hex.lllNative`, the exact all-integer `d`/`ν` reducer.
  Correct by construction, but its exact arithmetic pays for wide operands and
  high swap counts.
* `Lean certified` — an `fpLLL` candidate *checked* by the verified Lean checker
  `Hex.certCheck`. It inherits floating-point speed and adds only a cheap
  integer check, so it hugs the `fpLLL` curve while remaining fully verified.
* `verified Isabelle native` — the Isabelle extraction's own reducer; the
  independent verified point of comparison.
* `verified Isabelle certified` — the *same* `fpLLL` candidate checked by the
  Isabelle checker instead of the Lean one; the apples-to-apples yardstick for
  the Lean certified path.

## The six input families

Each family is a faithful port of an fplll generator, and stresses a different
part of the algorithm:

* `random-bounded` — near-orthogonal random bases; the easy baseline, few swaps.
* `harsh-cubic` — entries of bit-length about `3.3·n`; exact-integer
  operand-width growth (shown above).
* `ajtai` — fplll `gen_trg` worst-case triangular bases; the swap / iteration
  count `Θ(d² log B)` (shown in the {ref "hex-lll-intro"}[introduction]).
* `q-ary` — LWE/SIS bases `[[I, H], [0, qI]]`; the cryptographic Z-shape.
* `ntru` — bases `[[I, Rot h], [0, qI]]`; a planted dense sublattice plus a
  q-block.
* `knapsack` — the rectangular `d × (d+1)` integer-relation form; the only
  family with more columns than rows, exercising the `m > n` construction.

Across every family the exact reducers are correct but climb steeply on the hard
bases, while `Lean certified` stays within about 1.2 to 2.5 times raw `fpLLL` —
verified output at close to floating-point cost.

## Selecting the certified versus native path

This is a runtime choice, not a Lean import. `HexLLL` always builds its FFI
shim, and the *same* `Hex.lll` call picks its path by whether an external
provider symbol is resolvable in the process:

* set the environment variable `HEX_FPLLL_FFI_LIB` to a built fpLLL-ffi shared
  library and `lll` takes the certified path — the shim `dlopen`s it,
  `providerAvailable` returns true, and the candidate is certified by
  `Hex.certCheck`;
* leave it unset (or if certification ever fails) and `lll` runs the exact
  `Hex.lllNative` directly.

Either way the returned basis satisfies the same `(δ, 11/20)`-reduced contract.

## The size-reduction bound and its constants

The public `Hex.lll` certifies its output `(δ, 11/20)`-reduced: every
Gram-Schmidt coefficient satisfies `|μ| ≤ 11/20`. Two numbers in its signature
follow from `η = 11/20`. The precondition is `121/400 < δ`, because
`121/400 = (11/20)² = η²` and the bound is well-defined only when `η² < δ`; and
the short-vector constant is `1/(δ − 121/400)`. So the `121/400` stands exactly
where the classical bound would put `1/4 = (1/2)²`.

Why `11/20` rather than the classical `1/2`? Solely the external provider. The
exact `Hex.lllNative` already lands at `|μ| ≤ 1/2`, but a black-box reducer
cannot be forced to exactly `1/2` (fpLLL's default size-reduction target sits
slightly above it), so the certified path accepts its candidate at the looser
`11/20`. When you want the tighter guarantee, call `Hex.lllNative` directly: its
short-vector theorem `lllNative_short_vector` carries the precondition
`1/4 < δ` and the strictly better constant `1/(δ − 1/4)`.

## The other families

The remaining comparator plots, for reference:

![ajtai](https://kim-em.github.io/hex-dev/figures/hex-lll-comparator-ajtai.svg)

![q-ary](https://kim-em.github.io/hex-dev/figures/hex-lll-comparator-q-ary.svg)

![ntru](https://kim-em.github.io/hex-dev/figures/hex-lll-comparator-ntru.svg)

![knapsack](https://kim-em.github.io/hex-dev/figures/hex-lll-comparator-knapsack.svg)

![random-bounded](https://kim-em.github.io/hex-dev/figures/hex-lll-comparator-random-bounded.svg)

# Worked example
%%%
tag := "hex-lll-worked"
%%%

The block reduces the rank-2 lattice with basis rows `(1, 12)` and
`(0, 1)`. The skewed first row is far from orthogonal; reduction returns
`(0, 1)`, `(1, 0)` (the two unit vectors), which generate the same
lattice and are as short as possible. Each `#guard` is checked when the
chapter builds.

```lean
open Hex Hex.Matrix Hex.Internal

namespace HexLLLChapterExample

-- B = [[1, 12], [0, 1]]: a skewed basis.
private def B : Matrix Int 2 2 :=
  Matrix.ofFn fun i j =>
    match i.val, j.val with
    | 0, 0 => 1
    | 0, 1 => 12
    | 1, 1 => 1
    | _, _ => 0

-- R = [[0, 1], [1, 0]]: the reduced basis.
private def R : Matrix Int 2 2 :=
  Matrix.ofFn fun i j =>
    match i.val, j.val with
    | 0, 1 => 1
    | 1, 0 => 1
    | _, _ => 0

-- U, V: the integer transforms witnessing that B
-- and R generate the same lattice (U·B = R,
-- V·R = B).
private def U : Matrix Int 2 2 :=
  Matrix.ofFn fun i j =>
    match i.val, j.val with
    | 0, 1 => 1
    | 1, 0 => 1
    | 1, 1 => -12
    | _, _ => 0

private def V : Matrix Int 2 2 :=
  Matrix.ofFn fun i j =>
    match i.val, j.val with
    | 0, 0 => 12
    | 0, 1 => 1
    | 1, 0 => 1
    | _, _ => 0

-- The δ = 3/4 preconditions for the exact reducer.
private theorem hlo : (1 / 4 : Rat) < 3 / 4 := by grind
private theorem hhi : (3 / 4 : Rat) ≤ 1 := by grind

-- Reduction turns the skewed basis into R.
#guard lllNative B (3 / 4) hlo hhi (by decide) = R

-- Its first row is a shortest lattice vector.
#guard ((lllNative B (3 / 4) hlo hhi (by decide)).row
          ⟨0, by decide⟩).toArray = #[0, 1]

-- The verified checker rejects the input basis
-- (not size-reduced) and accepts the output.
#guard lllReducedInt B (3 / 4) (11 / 20) = false
#guard lllReducedInt R (3 / 4) (11 / 20) = true

-- U, V certify that B and R share a lattice, and
-- certCheck combines that with reducedness of R.
#guard Matrix.sameLatticeCert B R U V = true
#guard certCheck B R U V (3 / 4) (11 / 20) = true

end HexLLLChapterExample
```

# Cross-references
%%%
tag := "hex-lll-cross-references"
%%%

`HexLLL`'s substantive dependency is `HexGramSchmidt`, with its correctness
proofs in `HexLLLMathlib`:

* `HexGramSchmidt` supplies the integer Gram-Schmidt representation
  ({name}`Hex.GramSchmidt.Int.independent`, the scaled coefficients, and
  the leading Gram determinants) on which both the
  {ref "hex-lll-predicates"}[reducedness predicates] and the
  {ref "hex-lll-checkers"}[integer checkers] are defined. Through it,
  `HexLLL` rests transitively on the fraction-free integer determinant stack
  (`HexBareiss`, `HexDeterminant`, `HexRowReduce`).
* `HexLLLMathlib` carries the soundness theorems. `lllReducedInt_sound`
  and `lllReducedCheck_sound` relate the integer checkers to
  {name}`Hex.isLLLReduced`, and `certCheck_sound` combines those with
  {name}`Hex.Matrix.sameLatticeCert_sound` into the property triple (same
  lattice, independence, reducedness) that the certified-dispatch path of
  {name}`Hex.lll` relies on. `HexLLL` itself is Mathlib-free.
