/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import VersoManual

import HexLLL.Basic
import HexMatrix

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

On adversarial worst-case input the reducers diverge sharply in cost. These are the
five benchmarked reducers on fplll's Ajtai-style `gen_trg` bases, whose steeply
decreasing profile forces a `Θ(d² log B)` swap count:

![HexLLL reducers on Ajtai-style worst-case bases](https://kim-em.github.io/hex-dev/figures/hex-lll-comparator-ajtai.svg)

The exact integer reducers (Lean's `lllNative` and the verified Isabelle
extraction) blow up `~d⁷`. The certified path (an `fpLLL` candidate
checked by a verified Lean checker) stays cheap, near raw floating-point speed.
The {ref "hex-lll-performance"}[performance comparison] below describes every
curve and all six input families.

The library splits computation from proof. The public reducer can
accelerate through an optional external `fpLLL` provider (fast, untrusted
numerics), but no proof depends on those numerics being correct. Every
external candidate is fed through a verified integer checker. Only a basis
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
and independence are the two structural predicates. Both are propositions
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

The key theorem is the short-vector bound: in a reduced basis the first
row is within an explicit `δ`/`η`-dependent factor of the shortest nonzero
lattice vector. This is the property downstream callers actually rely on.

{docstring Hex.short_vector_bound_of_size_bound}

# Verified integer checkers
%%%
tag := "hex-lll-checkers"
%%%

The predicates above mention rational Gram-Schmidt data. Deciding them
directly would require rational (or interval) arithmetic. The checkers
instead work over the scaled integer Gram-Schmidt representation (the
leading Gram determinants `d` and the integer scaled coefficients `ν`),
so a `Bool` answer needs only exact integer comparisons. The base checker
clears denominators in both the size-reduced and Lovász clauses.

{docstring Hex.lllReduced}

The exact integer checker is complete, but its operands grow with the
input. For larger inputs an unverified fixed-precision interval pass over
the same integer data is usually faster at deciding reducedness, so the
dispatching checker uses a cheap size predictor to pick between the two,
always keeping the exact integer checker as a mandatory fallback when the
interval pass is indecisive; completeness therefore stays structural
rather than numerical. This is a choice between two *checkers* for a
basis already in hand, and is independent of how that basis was reduced.

{docstring Hex.lllReducedCheck}

Reducedness is only half of what an external candidate needs. We certify
separately that the external certificate applies to the original input
lattice: a pair of integer transforms `U`, `V` witnessing `U·B = B'` and
`V·B' = B` proves the two bases generate the same lattice. The
certificate is a denominator-free `Bool` check with a packed-row
comparison.

{docstring Hex.Matrix.sameLatticeCert}

{docstring Hex.Matrix.sameLatticeCert_sound}

The full external-candidate check composes the same-lattice certificate
with the reducedness checker.

{docstring Hex.certCheck}

# The reduction entry points
%%%
tag := "hex-lll-reduction"
%%%

The exact all-integer reducer {name}`Hex.lllNative` drives the standard LLL
outer loop — integer size-reduction and adjacent Lovász swaps — directly on
the exact `d`/`ν` Gram-Schmidt data. Its size-reduction step produces exact
`|μ| ≤ 1/2`, so it satisfies the classical `η = 1/2` bound and is the direct
`1/4 < δ` entry point.

{docstring Hex.lllNative}

The public entry point unifies two internal paths behind one signature.
Given a basis with independent rows and `δ` in the classical range,
{name}`Hex.lll` returns a reduced basis for the same lattice. It gets there
either by running `lllNative` directly, or, when an external `fpLLL` provider
is available at runtime, by certifying the provider's candidate with the
verified checker and returning that instead (the
{ref "hex-lll-dispatch"}[next section] describes the switch). Accepting a
black-box candidate is what forces the slightly weaker `η = 11/20` bound
described below; both paths meet the same short-vector and same-lattice
post-conditions, so callers and proofs never see which one ran.

{docstring Hex.lll}

## The size-reduction bound and its constants
%%%
tag := "hex-lll-bound"
%%%

The public `Hex.lll` certifies its output `(δ, 11/20)`-reduced: every
Gram-Schmidt coefficient satisfies `|μ| ≤ 11/20`. Two numbers in its signature
follow from `η = 11/20`. The precondition is `121/400 < δ`, because
`121/400 = (11/20)² = η²` and the bound is well-defined only when `η² < δ`. The
short-vector constant is `1/(δ − 121/400)`. So the `121/400` stands exactly
where the classical bound would put `1/4 = (1/2)²`.

Why `11/20` rather than the classical `1/2`? Solely the external provider. The
exact `Hex.lllNative` already lands at `|μ| ≤ 1/2`, but a black-box reducer
cannot be forced to exactly `1/2` (fpLLL's default size-reduction target sits
slightly above it), so the certified path accepts its candidate at the looser
`11/20`. When you want the tighter guarantee, call `Hex.lllNative` directly: its
short-vector theorem `lllNative_short_vector` carries the precondition
`1/4 < δ` and the strictly better constant `1/(δ − 1/4)`.

## Short vectors
%%%
tag := "hex-lll-short-vectors"
%%%

Two functions read the short vectors off the reduced basis.
{name}`Hex.lll.firstShortVector` is the single short vector used by
recombination. {name}`Hex.lll.shortVectors` returns the whole reduced
basis as an ordered candidate list.

{docstring Hex.lll.firstShortVector}

{docstring Hex.lll.shortVectors}

Each has a counterpart under the {name}`Hex.lllNative` namespace.
{name}`Hex.lllNative.firstShortVector` and {name}`Hex.lllNative.shortVectors`
call `lllNative` directly, so they take the tighter native precondition
`1/4 < δ` and skip the provider dispatch and its certification. They also omit
the `b.independent` hypothesis — and this is the key point: independence is a
precondition of the *theorems* about the output, not of the *computation*. The
reducer runs on any input; the native-namespace variants simply forgo the
reduced-basis guarantees, so you get the reduced rows back without having to
discharge an independence proof. That is what makes them convenient for quick
experimentation.

{docstring Hex.lllNative.firstShortVector}

{docstring Hex.lllNative.shortVectors}

# Certified external dispatch
%%%
tag := "hex-lll-dispatch"
%%%

By default `Hex.lll` runs the exact `Hex.lllNative`. To let it accelerate
through the external `fpLLL` provider instead, call {name}`Hex.lll.loadProvider`
with the path to a built fpLLL-ffi shared library
(`scripts/oracle/setup_fplll_ffi.sh` builds one and prints its path); it
`dlopen`s the library, installs it as the process provider, and returns `true`
on success. {name}`Hex.lll.providerActive` reports whether one is installed.
This is a runtime switch, not a matter of importing a different module —
`HexLLL` always links its small provider shim, and the *same* `Hex.lll` call
takes the certified path exactly when a provider is installed. Loading is an
explicit, discoverable Lean action next to `lll`: there is no environment
variable read on the `lll` path and no implicit `dlopen`.

Either way the result is `(δ, 11/20)`-reduced. When the provider is in use,
`Hex.lll` asks it for a reduced basis and re-checks the candidate with
{name}`Hex.certCheck` before returning it; a candidate the checker rejects,
or an absent provider, falls straight through to the native reducer. The
foreign numerics can therefore speed things up but can never affect
correctness: nothing the provider returns is trusted until the verified
integer checker has accepted it.

{docstring Hex.lll.loadProvider}

{docstring Hex.lll.providerActive}

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

* `fpLLL`: the raw floating-point reducer, unverified; the speed baseline.
* `Lean native`: `Hex.lllNative`, the exact all-integer `d`/`ν` reducer.
  Correct by construction, but its exact arithmetic pays for wide operands and
  high swap counts.
* `Lean certified`: an `fpLLL` candidate *checked* by the verified Lean checker
  `Hex.certCheck`. It inherits floating-point speed and adds only a cheap
  integer check, so it stays close to the `fpLLL` curve while remaining fully
  verified.
* `verified Isabelle native`: the Isabelle extraction's own reducer; the
  independent verified point of comparison.
* `verified Isabelle certified`: the *same* `fpLLL` candidate checked by the
  Isabelle checker instead of the Lean one; the apples-to-apples yardstick for
  the Lean certified path.

## The six input families

Each family is a faithful port of an fplll generator, and stresses a different
part of the algorithm:

* `random-bounded`: near-orthogonal random bases; the easy baseline, few swaps.
* `harsh-cubic`: entries of bit-length about `3.3·n`; exact-integer
  operand-width growth (shown above).
* `ajtai`: fplll `gen_trg` worst-case triangular bases; the swap / iteration
  count `Θ(d² log B)` (shown in the {ref "hex-lll-intro"}[introduction]).
* `q-ary`: LWE/SIS bases `[[I, H], [0, qI]]`; the cryptographic Z-shape.
* `ntru`: bases `[[I, Rot h], [0, qI]]`; a planted dense sublattice plus a
  q-block.
* `knapsack`: the rectangular `d × (d+1)` integer-relation form; the only
  family with more columns than rows, using the `m > n` construction.

Across every family the exact reducers are correct but climb steeply on the hard
bases, while `Lean certified` stays within about 1.2 to 2.5 times raw `fpLLL`:
verified output at close to floating-point cost. Selecting the certified
versus native path is the runtime switch described under
{ref "hex-lll-dispatch"}[Certified external dispatch]; the `η = 11/20`
constants both paths report are explained under
{ref "hex-lll-bound"}[the size-reduction bound].

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
`(0, 1)`. The skewed first row is far from orthogonal. Reduction returns
`(0, 1)`, `(1, 0)` (the two unit vectors), which generate the same
lattice and are as short as possible.

```lean
open Hex Hex.Matrix

namespace HexLLLChapterExample

-- B = [[1, 12], [0, 1]]: a skewed basis.
private def B : Hex.Matrix Int 2 2 := #m[1, 12; 0, 1]

-- R = [[0, 1], [1, 0]]: the reduced basis.
private def R : Hex.Matrix Int 2 2 := #m[0, 1; 1, 0]

-- U, V: the integer transforms witnessing that B
-- and R generate the same lattice (U·B = R, V·R = B).
private def U : Hex.Matrix Int 2 2 := #m[0, 1; 1, -12]

private def V : Hex.Matrix Int 2 2 := #m[12, 1; 1, 0]

-- The δ = 3/4 preconditions for the exact reducer.
private theorem hlo : (1 / 4 : Rat) < 3 / 4 := by grind
private theorem hhi : (3 / 4 : Rat) ≤ 1 := by grind

-- Reduction turns the skewed basis into R.
#guard lllNative B (3 / 4) hlo hhi (by decide) = R

-- Its first row is a shortest lattice vector.
#guard (lllNative B (3 / 4) hlo hhi (by decide)).row
    ⟨0, by decide⟩ = #v[0, 1]

-- The verified checker rejects the input basis
-- (not size-reduced) and accepts the output.
#guard lllReduced B (3 / 4) (11 / 20) = false
#guard lllReduced R (3 / 4) (11 / 20) = true

-- U, V certify that B and R share a lattice, and
-- certCheck combines that with reducedness of R.
#guard Matrix.sameLatticeCert B R U V = true
#guard certCheck B R U V (3 / 4) (11 / 20) = true

end HexLLLChapterExample
```

## Recovering a minimal polynomial from a decimal

A short vector of a well-chosen lattice recovers an integer relation among
real numbers. The classic application is guessing the minimal polynomial
of an algebraic number from a numerical approximation. Take the decimal
`α = 1.220744…`, and suppose all we know is that it is a root of some monic
integer polynomial of degree at most four — but not which one.

Scale the powers `1, α, α², α³, α⁴` by `C = 10⁶` and round to integers. The
lattice has one row per power: an identity block that remembers the
coefficient, and a last column holding the scaled power. A combination
`Σ aᵢ · rowᵢ` has last coordinate `≈ C · Σ aᵢ αⁱ`, which is tiny exactly
when `Σ aᵢ αⁱ ≈ 0` — that is, when the `aᵢ` are the coefficients of a
polynomial that `α` nearly satisfies. LLL finds the shortest such vector.

```lean
open Hex Hex.Matrix

namespace HexLLLMinPoly

-- One row per power of α: eᵢ in the first five columns,
-- round(10⁶ · αⁱ) in the last, for i = 0..4.
private def L : Hex.Matrix Int 5 6 :=
  #m[1, 0, 0, 0, 0, 1000000;
     0, 1, 0, 0, 0, 1220744;
     0, 0, 1, 0, 0, 1490216;
     0, 0, 0, 1, 0, 1819173;
     0, 0, 0, 0, 1, 2220744]

private theorem hlo : (1 / 4 : Rat) < 3 / 4 := by grind
private theorem hhi : (3 / 4 : Rat) ≤ 1 := by grind

-- The shortest reduced row reads off the coefficients
-- (a₀, a₁, a₂, a₃, a₄) = (-1, -1, 0, 0, 1) with a zero
-- last coordinate: the relation -1 - α + α⁴ = 0, i.e.
-- the minimal polynomial x⁴ - x - 1.
#guard (lllNative L (3 / 4) hlo hhi (by decide)).row
    ⟨0, by decide⟩ = #v[-1, -1, 0, 0, 1, 0]

end HexLLLMinPoly
```

The last coordinate comes out exactly zero, not merely small: because
`α⁴ = α + 1` holds exactly and `C` is an integer, the rounded scaled powers
satisfy `round(C·α⁴) − round(C·α) − round(C) = 0` on the nose. So the
recovered vector is a genuine lattice element, and its first five entries
`(-1, -1, 0, 0, 1)` are the coefficients of `x⁴ − x − 1`.

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
  `HexLLL` rests transitively on the fraction-free integer determinant
  libraries `HexBareiss`, `HexDeterminant`, and `HexRowReduce`.
* `HexLLLMathlib` carries the soundness theorems. `lllReduced_sound`
  and `lllReducedCheck_sound` relate the integer checkers to
  {name}`Hex.isLLLReduced`, and `certCheck_sound` combines those with
  {name}`Hex.Matrix.sameLatticeCert_sound` into the property triple (same
  lattice, independence, reducedness) that the certified-dispatch path of
  {name}`Hex.lll` relies on. `HexLLL` itself is Mathlib-free.
