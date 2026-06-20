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

`HexLLL` is the executable lattice-reduction layer of the stack. Given an
integer basis — the rows of a {name}`Hex.Matrix` over `Int` — it produces a
new basis generating the *same* integer lattice but made of short, nearly
orthogonal vectors, the LLL guarantee. Its first row is a provably short
lattice vector, which is the service the
{ref "hex-lll-cross-references"}[downstream factorization path] consumes:
the BHKS van Hoeij recombination step in `hex-berlekamp-zassenhaus`
reconstructs true factors from short vectors of a knapsack lattice.

The library is built around a strict computational/proof split. The
reduction itself runs through fast, untrusted numerics (a floating-point
steering pass, and optionally an external `fpLLL` provider), but no proof
ever depends on those numerics being correct. Instead every reduced basis
is fed through a *verified integer checker*; only a basis the checker
accepts is returned, and the checker's soundness theorem — proved on the
Mathlib side — turns that acceptance into the real mathematical guarantee.
This chapter follows that arc: first the predicates that *define* a reduced
basis, then the integer checkers that *decide* them, then the reduction
{ref "hex-lll-reduction"}[entry points] that produce candidates, and
finally the {ref "hex-lll-dispatch"}[certified dispatch] that ties the two
together.

`HexLLL` is Mathlib-free and depends only on {ref "hex-lll-cross-references"}[`HexGramSchmidt`] for the
Gram-Schmidt machinery underlying both the predicates and the checkers.

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

{docstring Hex.isLLLReduced.mono_η}

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
instead work over the *scaled integer* Gram-Schmidt representation — the
leading Gram determinants `d` and the integer scaled coefficients `ν` — so
a `Bool` answer needs only exact integer comparisons. The base checker
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

The reducer carries two pieces of state. The proof-facing
{name}`Hex.LLLState` holds the exact integer basis together with the scaled
Gram-Schmidt data, and a separate {name}`Hex.LLLState.Valid` predicate ties
that data back to the `GramSchmidt.Int` representation — keeping the state
updates purely computational while letting the Mathlib layer reason about
them.

{docstring Hex.LLLState}

{docstring Hex.LLLState.Valid}

The hot path runs over a floating-point state instead. Its integer basis is
the only proof-relevant field; the `Float` Gram-Schmidt approximations
steer the swap trajectory but never enter a proof.

{docstring Hex.SteeredState}

{docstring Hex.steeredReduce}

`steeredReduce` is a heuristic with no standalone guarantee, so it is never
returned raw. {name}`Hex.lllSteered` runs it, checks the candidate with
{name}`Hex.lllReducedCheck`, and falls back to the exact integer reducer if
the check fails — so its output is always certified `(δ, 11/20)`-reduced.

{docstring Hex.lllSteered}

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

When an external `fpLLL` provider is linked in, {name}`Hex.LLLProvider.dispatch`
asks it for a reduced basis and validates the answer with {name}`Hex.certCheck`
before trusting it. A rejected or absent provider yields `none`, and the
caller falls through to the native path — so the foreign reducer is a
performance accelerator that can never compromise correctness.

{docstring Hex.LLLProvider.dispatch}

An accepted dispatch result comes with the integer transforms witnessing
its certificate, the single fact the certified-dispatch path of
{name}`Hex.lll` depends on.

{docstring Hex.LLLProvider.dispatch_some_certCheck}

# Worked example
%%%
tag := "hex-lll-worked"
%%%

The block below reduces the rank-2 lattice with basis rows `(1, 12)` and
`(0, 1)`. The skewed first row is far from orthogonal; reduction returns
the basis `(0, 1)`, `(1, 0)` — the two unit vectors, which generate the
same lattice and are as short as possible. Every `#guard` is checked when
the chapter is built, so the outputs are guaranteed to match the executable
implementation.

```lean
open Hex Hex.Matrix

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

-- Reduction turns the skewed basis into R.
#guard steeredReduce B (3 / 4) = R

-- Its first row is a shortest lattice vector.
#guard ((steeredReduce B (3 / 4)).row
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

`HexLLL` sits one layer above the Gram-Schmidt machinery and one boundary
away from its correctness proofs:

* `HexGramSchmidt` supplies the integer Gram-Schmidt representation —
  {name}`Hex.GramSchmidt.Int.independent`, the scaled coefficients, and the
  leading Gram determinants — on which both the {ref "hex-lll-predicates"}[reducedness
  predicates] and the {ref "hex-lll-checkers"}[integer checkers] are
  defined. `HexLLL` is its only direct dependency.
* `HexLLLMathlib` is the correspondence library carrying the soundness
  theorems. `lllReducedInt_sound` and `lllReducedCheck_sound` bridge the
  integer checkers to {name}`Hex.isLLLReduced`, and `certCheck_sound`
  combines those with {name}`Hex.Matrix.sameLatticeCert_sound` into the
  property triple (same lattice, independence, reducedness) that the
  certified-dispatch path of {name}`Hex.lll` relies on. The Mathlib
  dependency lives entirely on that side of the boundary; `HexLLL` itself
  is Mathlib-free.
