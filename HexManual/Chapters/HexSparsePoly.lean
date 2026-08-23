/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import VersoManual

import HexSparsePolyMathlib

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

set_option pp.rawOnError true

#doc (Manual) "HexSparsePoly: sparse univariate polynomials" =>
%%%
tag := "hex-sparse-poly"
%%%

# Introduction
%%%
tag := "hex-sparse-poly-intro"
%%%

`HexSparsePoly` provides canonical sparse univariate polynomials: a
polynomial is a sorted array of `(exponent, coefficient)` terms with
strictly increasing exponents and no stored zero coefficient. Costs
scale with the number of stored terms rather than the degree, so a
two-term polynomial of degree one million is two array entries. The
representation is canonical, so equality is structural and decidable.

The executable library is Mathlib-free. It depends on `HexBasic` for
array equality and fold algebra, and on {ref "hex-poly"}[`HexPoly`] for
the dense representation it converts to and from. It is a second
representation next to `Hex.DensePoly`, not a replacement: callers name
the representation they hold and convert explicitly, because the same
named operation can differ in cost by a factor of the degree between
the two. `HexSparsePolyMathlib`, described in
{ref "hex-sparse-poly-mathlib"}[the correspondence section], identifies
the type with Mathlib's `Polynomial R`.

# The representation
%%%
tag := "hex-sparse-poly-representation"
%%%

{docstring Hex.SparsePoly}

{docstring Hex.SparsePolyCanonical}

Coefficient access is the semantic anchor: every equality of sparse
polynomials reduces to coefficient extensionality, and the canonical
invariant makes the stored exponents exactly the nonzero positions.

{docstring Hex.SparsePoly.coeff}

{docstring Hex.SparsePoly.mem_support_iff}

Construction goes through {name}`Hex.SparsePoly.ofTerms`, which accepts
arbitrary unsorted term arrays, combines duplicates in input order, and
drops cancellations; its compiled implementation is a stable
sort-and-combine selected by `@[csimp]`.

{docstring Hex.SparsePoly.ofTerms}

{docstring Hex.SparsePoly.addTerm}

{docstring Hex.SparsePoly.monomial}

# Arithmetic
%%%
tag := "hex-sparse-poly-arithmetic"
%%%

Addition is a linear merge of the two term lists; degree never appears
in the cost. Multiplication's kernel-facing specification forms all
pairwise products and canonicalises; the compiled implementation,
selected by measurement in the project's benchmarking phase, folds the
pairwise products into an `Std.ExtTreeMap` accumulator, which beat both
the sort-and-combine route and a Johnson-style heap merge by about
three times on low- and high-collision inputs alike.

{docstring Hex.SparsePoly.add}

{docstring Hex.SparsePoly.mul}

{docstring Hex.SparsePoly.mulMonomial}

{docstring Hex.SparsePoly.scale}

{docstring Hex.SparsePoly.pow}

The coefficient laws and the commutative-ring laws are proved under the
`Lean.Grind` algebra classes; `coeff_mul` and the multiplicative laws
are transported through the dense conversion.

{docstring Hex.SparsePoly.coeff_mul}

# Conversions
%%%
tag := "hex-sparse-poly-conversions"
%%%

The dense conversions are the boundary between the two representations
and the proof route for the multiplicative laws. `toDense` is the one
operation whose cost is governed by the degree.

{docstring Hex.SparsePoly.toDense}

{docstring Hex.SparsePoly.ofDense}

{docstring Hex.SparsePoly.toDense_mul}

Measured crossovers (recorded in the library SPEC): sparse addition
beats dense up to about `t ≈ n/8` stored terms at degree `n`, sparse
multiplication up to about `t ≈ n/4`, and sparse evaluation stays ahead
to at least `t ≈ n/6`.

# Evaluation and substitution
%%%
tag := "hex-sparse-poly-eval"
%%%

Evaluation is gap Horner: one pass over the stored terms with binary
powering across exponent gaps, `O(t)` coefficient multiplications plus
`O(t log (n/t))` squarings.

{docstring Hex.SparsePoly.eval}

{docstring Hex.SparsePoly.derivative}

{docstring Hex.SparsePoly.substPow}

{docstring Hex.SparsePoly.substScale}

{docstring Hex.SparsePoly.compose}

# The Euclidean layer
%%%
tag := "hex-sparse-poly-euclid"
%%%

Division and gcd route through the dense representation, and the
library makes no claim that they stay sparse: the cost is the dense
cost at the degree plus the conversions. The one division that stays
sparse is division by a monomial.

{docstring Hex.SparsePoly.divModMonic}

{docstring Hex.SparsePoly.divMod}

{docstring Hex.SparsePoly.gcd}

{docstring Hex.SparsePoly.divExactMonic?}

{docstring Hex.SparsePoly.divMonomial?}

# The Mathlib correspondence
%%%
tag := "hex-sparse-poly-mathlib"
%%%

Everything above is executable and Mathlib-free. `HexSparsePolyMathlib`
identifies the sparse representation with Mathlib's `Polynomial R`,
composing a ring equivalence with the dense representation and
`HexPolyMathlib`'s equivalence.

{docstring HexSparsePolyMathlib.denseEquiv}

{docstring HexSparsePolyMathlib.equiv}

The identification is exact, coefficient by coefficient, and the stored
exponents are exactly Mathlib's `support`, which is the sense in which
the representation is sparse.

{docstring HexSparsePolyMathlib.coeff_equiv}

{docstring HexSparsePolyMathlib.equiv_support}

One correspondence lemma per public operation transports evaluation,
differentiation, composition, and exponent substitution, alongside the
constructor and observer images.

{docstring HexSparsePolyMathlib.equiv_eval}

{docstring HexSparsePolyMathlib.equiv_derivative}

{docstring HexSparsePolyMathlib.equiv_compose}

{docstring HexSparsePolyMathlib.equiv_substPow}

# Cross-references
%%%
tag := "hex-sparse-poly-cross-references"
%%%

* {ref "hex-poly"}[`HexPoly`] supplies the dense representation behind
  the conversions and the Euclidean layer.
* `HexBasic/ArrayDecEq.lean` supplies the array equality instance the
  decidable equality routes through.
* `HexSparsePolyMathlib` is the proof boundary: it imports Mathlib,
  while `HexSparsePoly` and its executable consumers do not.
