/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import VersoManual

import HexMvPolyMathlib

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

set_option pp.rawOnError true

#doc (Manual) "HexMvPoly: executable sparse multivariate polynomials" =>
%%%
tag := "hex-mv-poly"
%%%

# Introduction
%%%
tag := "hex-mv-poly-intro"
%%%

`HexMvPoly` provides canonical sparse multivariate polynomials in a fixed
number of variables. A polynomial stores its nonzero coefficients in
monomial order, so equality is structural, iteration is ordered, and
leading terms are available without sorting at each use. The monomial
comparator is an explicit type parameter: callers can select lexicographic,
graded lexicographic, or graded reverse lexicographic order.

The executable library is Mathlib-free. It depends on `HexBasic` for its
tree-map and kernel-reduction support, and on
{ref "hex-poly"}[`HexPoly`] for the dense recursive view.
`HexMvPolyMathlib`, described in
{ref "hex-mv-poly-mathlib"}[the correspondence section], supplies the
ring equivalence with Mathlib's multivariate polynomials and the
proof-facing algebraic API.

# Monomials and storage order
%%%
tag := "hex-mv-poly-monomials"
%%%

An {name}`Hex.Mono` is a fixed-length vector of natural-number exponents.
The operations below are the building blocks for divisibility,
S-polynomials, variable maps, and evaluation.

{docstring Hex.Mono}

{docstring Hex.Mono.mul}

{docstring Hex.Mono.dvd}

{docstring Hex.Mono.div}

{docstring Hex.Mono.splits}

{docstring Hex.Mono.prod}

The named comparators {name}`Hex.Mono.lex`,
{name}`Hex.Mono.grlex`, and {name}`Hex.Mono.grevlex` are faithful total
orders. Each also satisfies {name}`Hex.IsMonomialOrder`, which adds the
least-monomial, multiplicative-compatibility, and well-foundedness laws
needed by leading-term and reduction algorithms.

{docstring Hex.IsMonomialOrder}

# The polynomial type
%%%
tag := "hex-mv-poly-type"
%%%

{name}`Hex.MvPoly` bundles an ordered tree map with the invariant that no
stored coefficient is zero. Duplicate terms are combined and
cancellations are deleted, leaving one representation for each
polynomial.

{docstring Hex.MvPoly}

The tree is an implementation detail. Construction and inspection go
through the following API:

{docstring Hex.MvPoly.monomial}

{docstring Hex.MvPoly.C}

{docstring Hex.MvPoly.X}

{docstring Hex.MvPoly.ofTerms}

{docstring Hex.MvPoly.coeff}

{docstring Hex.MvPoly.termsList}

{docstring Hex.MvPoly.foldTerms}

{docstring Hex.MvPoly.termCount}

The reusable map machinery is kept below the polynomial layer in
`HexBasic/ExtTreeMap.lean`. Its deletion-capable merge API is independent
of coefficient types and polynomial policy, making that file a candidate
for later upstreaming. `HexMvPoly` supplies only the coefficient
combination and zero-elision rules.

# Arithmetic and correctness
%%%
tag := "hex-mv-poly-arithmetic"
%%%

Addition merges supports and deletes coefficients that cancel.
Multiplication accumulates every pairwise monomial product into one
canonical output map. Negation maps the values in a single tree pass.
The usual `+`, `-`, unary `-`, `*`, and power notation uses these
executable operations.

{docstring Hex.MvPoly.add}

{docstring Hex.MvPoly.neg}

{docstring Hex.MvPoly.mul}

Coefficient laws characterize the operations without exposing the
backing map. In particular, a product coefficient is the convolution
over every split of its target monomial.

{docstring Hex.MvPoly.coeff_add}

{docstring Hex.MvPoly.coeff_neg}

{docstring Hex.MvPoly.coeff_mul}

The executable operations satisfy the complete commutative-semiring and
commutative-ring law set. `HexMvPolyMathlib` packages those laws as
standard Mathlib structures; the computational library itself remains
independent of Mathlib.

# Evaluation and structural operations
%%%
tag := "hex-mv-poly-structural"
%%%

Direct evaluation folds the sparse support, using repeated squaring for
each exponent. Sparse Horner evaluation groups terms by variable
exponent, and is proven equal to the direct evaluator.

{docstring Hex.MvPoly.eval}

{docstring Hex.MvPoly.evalHorner}

{docstring Hex.MvPoly.evalHorner_eq}

The structural API changes variables, substitutes polynomials, projects
homogeneous pieces, differentiates, or partially evaluates selected
variables while preserving canonical form.

{docstring Hex.MvPoly.reorder}

{docstring Hex.MvPoly.rename}

{docstring Hex.MvPoly.derivative}

{docstring Hex.MvPoly.homogeneousComponent}

{docstring Hex.MvPoly.subst}

{docstring Hex.MvPoly.partialEval}

For algorithms that recurse on the number of variables,
{name}`Hex.MvPoly.toUnivariate` views a polynomial as a dense polynomial
in one selected variable whose coefficients are sparse polynomials in
the remaining variables. {name}`Hex.MvPoly.ofUnivariate` is its proven
inverse.

{docstring Hex.MvPoly.toUnivariate}

{docstring Hex.MvPoly.ofUnivariate_toUnivariate}

## Worked example
%%%
tag := "hex-mv-poly-worked"
%%%

The example builds
`x² + 2xy + 3`, inspects its sparse support, evaluates it, and
differentiates with respect to `x`.

```lean
open Hex Hex.MvPoly

namespace HexMvPolyChapter

abbrev P := MvPoly 2 Int Mono.lex

def x : P := X 0
def y : P := X 1
def p : P :=
  x ^ 2 + (C 2 * x) * y + C 3

#guard p.termCount = 3
#guard p.coeff #v[2, 0] = 1
#guard p.coeff #v[1, 1] = 2
#guard p.totalDegree = 2
#guard eval (fun i => if i = 0 then 2 else 5) p = 27
#guard derivative 0 p =
  C 2 * x + C 2 * y

end HexMvPolyChapter
```

# The Mathlib correspondence
%%%
tag := "hex-mv-poly-mathlib"
%%%

Everything above is executable and Mathlib-free. `HexMvPolyMathlib`
identifies exponent vectors with finitely supported functions and sparse
polynomials with Mathlib's {name}`MvPolynomial` over `Fin n`.

{docstring HexMvPolyMathlib.monoEquiv}

{docstring HexMvPolyMathlib.equiv}

{docstring HexMvPolyMathlib.algEquiv}

Conversion preserves coefficients and all ring operations. It also
matches differentiation, homogeneous projection, substitution, support,
degree, and the recursive view.

{docstring HexMvPolyMathlib.coeff_toMvPolynomial}

{docstring HexMvPolyMathlib.toMvPolynomial_derivative}

{docstring HexMvPolyMathlib.toMvPolynomial_subst}

{docstring HexMvPolyMathlib.finSuccEquiv}

The bridge packages evaluation as an algebra homomorphism. Its application
theorem states that executable evaluation is exactly Mathlib evaluation
after conversion, and its remaining `aeval_*` lemmas expose the familiar
homomorphism rules.

{docstring HexMvPolyMathlib.aeval}

{docstring HexMvPolyMathlib.aeval_apply}

# Cross-references
%%%
tag := "hex-mv-poly-cross-references"
%%%

* {ref "hex-poly"}[`HexPoly`] supplies the dense polynomial used by the
  recursive view.
* `HexBasic/ExtTreeMap.lean` contains the reusable ordered-map algorithms
  used by sparse addition and canonicalization.
* `HexMvPolyMathlib` is the proof boundary: it imports Mathlib, while
  `HexMvPoly` and its executable consumers do not.
