/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import VersoManual

import HexBerlekampZassenhausMathlib
import HexBerlekampZassenhausMathlib.LatticeTotality

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

set_option pp.rawOnError true

#doc (Manual) "HexBerlekampZassenhaus: factorization over the integers" =>
%%%
tag := "hex-berlekamp-zassenhaus"
%%%

# From integer factors to modular factors

`HexBerlekampZassenhaus` factors dense univariate polynomials over
the integers. The public function {name}`Hex.ZPoly.factorize` first
separates the signed content, powers of `X`, and repeated factors.
The remaining polynomial is primitive, square-free, and has positive
leading coefficient.

For a suitable prime `p`, reduction modulo `p` preserves the
square-free factorization. Hex factors the resulting polynomial over
`𝔽_p` by Berlekamp's method, then uses Hensel lifting to raise the
modular factors from `p` to a sufficiently large power `p^a`.
Each irreducible integer factor is represented by a product of some
of these lifted factors. Determining those subsets is called
recombination.

# Direct integer coordinates

Let `f` have leading coefficient `c`. The finite-field target is the
monic unit multiple `c⁻¹ f mod p`.

{name}`Hex.ZPoly.monicTarget` is its canonical integer lift modulo
`p^a`. This multiplication by a unit in `𝔽_p` does not change the
integer variable or apply a coefficient-swelling substitution.
During recombination, scaling a selected lifted product by `c`
returns it to the coordinates of `f`. Centred coefficient recovery,
primitive-part extraction, and sign normalization then give a factor
of the original polynomial.

Classical and lattice recombination use the same modular
factorization, factor indices, and direct-coordinate Hensel lift.

# Classical recombination

Classical Zassenhaus recombination enumerates subsets of the lifted
factors. For each distinguished first factor it considers subsets in
increasing cardinality, constructs the corresponding integer
candidate, and tests exact division. The direct support-partition
proof shows that the first accepted subset is exactly the support of
the irreducible factor containing the distinguished modular factor.

This method has small overhead when the number of modular factors is
small. Its worst-case subset search is exponential, so the public
implementation uses a complete-level budget: it either finishes a
whole subset-cardinality level or reports a typed decline before
starting that level.

For a large modular support, the total factorizer first tries all
unforced subsets of cardinality one through three. A factor found by
exact division is peeled immediately; its exact quotient and the
remaining lifted-factor indices are retained. This corrects an
important weakness of a distinguished-first-factor search: a small
integer factor need not contain the arbitrarily distinguished modular
factor.

# Iterated quadratic norms

Some irreducible polynomials factor into quadratics modulo every
prime, so recombination has to search the whole support lattice to
learn that no proper subset divides. The Swinnerton-Dyer polynomials
are the standard example: at modular width {lean}`16` the walk is
{lean}`32768` nodes to answer *irreducible*, and the width doubles with
each new radicand.

For that class the answer is available directly. The quadratic norm
{name}`Hex.quadNorm` of `g` at `d` is the norm of `g(X - t)`
along `ℤ[t]/(t² - d) → ℤ`, and {name}`Hex.iteratedNorm` folds it over a
list of radicands from `X - c`, producing the product of `X - c - ∑ᵢ εᵢ √dᵢ`
over all sign patterns. When no nonempty subproduct of the radicands is
a perfect square, that polynomial is the minimal polynomial of
`c + ∑ᵢ √dᵢ` over a field of degree `2ⁿ`, hence irreducible.

{docstring Hex.QuadraticNormCertificate}

{docstring Hex.QuadraticNormCertificate.check}

Both halves of the check are integer arithmetic: no number field is
constructed, the radicands are never factored, and no floating point is
used. Finding the certificate is a separate, untrusted step
({name}`Hex.QuadraticNormCertificate.recover?`), because a wrong
proposal is refused by the check.

{docstring Hex.quadraticNormCertified}

The gate is consulted once, where the modular factorization is already
in hand and before any Hensel lift. A success answers the whole
square-free core as one irreducible factor, reassembled by the same
code path as every other singleton proof; a failure falls through to
ordinary recombination carrying no state.

# Logarithmic derivatives and lattice recombination

For larger modular factorizations, Hex uses the recombination method
of Belabas, van Hoeij, Klüners, and Steel. For a lifted local factor
`g`, form its combined logarithmic derivative (CLD),
`Φ(g) = f · g' / g mod p^a`.

The identity `Φ(gh) = Φ(g) + Φ(h)` changes multiplication of selected
factors into addition of coefficient vectors. These vectors form the
coefficient block of an integer lattice. LLL reduction finds short
relations, and projection to the first coordinates produces
zero-one support indicators.

The Belabas-Hoeij-Klüners-Steel (BHKS) argument has two inclusions.
At the coefficient-recovery precision, every genuine factor support
indicator lies in the projected span. At the resultant precision,
every retained short vector is constant on genuine supports. The two
spans are then equal, so the equivalence classes of projected columns
are exactly the irreducible-factor supports.

This lattice calculation determines which lifted factors belong
together; it is not the older LLL polynomial-factorization algorithm
that recovers a factor directly from one short vector.

# Small lattices as checked proposals

On eligible large, dense inputs, the total factorizer also uses CLD
data as a cheap source of proposals. It prepares sixteen leading
coefficient columns once and tries nested lattices with four, eight,
twelve, and sixteen columns. These lattices have dimension close to
the number of remaining lifted factors, instead of adding every
coefficient of the polynomial.

No theorem trusts the proposed partition. Hex reconstructs the
proposed pieces in the original integer coordinates, checks their
exact product, and runs the unrestricted proved classical factorizer
on every piece. Only those classical results supply the final
irreducibility proof. A failed proposal continues to the full proved
CLD method and then, if necessary, trial division.

# Prime choice and totality

A direct prime plan records every successful modular factorization it
examines and chooses among them using predicted subset work, possible
factor degrees, lift precision, and the prime as a deterministic tie
breaker. The chosen factorization is reused by both recombination
methods.

Classical recombination and checked proposal replay may decline.
Lattice recombination is conclusive at its proved public precision
whenever prime selection succeeds. The finite prime search itself can
fail, so exhaustive integer trial division is the unconditional final
method. Thus {name}`Hex.ZPoly.factorize` is total on every integer
polynomial.

# Result and correctness

{docstring Hex.Factorization}

{docstring Hex.ZPoly.factorize}

For a nonzero input, the result has signed content as its scalar;
positive multiplicities; primitive, irreducible factors with positive
leading coefficients; and no two associated factor entries. Its
product is the input, and this normalized factorization is unique.
The next section states those guarantees as theorems.

{name}`Hex.factorTraced` returns the same factorization together with
the selected {name}`Hex.FactorMethod`, a possible classical decline,
and measurements of the classical search. The trace is observational:
all methods are checked by the same product and irreducibility
theorems.

# The Mathlib correspondence
%%%
tag := "hex-berlekamp-zassenhaus-mathlib"
%%%

Everything above is executable and Mathlib-free.
`HexBerlekampZassenhausMathlib` is the companion that restates the
guarantees of {name}`Hex.ZPoly.factorize` against Mathlib's
`Polynomial ℤ`, transported through `HexPolyZMathlib.toPolynomial`.

The product identity holds unconditionally and is re-exported as a
`simp` lemma:

{docstring HexBerlekampZassenhausMathlib.factorize_product}

Every emitted factor is irreducible, with no hypothesis on the input:

{docstring HexBerlekampZassenhausMathlib.factorize_irreducible_of_nonUnit}

The headline theorem bundles the full normal form of a nonzero input's
factorization:

{docstring HexBerlekampZassenhausMathlib.factorize_normalized}

That normal form is canonical. Any two factorizations satisfying it
with the same product agree up to the packing of multiplicities:

{docstring HexBerlekampZassenhausMathlib.factorize_unique}

The companion also carries the tactic surface across the boundary.
The base library's `factor_poly` and `irreducibility` elaborators work
on {name}`Hex.ZPoly` goals; importing `HexBerlekampZassenhausMathlib`
upgrades them to accept `Polynomial ℤ` as well, and adds the
kernel-checked `factor_poly!` and `irreducibility!` variants whose
certificate checks reduce inside the kernel.

# Relationship to the tactics

The `factor_poly` and `irreducibility` tactics described in
{ref "factor-tactics"}[the factor-tactics chapter] use this
factorization code as certificate search. Their emitted proof terms
contain reified polynomial data and verified certificate checks, not
an invocation of the factorization algorithm.
