/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import VersoManual

import HexRootsMathlib

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

set_option pp.rawOnError true

#doc (Manual) "HexRoots: certified complex-root isolation" =>
%%%
tag := "hex-roots"
%%%

# Introduction
%%%
tag := "hex-roots-intro"
%%%

`HexRoots` isolates the complex roots of a polynomial with integer
coefficients. Each root is enclosed in a square in the complex plane with
Gaussian-dyadic centre and power-of-two half-width, carrying a witness,
checked by `decide`, that a certified region around the square holds exactly
one root. As with real-root isolation the arithmetic is exact: the Taylor
coefficients at the centre are exact Gaussian dyadics, and every witness is a
strict comparison between two dyadic rationals. There are no floats and no
error budget anywhere in the computation.

The computational core is Mathlib-free. It expands a polynomial about a
Gaussian-dyadic centre, tests candidate squares, subdivides, and glues the
survivors into connected components until each root sits alone in a certified
square. The correspondence library `HexRootsMathlib` is the Mathlib companion:
it proves that a certified square really does contain a root of the polynomial
viewed as an element of `Polynomial ℂ`, and that a successful whole-polynomial
run enumerates every distinct root exactly once.

A single root is an {deftech}_atom_. Atoms admit two interchangeable
certificate forms: a Newton-Kantorovich contraction witness, whose certified
region is the square itself, and a Pellet root-count witness, whose certified
region is the square's circumscribed disc. A repeated root, or a pair too close
to separate, is reported instead as a {deftech}_cluster_ carrying a Pellet
witness that counts `k ≥ 2` roots with multiplicity. Squarefree inputs isolate
entirely into atoms; that is the case the user-facing {name}`Hex.isolate`
entry point below handles.

# The `isolate` entry point
%%%
tag := "hex-roots-isolate"
%%%

For a polynomial with only simple roots, {name}`Hex.isolate` runs the whole
isolator and returns one atom per distinct complex root. It takes the
polynomial as a {name}`Hex.ZPoly` (the Mathlib-free dense integer polynomial),
a proof that the roots are simple, a target precision in bits, and a choice of
which atom certificate to attempt:

{docstring Hex.isolate}

The simple-root precondition is decidable, so discharging it is a matter of
`by decide` in the common case, or a companion lemma for a named polynomial.
It casts the polynomial and its derivative to rationals and checks that their
gcd is constant:

{docstring Hex.HasOnlySimpleRoots}

The strategy argument, a {name}`Hex.AtomStrategy`, selects which certificate
form the driver attempts, and in which order: `.nk` for the
Newton-Kantorovich witness alone, `.pellet` for the Pellet witness alone, and
`.nkThenPellet` (the default) for the former with the latter as fallback. The
two forms are carried side by side while their soundness developments and
benchmarks are compared; a caller who does not care picks the default.

Each returned atom is one square with its certificate. The certified region
depends on which disjunct fired, but every consumer needs only the shared
consequence: the atom's stored square encloses exactly one root.

{docstring Hex.DyadicRootIsolation}

# Worked example: the smallest Pisot number
%%%
tag := "hex-roots-pisot"
%%%

Take `p(x) = x³ − x − 1`. It has one real root, the plastic constant
`β ≈ 1.3247`, and a complex-conjugate pair. The real root is the smallest
Pisot number: an algebraic integer greater than one all of whose conjugates
lie strictly inside the unit disc. `HexRoots` isolates all three roots, and the
companion turns those certificates into a proof of exactly that Pisot property.

{docstring HexRootsMathlib.Examples.pisot}

The polynomial has only simple roots, so it meets `isolate`'s precondition. The
companion proves this from a Bézout identity for `p` and `p'`, but any input
also decides it directly:

```lean
open Hex HexRootsMathlib.Examples

example : HasOnlySimpleRoots pisot := pisot_simple
```

Running the default driver to 32 bits returns three atoms, and the companion
identifies their semantic roots with the three complex roots of `x³ − x − 1`:

{docstring HexRootsMathlib.Examples.isolate_pisot}

The certificates pin the real root to eight decimal places and place both
nonreal roots strictly inside the unit disc, which is the Pisot property
stated for this polynomial:

{docstring HexRootsMathlib.Examples.pisot_property}

The same polynomial drives a runnable demo. From the repository root,
`lake exe hexroots_demo`
decides that all roots are simple, isolates all three in pairwise-disjoint
dyadic squares, and refines the positive-real isolation to at least 80 bits of
square precision, printing the certified centres and radii. The demo does the
search with the compiled isolator; the theorems above are the kernel-checked
statement of what it found.

# What the certificate proves
%%%
tag := "hex-roots-soundness"
%%%

A successful `isolate` run is not just a list of squares; the companion reads a
complete root enumeration out of it. Each atom names a genuine complex root,
distinct atoms name distinct roots, and together they exhaust the root set:

{docstring HexRootsMathlib.isolate_sound}

The root an atom names is a semantic value, not part of the executable data.
The companion selects it from the atom's certificate:

{docstring HexRootsMathlib.DyadicRootIsolation.root}

Because the semantic roots of the returned atoms are exactly
`(toPolyℂ p).roots.toFinset`, listing the atoms is a complete case analysis of
the complex roots, the same way real-root isolation gives a complete analysis
of the real roots. The Pisot example above is one instance: its three atoms
account for every root, so bounding each atom bounds every root.

# Refining a root
%%%
tag := "hex-roots-refine"
%%%

The precision the driver reaches is only as fine as separating the roots
required, floored at the target. To sharpen a single root without re-running
the whole isolator, refine its atom directly:

{docstring Hex.DyadicRootIsolation.refineTo?}

Refinement combines a speculative Newton step, which gains quadratic precision
when it certifies, with subdivision as the fallback. It preserves the root, so
the refined atom can stand in for the original wherever a caller needs a
tighter enclosure. This is the operation the demo uses to drive the real root
of `x³ − x − 1` down to 80 bits.

For consumers that need to compare roots for identity rather than approximate
them, an atom refined to at least separation precision becomes a
{name}`Hex.RefinedIsolation`, and {name}`Hex.RefinedIsolation.sameRoot` decides
whether two such isolations name the same root by a single dyadic
disc-intersection test. `hex-number-field` builds on that comparison.

# How the certificate is checked
%%%
tag := "hex-roots-certificate"
%%%

The driver does the search at run time with the compiled isolator. The witness
it emits is what the kernel re-checks, and that witness is a fixed conjunction
of strict comparisons between exact dyadics, not a replay of the search. The
Newton-Kantorovich atom witness is three such comparisons on the square itself:

{docstring Hex.nkWitness}

The Pellet form is the analogous root-count inequality on the circumscribed
disc, at three radii. Either way the kernel cost is a bounded number of exact
dyadic evaluations at the atom's centre, independent of how many subdivision
rounds the search performed to find it. Absolute values, which are irrational
in general, never enter the kernel: each is replaced by an exact dyadic bound
on the correct side, so soundness is preserved at the cost of a factor-2 margin
in how well-separated a root must be before its witness fires.

# Cross-references
%%%
tag := "hex-roots-cross-references"
%%%

`HexRoots` sits at the top of the polynomial stack, alongside the real-root
isolator, and is consumed through its Mathlib companion:

* {ref "hex-poly-z"}[HexPolyZ] provides the dense integer polynomial
  {name}`Hex.ZPoly` the isolator operates on, together with the
  squarefree-decomposition machinery the simple-root test relies on.
* {ref "hex-real-roots"}[HexRealRoots] is the real-line analogue. It isolates
  the real roots with a Sturm sign-variation certificate and returns rational
  intervals; `HexRoots` isolates every complex root with dyadic squares.
  A polynomial's real roots appear in both, as intervals there and as the
  real-centred atoms here.
* `HexRootsMathlib` is the correspondence library. It ports the
  Newton-Kantorovich theorem and develops the argument principle, Rouché's
  theorem, and the Mahler separation bound for polynomials on circles, then
  proves soundness and completeness of the isolator: every certificate names
  the roots it claims, and `isolate` never fails on a nonzero squarefree input.
  The Mathlib dependency lives entirely in this companion; a `ZPoly` input
  keeps the executable core Mathlib-free.
