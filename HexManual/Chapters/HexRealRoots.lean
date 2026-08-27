/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import VersoManual

import HexRealRootsMathlib

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

set_option pp.rawOnError true

#doc (Manual) "HexRealRoots: certified real-root isolation" =>
%%%
tag := "hex-real-roots"
%%%

# Introduction
%%%
tag := "hex-real-roots-intro"
%%%

`HexRealRoots` isolates the real roots of a polynomial with integer
coefficients: it returns disjoint rational intervals, one per real root,
each certified to contain exactly one. The isolation is exact. There are
no floats and no error budget anywhere in the computation; the endpoints
are dyadic rationals and the certificate is a Sturm sign-variation count
checked in the kernel.

The computational core is Mathlib-free. It builds the Sturm chain of a
polynomial by exact integer arithmetic, evaluates sign variations at
dyadic points, and bisects until each root is alone in its interval. The
correspondence library `HexRealRootsMathlib` is the Mathlib bridge: it
proves that the isolated intervals really do capture the roots of the
polynomial as an element of `Polynomial ℝ`, and it packages the whole
workflow behind a single term elaborator.

The user-facing entry point is {ref "hex-real-roots-isolate"}[`isolate_roots`].
One call inspects a polynomial, runs the exact isolator while the file
elaborates, and produces a term whose type records the certified
statements. No knowledge of Sturm chains, dyadic arithmetic, or
squarefreeness is needed at the call site.

# Mathlib-free execution
%%%
tag := "hex-real-roots-core"
%%%

The computational package exposes {name}`Hex.isolate?`, which tries Descartes
search before falling back to Sturm bisection. The
{name}`Hex.isolateDescartes?` and {name}`Hex.isolateSturm?` variants select one
engine explicitly; {name}`Hex.rootCount` and {name}`Hex.sturmCount` expose the
exact counting operations. These functions run in native Lean and need no
external oracle at runtime.

The core isolators reject the zero polynomial; positive-degree inputs must be
squarefree, while nonzero constants have no roots and return an empty
isolation. Every emitted interval carries executable evidence for its Sturm
count, ordering, and contribution to the certified total. The core package
checks that finite evidence, while `HexRealRootsMathlib` supplies the theorem
connecting it to roots of `Polynomial ℝ` and handles squarefree reduction for
the elaborator below.

# The `isolate_roots` elaborator
%%%
tag := "hex-real-roots-isolate"
%%%

`isolate_roots p` takes a polynomial `p` and elaborates to a value of
type {name}`Hex.IsolatedRealRoots`. The polynomial may be a `Polynomial ℤ`,
`Polynomial ℚ`, or `Polynomial ℝ` with integer coefficients, or a raw
{name}`Hex.ZPoly` (the Mathlib-free dense integer polynomial). The result
structure carries the intervals and the three theorems that make them a
genuine isolation.

{docstring Hex.IsolatedRealRoots}

Take `x⁴ − 2`, whose two real roots are `±2^{1/4} ≈ ±1.189`. One call
isolates them. When the expected type is given — here through the
definition's type ascription — it pins the coefficient ring, so the
argument itself needs no annotation, and the type records the certified
count `2`:

```lean
open Hex Polynomial

/-- Both real roots of `x⁴ − 2`, certified. -/
noncomputable def x4roots :
    IsolatedRealRoots (X ^ 4 - 2 : Polynomial ℝ) 2 :=
  isolate_roots (X ^ 4 - 2)
```

The `intervals` field is an ordinary literal vector, so reading it back
is definitional. With no width request the intervals are whatever the
isolator's separation produced; here `(-4, 0]` and `(0, 4]`:

```lean
open Hex Polynomial

example : x4roots.intervals = #v[(-4, 0), (0, 4)] :=
  rfl
```

# What the fields say
%%%
tag := "hex-real-roots-fields"
%%%

The three propositional fields are the isolation contract, stated in
`aeval` form so they read uniformly across the coefficient rings. Project
`unique_root` at an index for the existence-and-uniqueness statement of
that interval; `simp [x4roots]` computes the interval endpoints to their
literal values, turning it into a self-contained theorem about `x⁴ − 2`:

```lean
open Hex Polynomial

/-- One real root of `x⁴ − 2` in `(0, 4]`. -/
theorem root_pos :
    ∃! x : ℝ, x ^ 4 - 2 = 0 ∧ (0 : ℝ) < x ∧ x ≤ 4 := by
  simpa [x4roots] using x4roots.unique_root 1
```

The `covers` field runs the other way: every real root lies in one of the
intervals, so listing them is a complete case analysis of the roots. Here
it proves that `x⁴ − 2` has no real root outside the two intervals:

```lean
open Hex Polynomial

theorem roots_complete (x : ℝ) (hx : x ^ 4 - 2 = 0) :
    (-4 < x ∧ x ≤ 0) ∨ (0 < x ∧ x ≤ 4) := by
  obtain ⟨i, hlo, hhi⟩ :=
    x4roots.covers x (by simpa using hx)
  simp only [x4roots] at hlo hhi
  fin_cases i
  · exact .inl ⟨by simpa using hlo, by simpa using hhi⟩
  · exact .inr ⟨by simpa using hlo, by simpa using hhi⟩
```

The `ordered` field says the intervals are sorted and pairwise disjoint.
Because the intervals are half-open, this is what makes the index count
`n` equal to the number of distinct real roots, and it gives disjointness
as a one-liner:

```lean
open Hex Polynomial

example : (x4roots.intervals[0]).2
    ≤ (x4roots.intervals[1]).1 := by
  simpa using x4roots.ordered 0 1 (by decide)
```

The whole structure unpacks with `obtain`, so the fields can be named and
fed to later tactics however a proof needs them:

```lean
open Hex Polynomial

example : True := by
  obtain ⟨ivals, uniq, cov, ord⟩ := x4roots
  trivial
```

# Requesting tighter intervals
%%%
tag := "hex-real-roots-width"
%%%

The natural intervals are only as tight as the isolator needed to separate the
roots. Passing `(width := x)` refines every interval to width at most `x`,
still with exact rational endpoints. The width must be a closed, strictly
positive rational expression; a free variable, zero, or a negative value is
rejected during elaboration. It may be written as a fraction, a power of two,
or a decimal power: `1/1000`, `2 ^ (-20 : ℤ)`, and `10 ^ (-2 : ℤ)` all work.

Internally the elaborator chooses the least nonnegative `k` with `2⁻ᵏ ≤ x` and
refines to that binary target. Widths above one therefore request `k = 0`,
which still refines any wider natural interval to width at most one;
refinement only narrows, so a coarse request cannot undo the isolator's
separation. A non-dyadic request can produce a strictly narrower interval than
requested. Targets finer than `2⁻⁴⁰⁹⁶` are rejected as pathological. Refining
`x⁴ − 2` to width `2⁻²⁰` places the positive root in an interval of width
exactly `2⁻²⁰`:

```lean
open Hex Polynomial

/-- The same two roots, isolated to width `2⁻²⁰`. -/
noncomputable def x4rootsTight :
    IsolatedRealRoots (X ^ 4 - 2 : Polynomial ℝ) 2 :=
  isolate_roots (width := 2 ^ (-20 : ℤ)) (X ^ 4 - 2)

/-- One real root in `(623487/2¹⁹, 1246975/2²⁰]`. -/
theorem root_pos_tight :
    ∃! x : ℝ, x ^ 4 - 2 = 0 ∧
      (623487 : ℝ) / 2 ^ 19 < x ∧ x ≤ 1246975 / 2 ^ 20 := by
  simpa [x4rootsTight] using x4rootsTight.unique_root 1
```

Width is an operational promise about the intervals the elaborator emits,
not a field of the structure. Reading the refined endpoints back is still
`rfl`, exactly as for the natural intervals; the refinement does not push
`Rat` normalization into the kernel.

# Squarefreeness is invisible
%%%
tag := "hex-real-roots-squarefree"
%%%

Sturm isolation needs a squarefree polynomial, but the user never has to
supply one. When the input has repeated roots the elaborator isolates its
squarefree core and transports the certificate back to the original
polynomial, so a polynomial like `(x − 1)²(x − 3)` isolates as its two
distinct roots with no bookkeeping at the call site:

```lean
open Hex Polynomial

noncomputable def cubeRoots :
    IsolatedRealRoots
      ((X - 1) ^ 2 * (X - 3) : Polynomial ℝ) 2 :=
  isolate_roots ((X - 1) ^ 2 * (X - 3))

example : cubeRoots.intervals = #v[(0, 2), (2, 4)] :=
  rfl
```

A polynomial with no real roots isolates as the empty vector, and a
nonzero constant isolates as `n = 0` without ever entering the isolator.
The zero polynomial is rejected, since every real number is a root.

# The Mathlib correspondence
%%%
tag := "hex-real-roots-mathlib"
%%%

The split between `HexRealRoots` and `HexRealRootsMathlib` is a trust and
dependency boundary. `HexRealRoots` performs exact integer and dyadic
computation without importing Mathlib. `HexRealRootsMathlib` interprets the
result in Mathlib's language of `Polynomial ℝ` and real roots. Its abstract
Sturm theorem is connected to the executable signed pseudo-remainder chain by
the following headline correspondence.

{docstring HexRealRootsMathlib.sturmChain_isSturmChain}

The elaborator runs compiled search only to choose certificate data. It emits
the integer polynomial, Sturm chain, and intervals as literals, then applies
the replay constructor whose obligations are ordinary Lean propositions.

{docstring Hex.IsolatedRealRoots.ofCert}

The emitted top-level term uses {name}`Hex.IsolatedRealRoots.ofCertPretty`,
which changes only the presentation of dyadic endpoints. The kernel checks
the chain, each interval count, the total count, and interval ordering; it
does not trust the compiled search or the Descartes dispatch. Inputs written
as `Polynomial ℤ`, `Polynomial ℚ`, or `Polynomial ℝ` are connected to
{name}`HexPolyZMathlib.toPolynomial` by a checked evaluation equivalence.
Repeated-root inputs are isolated through a squarefree core and transported
back with the following root-equivalence operation.

{docstring Hex.IsolatedRealRoots.congrRoots}

The interval endpoints are presented as reduced rational literals, and
the identification of the emitted literals with the isolator's dyadic
endpoints is stated over `ℝ`. This keeps rational normalization, and its
`Nat.gcd`, away from the kernel, which is what makes endpoint extraction a
plain `rfl` even for the refined fractional endpoints above.

# Cross-references
%%%
tag := "hex-real-roots-cross-references"
%%%

`HexRealRoots` sits at the top of the polynomial stack and is consumed
through its Mathlib bridge:

* {ref "hex-poly-z"}[HexPolyZ] provides the dense integer polynomial
  {name}`Hex.ZPoly` that the isolator operates on, together with the
  content, primitive-part, and squarefree-decomposition operations the
  squarefree-core step relies on.
* `HexRealRootsMathlib` is the correspondence library. It identifies the
  executable Sturm certificate with the root theory of `Polynomial ℝ`,
  proves that the squarefree core shares the real roots of the original
  polynomial, and provides {name}`Hex.IsolatedRealRoots` and the
  {ref "hex-real-roots-isolate"}[`isolate_roots`] elaborator documented
  here. The Mathlib dependency lives entirely in this bridge; a {name}`Hex.ZPoly`
  input keeps every emitted statement Mathlib-facing only through
  {name}`HexPolyZMathlib.toPolynomial`.
