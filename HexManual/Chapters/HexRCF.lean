/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import VersoManual

import HexRCF

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

set_option pp.rawOnError true

#doc (Manual) "HexRCF: a decision procedure for univariate real arithmetic" =>
%%%
tag := "hex-rcf"
%%%

# Introduction
%%%
tag := "hex-rcf-intro"
%%%

`rcf` decides statements about one real variable. Give it a sentence such as
`∀ x : ℝ, x⁴ − 4x + 3 ≥ 0` or `∃ x ∈ (1, 2], x³ − x − 1 = 0`: one universal or
existential quantifier over `ℝ`, or over a half-open interval `Set.Ioc a b`
with dyadic endpoints, followed by any Boolean combination of polynomial
equations and inequalities with rational coefficients. If the sentence is
true, `rcf` proves it. If it is false, `rcf` reports that, and for a universal
sentence names an interval on which the body fails.

This is Tarski's decision procedure in its simplest case. The real roots of
the polynomials in the sentence cut the line into finitely many intervals and
points, each polynomial keeps a constant sign on each piece, and so a
statement about every real number, or about some real number, becomes a
finite check. The tactic performs that check with exact integer arithmetic:
it isolates the roots with certified Sturm counts, records the sign of each
polynomial on each piece, and hands the kernel a certificate containing those
signs and counts. The kernel replays the certificate by evaluation, never
repeats the search, and the resulting proof uses no axiom beyond the three
that Mathlib always uses.

The tactics Mathlib already provides do something different. `nlinarith` and
`positivity` are heuristics: they succeed on many true inequalities of this
shape, may need hints such as `sq_nonneg (x - 1)` supplied by hand, and give
no verdict when they fail. `polyrith` proves equalities only. `decide` does
not apply to quantifiers over `ℝ`. None of them proves an existential
statement without a named witness, and the witness in the cubic above is
irrational. `rcf` needs neither hints nor a witness, and on this fragment it
always answers.

Import `HexRCF` and write `rcf` at the goal:

```lean
example : ∀ x : ℝ, x ^ 2 + 1 > 0 := by
  rcf
```

# Three facts a mathematician might want
%%%
tag := "hex-rcf-examples"
%%%

The Chebyshev polynomial `T₅` is bounded by one on `(−1, 1]` and attains the
bound; a cubic has a root in a dyadic interval and none outside it; a quartic
is nonnegative with equality at exactly one point. Each is one call:

```lean
example : ∀ x : ℝ, x ∈ Set.Ioc (-1 : ℝ) 1 →
    -1 ≤ 16 * x ^ 5 - 20 * x ^ 3 + 5 * x ∧
      16 * x ^ 5 - 20 * x ^ 3 + 5 * x ≤ 1 := by
  rcf

example : ∃ x : ℝ, x ∈ Set.Ioc (-1 : ℝ) 1 ∧
    16 * x ^ 5 - 20 * x ^ 3 + 5 * x = 1 := by
  rcf

-- The real root of x³ − x − 1 lies in (21/16, 43/32], and
-- nothing outside that interval is a root.
example : ∃ x : ℝ, x ^ 3 - x - 1 = 0 ∧
    21 / 16 < x ∧ x ≤ 43 / 32 := by
  rcf

example : ∀ x : ℝ, x ^ 3 - x - 1 = 0 →
    21 / 16 < x ∧ x ≤ 43 / 32 := by
  rcf

-- x⁴ − 4x + 3 = (x − 1)² (x² + 2x + 3) is nonnegative,
-- and zero only at x = 1.
example : ∀ x : ℝ, x ^ 4 - 4 * x + 3 ≥ 0 := by
  rcf

example : ∀ x : ℝ, x ^ 4 - 4 * x + 3 = 0 → x = 1 := by
  rcf
```

The statement that the cubic has exactly one real root mentions two
variables and is outside this fragment; {ref "hex-real-roots"}[HexRealRoots]
proves counts of that kind.

# The four quantifier forms
%%%
tag := "hex-rcf-quantifiers"
%%%

Quantification over the whole real line may be universal or existential. The
body can combine equalities, inequalities, conjunctions, disjunctions,
negations, and implications:

```lean
/-- A universal sentence over the real line. -/
example : ∀ x : ℝ, x ^ 2 ≤ 1 → x ^ 4 - x ^ 2 ≤ 0 := by
  rcf

/-- An existential sentence over the real line. -/
example : ∃ x : ℝ, x ^ 3 - x - 1 = 0 ∧ 1 < x ∧ x < 2 := by
  rcf
```

The bounded forms use `Set.Ioc a b`, which denotes `(a, b]`. The lower
endpoint is excluded and the upper endpoint is included:

```lean
/-- Universal quantification over `(0, 1]`. -/
example : ∀ x : ℝ, x ∈ Set.Ioc (0 : ℝ) 1 → x > 0 := by
  rcf

/-- Existential quantification over `(0, 1]`.
The upper endpoint is a witness. -/
example : ∃ x : ℝ, x ∈ Set.Ioc (0 : ℝ) 1 ∧ x = 1 := by
  rcf
```

An interval is empty when `a ≥ b`. Universal statements on an empty
interval are true, while existential statements are false. These examples
also show that the lower endpoint is not part of a nonempty interval:

```lean
example : ∀ x : ℝ, x ∈ Set.Ioc (1 : ℝ) 1 → x ^ 2 < 0 := by
  rcf

example : ¬ ∃ x : ℝ, x ∈ Set.Ioc (1 : ℝ) 1 ∧ x = x := by
  rintro ⟨x, hx, _⟩
  exact (not_lt_of_ge hx.2) hx.1

example : ∀ x : ℝ, x ∈ Set.Ioc (0 : ℝ) 1 → x ≠ 0 := by
  rcf
```

# Polynomial and rational syntax
%%%
tag := "hex-rcf-syntax"
%%%

Polynomial expressions may use numerals, the quantified variable, `+`, `-`,
`*`, negation, natural powers, and division by rational constants. The first
example exercises all of these arithmetic forms. The tactic clears rational
denominators before constructing its certificate:

```lean
example : ∀ x : ℝ,
    -(2 * x - 1) ^ 2 / 3 + 1 / 5 ≤ 1 / 5 := by
  rcf

example : ∀ x : ℝ,
    (x < 0 ∨ x ≥ 0) ∧
      (x ≤ 0 ∨ x > 0) ∧
      (x = 0 ∨ x ≠ 0) := by
  rcf
```

The coefficients may be any exact rationals, but bounded endpoints must be
dyadic rationals. Thus `1 / 3` is valid as a coefficient and is not valid as
an endpoint. An endpoint is supported exactly when its reduced denominator is
a power of two.

The proposition must contain exactly one quantified real variable and no other
free variables. Nested quantifiers, symbolic coefficients, division by an
expression containing the variable, and non-polynomial functions such as
`Real.sin` are outside the supported fragment. The tactic reports which of
these conditions failed.

# False sentences and fall-through
%%%
tag := "hex-rcf-false"
%%%

The tactic constructs proofs only for true sentences. For a false universal
sentence it identifies a cell on which the body is false:

```lean +error (name := rcfFalseUniversal)
example : ∀ x : ℝ, x ^ 2 > 0 := by
  rcf
```
```leanOutput rcfFalseUniversal
rcf: the universal sentence is false on the root cell isolated in (-2, 2]
```

For a false existential sentence it reports that all relevant cells were
checked and that none supplies a witness:

```lean +error (name := rcfFalseExistential)
example : ∃ x : ℝ, x ^ 2 + 1 = 0 := by
  rcf
```
```leanOutput rcfFalseExistential
rcf: the existential sentence is false. Every relevant decomposition
cell was checked and found false, so there is no witness
```

A sentence can be well formed and false. `rcf` then reports the failure
shown above and produces no proof. A goal outside the fragment is different:
it is not recognised as a sentence at all, and `rcf` fails before any
computation. Both are ordinary tactic failures, so tactic combinators may
fall through to another method. Here the unquantified goal is outside the
fragment and `norm_num` handles it:

```lean
example : (0 : ℝ) < 1 := by
  first | rcf | norm_num
```

# Rewriting other interval conventions
%%%
tag := "hex-rcf-interval-rewrites"
%%%

Only `Set.Ioc` is accepted directly. If a goal uses a closed interval
`Set.Icc`, separate the lower endpoint from the remaining half-open interval.
For a predicate `φ` the exact rewrites are:

* `∀ x ∈ Set.Icc a b, φ x` becomes
  `(a ≤ b → φ a) ∧ ∀ x ∈ Set.Ioc a b, φ x`.
* `∃ x ∈ Set.Icc a b, φ x` becomes
  `a ≤ b ∧ (φ a ∨ ∃ x ∈ Set.Ioc a b, φ x)`.

For an open interval `Set.Ioo`, exclude the upper endpoint from `Set.Ioc`:

* `∀ x ∈ Set.Ioo a b, φ x` becomes
  `∀ x ∈ Set.Ioc a b, x ≠ b → φ x`.
* `∃ x ∈ Set.Ioo a b, φ x` becomes
  `∃ x ∈ Set.Ioc a b, φ x ∧ x ≠ b`.

After the endpoint proposition has been handled separately, `rcf` can prove
the remaining singly quantified part. This worked closed-interval example
checks the lower endpoint separately and sends the `Set.Ioc` tail to `rcf`:

```lean
example : ∀ x : ℝ,
    x ∈ Set.Icc (0 : ℝ) 1 → x ^ 2 ≤ 1 := by
  have endpoint : (0 : ℝ) ^ 2 ≤ 1 := by norm_num
  have tail : ∀ x : ℝ,
      x ∈ Set.Ioc (0 : ℝ) 1 → x ^ 2 ≤ 1 := by
    rcf
  intro x hx
  rcases eq_or_lt_of_le hx.1 with h | h
  · subst x
    exact endpoint
  · exact tail x ⟨h, hx.2⟩
```

The open-interval rewrite is likewise accepted directly:

```lean
example : ∀ x : ℝ,
    x ∈ Set.Ioc (0 : ℝ) 1 → x ≠ 1 → x < 1 := by
  rcf

example : ∃ x : ℝ,
    x ∈ Set.Ioc (0 : ℝ) 1 ∧ x = 1 / 2 ∧ x ≠ 1 := by
  rcf
```

When `rcf` sees `Set.Icc` or `Set.Ioo` directly, its error message includes
the corresponding rewrite above.

# Sentences as data
%%%
tag := "hex-rcf-reflected-api"
%%%

Most users only need the `rcf` tactic. Programs that construct or inspect
sentences directly use the data types below. An atom compares one integer
polynomial with zero under one of the six comparison signs, formulas combine
atoms with the Boolean connectives, and a sentence adds the one quantifier
the decision procedure supports.

{docstring Hex.RCF.Formula}

{docstring Hex.RCF.Sentence}

{docstring Hex.RCF.Sentence.toProp}

The `#p[...]` literal lists coefficients in ascending degree order and
normalizes away trailing zeros. This direct construction represents
`∀ x : ℝ, x² + 1 > 0` and sends it through the same compiled decision
procedure used by the tactic:

```lean
open Hex.RCF

private def positiveQuadratic : Sentence :=
  .forallReal (.atom {
    p := #p[1, 0, 1]
    cmp := .gt
  })

#guard Hex.RCF.decide positiveQuadratic == some true
```

Bounded sentences use Lean's core {name}`Dyadic` endpoints and the half-open
interval `(a, b]`. This sentence represents
`∀ x ∈ Set.Ioc (0 : ℝ) 1, x ≥ 0`:

```lean
open Hex.RCF

private def nonnegativeOnUnit : Sentence :=
  .forallIoc (Dyadic.ofInt 0) (Dyadic.ofInt 1)
    (.atom {
      p := #p[0, 1]
      cmp := .ge
    })

#guard Hex.RCF.decide nonnegativeOnUnit == some true
```

For clients that need the evidence as well as the verdict,
{name}`Hex.RCF.build?` returns
the certificate together with its replay verdict:

{docstring Hex.RCF.build?}

```lean
open Hex.RCF

example (s : Sentence) (result : BuildResult)
    (h : build? s = some result) :
    result.certificate.replay? s =
      some result.verdict :=
  replay_build h
```

`build? s = none` means certificate construction or replay failed. It is
distinct from a successful result whose `verdict` is `false`.

# Performance
%%%
tag := "hex-rcf-performance"
%%%

The cost of `rcf` is the cost of elaborating the tactic: running the compiled
search, building the certificate as a literal, and having the kernel replay
it. The table gives the median added time of a fresh module containing one
`by rcf` theorem over the same module without it, so it includes elaboration
and kernel replay but not the fixed cost of loading Mathlib.

:::table +header
* * goal
  * polynomial degree
  * atoms
  * tactic time
* * quadratic
  * 2
  * 1
  * 0.26 s
* * degree ten
  * 10
  * 3
  * 4.4 s
* * adversarial
  * 50
  * 1
  * 4.3 s
:::

The compiled decision procedure on its own, {name}`Hex.RCF.decide` with no
proof, takes 32 ms, 85 ms, 184 ms, 333 ms and 541 ms on one-atom sentences
whose polynomial has 16, 20, 24, 28 and 32 real roots, consistent with the
declared quartic model in the root count. Measured on chungus2; the
artefacts and their provenance are recorded in `reports/hex-rcf-performance.md`
in the `hex-dev` repository, and the three tactic budgets they sit under are
2 s, 12 s and 30 s.

# Certificates and what the kernel checks
%%%
tag := "hex-rcf-trust"
%%%

A certificate has one of four shapes: the interval is empty; every polynomial
in the sentence is constant; the polynomial that governs the sign changes has
no real root in the domain; or, in the general case, a list of the pieces into
which its real roots cut the domain, with the sign of every polynomial on each
piece.

{docstring Hex.RCF.Certificate}

Unlike the other libraries in this manual, `HexRCF` imports Mathlib: the
tactic works on `ℝ`, and its soundness theorem is a statement about real
numbers. The search, the certificate checker and {name}`Hex.RCF.decide` do not
need Mathlib. They are collected in the module `HexRCF.DecisionCheck`, which
a build-time check keeps free of Mathlib imports, so the executable part can
be run and tested on its own.

Certificate construction runs as compiled elaboration code. That search is
not trusted. The tactic embeds its sentence and a literal
{name}`Hex.RCF.Certificate`, reduces the public Boolean checker
{name}`Hex.RCF.Certificate.check` to `true` in the kernel, and applies the
soundness theorem {name}`Hex.RCF.check_sound`. Lean's kernel also checks the
proof that the sentence as data is equivalent to the source goal.

The public soundness boundary can be used independently of the tactic:

```lean
open Hex.RCF

example (s : Sentence) (cert : Certificate)
    (h : Certificate.check s cert = true) : s.toProp :=
  check_sound s cert h

example (s : Sentence)
    (h : Hex.RCF.decide s = some true) : s.toProp :=
  decide_sound s h
```

{name}`Hex.RCF.Certificate.replay?` distinguishes malformed evidence (`none`), a checked
false verdict (`some false`), and a checked true verdict (`some true`).
{name}`Hex.RCF.Certificate.check` accepts only the last case. The convenience function
{name}`Hex.RCF.decide` returns `some true` only after this checker accepts the
certificate. Advanced clients can use {name}`Hex.RCF.build?` to retain the
certificate and its diagnostic or proof-producing verdict. A successfully
checked false sentence produces `some false`. Neither {name}`Hex.RCF.check_sound` nor the
tactic turns `some false` into a proof of a negation.

A `none` from {name}`Hex.RCF.decide` means the compiled path did not produce a
checker-accepted certificate. It does not mean that the sentence is false.

The kernel replays polynomial identities, signs, root counts, endpoint
comparisons, and the Boolean structure of the sentence, all on the concrete
numbers in the certificate. It does not repeat root isolation, polynomial gcd
computation, or interval refinement. The emitted
proof uses ordinary kernel reduction and does not use `native_decide`:

```lean
theorem rcf_square_nonnegative : ∀ x : ℝ, x ^ 2 ≥ 0 := by
  rcf
```

```lean (name := rcfAxioms)
#print axioms rcf_square_nonnegative
```
```leanOutput rcfAxioms
'rcf_square_nonnegative' depends on axioms: [propext, Classical.choice, Quot.sound]
```

# Cross-references
%%%
tag := "hex-rcf-cross-references"
%%%

* {ref "hex-poly-z"}[HexPolyZ] provides the dense integer polynomial
  operations used to normalize atoms and check polynomial identities.
* {ref "hex-real-roots"}[HexRealRoots] provides the exact real-root isolator
  that `HexRCF` uses during the search. `HexRCF` then re-derives each root
  count inside the certificate with a Sturm sequence the kernel can check; it
  does not isolate roots a second time.
* {ref "hex-number-field"}[HexNumberField] gives exact values for the roots
  a sentence talks about, when the values themselves are wanted.
