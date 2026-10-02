/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import VersoManual

import HexRCF
import HexRCF.RealCoefficients
import HexRealClosure
import HexSignDet
import HexSignDetMathlib.SelectedProducer
import HexSignDetMathlib.CompletionProducer
import HexSignDetMathlib.TableProducer
import HexSignDetMathlib.ReencodingProducer
import HexSignDetMathlib.ReencodingRefinement
import HexSignDetMathlib.ThomReencoding
import HexSignDetMathlib.Convert

import HexSignDetMathlib.QueryHandle

import HexSignDetMathlib.RootList

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
signs and counts. The kernel replays the certificate by evaluation and never
repeats the search. Proofs in the rational fragment use no axiom beyond the
three that Mathlib always uses. The optional algebraic-coefficient extension
has a separately stated proof dependency below.

The tactics Mathlib already provides do something different. `nlinarith` and
`positivity` are heuristics: they succeed on many true inequalities of this
shape, may need hints such as `sq_nonneg (x - 1)` supplied by hand, and give
no verdict when they fail. `polyrith` proves equalities only. `decide` does
not apply to quantifiers over `ℝ`. None of them proves an existential
statement without a named witness, and the witness in the cubic above is
irrational. `rcf` needs neither hints nor a witness, and on this fragment it
always answers.

Import `HexRCF` and write `rcf` at the goal. Here it proves that the Chebyshev
polynomial `T₅` is bounded by one on `(−1, 1]` and attains the bound, that a
cubic has a root in a dyadic interval and none outside it, and that a quartic
is nonnegative with equality at exactly one point. Each is one call:

```lean
example : ∀ x : ℝ, x ^ 2 + 1 > 0 := by
  rcf

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

Bounded sentences use Lean's built-in {name}`Dyadic` endpoints and the half-open
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

# Algebraic coefficients
%%%
tag := "hex-rcf-coefficient-schemas"
%%%

Import `HexRCF.RealCoefficients` to extend the same `rcf` command. The original
`HexRCF` import and all its rational examples keep their existing behavior.
The adapter is currently available in the development monorepo; it is not in
the released `hex-rcf` package.
The optional adapter accepts a selected algebraic coefficient in
an otherwise rational polynomial sentence. Its direct notation support covers
`Real.sqrt 2` and Mathlib's `(2 : ℝ) ^ (1 / 3 : ℝ)`. It also accepts the checked
Hex values `CubeTwo.realAlgebraic` and `CubeTwo.shifted`. For a different
coordinate in a chosen number field, write a `Selected.field` expression with
the field element and its checked chosen root, as shown below. In these
examples, the power in `(2 : ℝ) ^ (1 / 3 : ℝ)` defines a closed coefficient;
the quantified variable still occurs in an ordinary polynomial. Products with
rational constants are supported, but expressions that divide by one of these
named algebraic coefficients currently decline; express an inverse as a
checked field coordinate when it is needed.

These examples use the selected real root of `X³ − 2`. The adapter records an
isolating square and verifies its root witness. It reconstructs Hex's
{name}`Hex.AlgebraicNumber` and {name}`Hex.RealAlgebraicNumber` through the
existing canonical constructor. The second coefficient is computed as `1 + a`
inside {name}`Hex.QAdjoin`, then converted through
{name}`Hex.RCF.RealCoefficients.Coefficients.ofField`; its selected real value
is proved to be `1 + a.toReal`. This `ofField` tactic example uses the specific
checked value `CubeTwo.shifted`. The definitions `CubeTwo.realAlgebraic` and
`CubeTwo.shifted` contain these constructions, and the following aliases show
their types and use. The second construction below takes a checked selected
root directly, computes `(a² + 1) / 2` with ordinary {name}`Hex.QAdjoin`
arithmetic, and uses {name}`Hex.RCF.RealCoefficients.Selected.field` to retain
the same root when converting back to a real algebraic number. These examples
set `maxRecDepth` to `2048` and `maxHeartbeats` to `1000000` so Lean can
elaborate their literal certificates; users may need the same options for
similar goals.

The same checked construction works for a different cubic, `X³ − X − 1`.
The square below selects its positive real root. The
{name}`Hex.RCF.RealCoefficients.Selected.real_rootNear` theorem identifies that
root with the ordinary {name}`Hex.ZPoly.rootNear` value at the real projection
of the square's centre. The tactic can use the selected root when it is named
by a `def` in the same file.

The two-square-root examples below combine `Real.sqrt 2` and `Real.sqrt 3`
in one common field and check that each field coordinate names the intended
positive root. This path accepts natural literal radicands when at least two
distinct square roots occur in the goal. A lone `Real.sqrt 2` uses the earlier
single-coefficient path; other lone square roots are not yet supported. The
two-root examples use a larger heartbeat limit for the quartic common field.
The next examples mix Mathlib's `Real.sqrt 2` with a Hex root selected from
`X² − 3`. They also use the ordinary `QAdjoin` element `1 + √3`, converted
back to a real algebraic number. `rcf` checks each proposed common-field
coordinate against the original selected root before proving the sentence.
For multiple sources, the tactic checks a defining polynomial and selected
real root for the common field, then verifies that every original coefficient
has the proposed value there. The higher-degree example below combines the
selected real root of `X³ − 2` with `Real.sqrt 2`.
Some larger combinations still decline with an irreducibility-witness
diagnostic: the current certificate search does not cover every polynomial
that can define a common field.

```lean
open Hex.RCF.RealCoefficients

set_option maxRecDepth 2048
set_option maxHeartbeats 1000000

private abbrev cubicGenerator : Hex.AlgebraicNumber :=
  CubeTwo.realAlgebraic.toAlgebraic

private abbrev fieldCoordinate :
    Hex.QAdjoin cubicGenerator :=
  1 + cubicGenerator.toQAdjoin

private abbrev fieldCoefficient : Hex.RealAlgebraicNumber :=
  Coefficients.ofField CubeTwo.realAlgebraic fieldCoordinate

private abbrev selectedCubic : Hex.RealAlgebraicNumber :=
  Selected.real CubeTwo.polynomial CubeTwo.square
    (by decide) (by decide) (by rfl) (by decide) (by decide)
    CubeTwo.checked CubeTwo.squarefree (by decide)

private abbrev selectedGenerator : Hex.AlgebraicNumber :=
  selectedCubic.toAlgebraic

private abbrev computedCoordinate :
    Hex.QAdjoin selectedGenerator :=
  (selectedGenerator.toQAdjoin *
    selectedGenerator.toQAdjoin + 1) / 2

private abbrev computedCoefficient :
    Hex.RealAlgebraicNumber :=
  Selected.field CubeTwo.polynomial CubeTwo.square
    (by decide) (by decide) (by rfl) (by decide) (by decide)
    CubeTwo.checked CubeTwo.squarefree (by decide)
    computedCoordinate

private abbrev plasticPolynomial : Hex.ZPoly :=
  Hex.DensePoly.ofList [-1, -1, 0, 1]

private abbrev plasticSquare : Hex.DyadicSquare :=
  ⟨Dyadic.ofInt 5426 >>> (12 : Int), 0, 12⟩

private theorem plasticChecked :
    plasticPolynomial.CheckedIrreducible :=
  ⟨by decide +kernel, by decide⟩

private theorem plasticSquarefree :
    Hex.HasOnlySimpleRoots plasticPolynomial := by
  have hne : plasticPolynomial ≠ 0 := by decide
  letI : plasticPolynomial.CheckedIrreducible :=
    plasticChecked
  exact (HexRootsMathlib.hasOnlySimpleRoots_iff_separable
    plasticPolynomial hne).mpr
    (Hex.ZPoly.CheckedIrreducible.separable
      plasticPolynomial)

private def plasticRoot : Hex.RealAlgebraicNumber :=
  Selected.real plasticPolynomial plasticSquare
    (by decide) (by decide) (by rfl) (by decide)
    (by decide) plasticChecked plasticSquarefree (by decide)

example :
    plasticPolynomial.rootNear plasticSquare.re.toRat 0 =
    plasticRoot.toAlgebraic := by
  exact Selected.real_rootNear
    plasticPolynomial plasticSquare
    (by decide) (by decide) (by rfl) (by decide) (by decide)
    plasticChecked plasticSquarefree (by decide)

example : ∀ x : ℝ, x + plasticRoot.toReal > x := by
  rcf

example : ∀ x : ℝ, x ^ 2 + Real.sqrt 2 > 0 := by
  rcf

/- The tactic checks both roots in one common field. -/
set_option maxHeartbeats 5000000 in
example : ∀ x : ℝ,
    x ^ 2 + Real.sqrt 3 - Real.sqrt 2 > 0 := by
  rcf

set_option maxHeartbeats 5000000 in
example : ∃ x : ℝ, Real.sqrt 2 < x ∧ x < Real.sqrt 3 := by
  rcf

private abbrev squareThreePolynomial : Hex.ZPoly :=
  Hex.DensePoly.ofList [-3, 0, 1]

private abbrev squareThreeSelection : Hex.DyadicSquare :=
  ⟨Dyadic.ofInt 7094 >>> (12 : Int), 0, 10⟩

private theorem squareThreeChecked :
    squareThreePolynomial.CheckedIrreducible :=
  Field.checkedIrreducible squareThreePolynomial
    (.eisenstein 3 0) (by decide +kernel) (by decide)

private theorem squareThreeSquarefree :
    Hex.HasOnlySimpleRoots squareThreePolynomial := by
  have hne : squareThreePolynomial ≠ 0 := by decide
  letI : squareThreePolynomial.CheckedIrreducible :=
    squareThreeChecked
  exact (HexRootsMathlib.hasOnlySimpleRoots_iff_separable
    squareThreePolynomial hne).mpr
    (Hex.ZPoly.CheckedIrreducible.separable
      squareThreePolynomial)

private def selectedThree : Hex.RealAlgebraicNumber :=
  Selected.real squareThreePolynomial squareThreeSelection
    (by decide +kernel) (by decide +kernel) (by rfl)
    (by decide) (by decide)
    squareThreeChecked squareThreeSquarefree
    (by decide +kernel)

private abbrev squareThreeGenerator : Hex.AlgebraicNumber :=
  selectedThree.toAlgebraic

private abbrev squareThreeCoordinate :
    Hex.QAdjoin squareThreeGenerator :=
  1 + squareThreeGenerator.toQAdjoin

private abbrev shiftedThree : Hex.RealAlgebraicNumber :=
  Coefficients.ofField selectedThree squareThreeCoordinate

set_option maxHeartbeats 5000000 in
example : ∀ x : ℝ,
    x ^ 2 + selectedThree.toReal - Real.sqrt 2 > 0 := by
  rcf

set_option maxHeartbeats 5000000 in
example : ∀ x : ℝ,
    x ^ 2 + shiftedThree.toReal - Real.sqrt 2 > 0 := by
  rcf

set_option maxHeartbeats 5000000 in
example : ∀ x : ℝ,
    x ^ 2 + selectedCubic.toReal - Real.sqrt 2 + 1 > 0 := by
  rcf

/-- error: rcf: the universal sentence is false on the
prepared cells -/
#guard_msgs (whitespace := lax) in
set_option maxHeartbeats 5000000 in
example : ∀ x : ℝ,
    x ^ 2 + selectedThree.toReal - Real.sqrt 2 < 0 := by
  rcf

example : ∃ x : ℝ, Real.sqrt 2 < x ∧ x < (3 : ℝ) / 2 := by
  rcf

example : ∀ x : ℝ, x ^ 2 + (2 : ℝ) ^ (1 / 3 : ℝ) > 0 := by
  rcf

example : ∀ x : ℝ, x ^ 2 +
    CubeTwo.realAlgebraic.toReal > 0 := by
  rcf

example : ∀ x : ℝ, x ^ 2 + fieldCoefficient.toReal > 0 := by
  rcf

example : ∀ x : ℝ,
    x ^ 2 + computedCoefficient.toReal > 0 := by
  rcf

example : ∃ x : ℝ, x ^ 2 = selectedCubic.toReal := by
  rcf

example : ∃ x : ℝ,
    x ^ 2 = selectedCubic.toReal ∧
    1 < x ∧ x < selectedCubic.toReal := by
  rcf

example : True := by
  fail_if_success
    have : ∀ x : ℝ, x ^ 2 + Real.sqrt 2 < 0 := by
      rcf
  trivial

example : True := by
  fail_if_success
    have : ∀ x : ℝ, Real.sin x = 0 := by
      rcf
  trivial
```

The existential statements have no witness supplied by the user. For the
selected cubic coefficient, `rcf` isolates a root of `x² − selectedCubic`
over its fixed real number field and checks both inequalities at that same
root in the interval example. The two
`fail_if_success` examples show that a false algebraic statement produces no
proof and that nonpolynomial syntax in the quantified variable is rejected.
The adapter's source reifier preserves explicit coefficient aliases and
original divisor obligations before normalization. Closed values built with
`Selected.real` may be named using `def` in the same file. Across modules, use
`abbrev` or `@[expose] def` so the defining expression remains visible. For
supported sentences, a divisor must be proved nonzero before certificate
construction.

The algebraic examples use the proved generic accepted-query soundness theorem
`HexRealRootsMathlib.Tarski.check_rootSum`. Their fixed-field certificate checks
and chosen-root identifications use only Lean's standard logical axioms.
See {ref "hex-number-field"}[HexNumberField] and
{ref "hex-real-algebraic"}[HexRealAlgebraic] for the underlying number APIs.

# Simultaneous signs and repeated roots over a cubic field
%%%
tag := "hex-rcf-cubic-signs"
%%%

Mathlib writes the nonnegative real cube root of two as
`(2 : ℝ) ^ (1 / 3 : ℝ)`, using {name}`Real.rpow`. It is a closed algebraic
coefficient here; powers of the quantified variable still have natural-number
exponents. The first example finds a positive square root of this coefficient
and checks two inequalities at the same root, without a supplied witness.
The second finds a common root of two different polynomials. That root has
multiplicity two in the first polynomial and multiplicity one in the second.

```lean
example : ∃ x : ℝ,
    x ^ 2 = (2 : ℝ) ^ (1 / 3 : ℝ) ∧
    1 < x ∧ x < (2 : ℝ) ^ (1 / 3 : ℝ) := by
  rcf

example : ∃ x : ℝ,
    (x - (2 : ℝ) ^ (1 / 3 : ℝ)) ^ 2 = 0 ∧
    x ^ 3 = 2 ∧ 1 < x ∧ x < 3 / 2 := by
  rcf

example : ∀ x : ℝ,
    (x - computedCoefficient.toReal) ^ 2 = 0 → 1 < x ∧ x < 3 / 2 := by
  rcf

example : ∃ x : ℝ,
    (x - computedCoefficient.toReal) ^ 2 = 0 ∧ 1 < x ∧ x < 3 / 2 := by
  rcf
```

The last two examples use the actual `QAdjoin` coordinate `(a² + 1) / 2`
constructed above, where `a` is the selected cube root of two. They check both
the location and existence of a repeated root over this nonquadratic field.
Repeated factors are allowed in the user's polynomials; the internal root
domain used for sign determination is squarefree. These examples use the
proved fixed-field replay and root-sum results, and their proofs depend only
on Lean's standard logical axioms.

# Arithmetic at a selected algebraic root
%%%
tag := "hex-rcf-selected-root"
%%%

`HexRealClosure` provides a computational interface for a selected real root
of a rational polynomial, including a reducible one. The checked descriptor
below selects `√2` from `(X² − 2)(X − 3)` using the open interval `(1, 2)`.
The value `a − 3` is nonzero at that root, even though it has a nonconstant
gcd with the defining polynomial. Its checked inverse and the cofactor split
use the selected root, not a quotient by the whole reducible polynomial.

The split creates context version `8` and explicitly refines `a` into it;
the original `a` remains in context version `7`. The checked `d.handle`
caches the selected canonical root. Its `pack` method stores a representative
with a unique zero. The resulting canonical value is positive and squares
to `2`. A polynomial over `Root.Handle.Value h` uses that same cached root
for every coefficient operation, including division.

```lean
section
open Hex Hex.RealClosure

private def x : DensePoly Rat := DensePoly.ofCoeffs #[0, 1]
private def head : DensePoly Rat :=
  (DensePoly.ofCoeffs #[-2, 0, 1]) *
    (x - DensePoly.C 3)
private def raw : SignDet.RawDescriptor Rat Nat :=
  { context := 7, head, lower := .finite 1,
    upper := .finite 2,
    indices := [], signs := [] }

private def selectedArithmetic : Option
    (Int × Int × Int × Nat × Nat × Nat × Bool ×
      Bool × Bool) := do
  let d ← Root.validate 7 raw
  let a : Expression d := ⟨x⟩
  let below : Expression d := ⟨x - DensePoly.C 3⟩
  let inverse? ← below.inverse?.toOption
  let inverse ← inverse?
  let split? ←
    (below.split? 8 (.finite 1) (.finite 2)).toOption
  let split ← split?
  let oldSign ← a.sign?.toOption
  let newSign ← (Expression.refine split a).sign?.toOption
  let inverseSign ← inverse.sign?.toOption
  let h := d.handle
  let packed : Element d := h.pack x
  let selectedZero := h.pack (x * x - DensePoly.C 2)
  let v := h.value packed
  let coeff : Root.Handle.Value h :=
    Root.Handle.Value.ofPoly h x
  let y : DensePoly (Root.Handle.Value h) :=
    DensePoly.ofCoeffs #[0, 1]
  let (_, remainder) := DensePoly.divMod
    (y * y - DensePoly.C 2) (y - DensePoly.C coeff)
  return (oldSign, newSign, inverseSign,
    d.raw.context, split.binding.target.raw.context,
    split.binding.target.raw.head.natDegree,
    selectedZero == 0,
    v * v == Hex.RealAlgebraicNumber.ofRat 2 &&
      v.sign == 1,
    remainder.isZero)

#guard selectedArithmetic ==
  some (1, 1, -1, 7, 8, 2, true, true, true)
end
```

The companion proves that checked signs, inversion, refinement and canonical
conversion preserve the selected real value. Those proofs use the shared
accepted-query soundness theorem `HexRealRootsMathlib.Tarski.check_rootSum`.
`Root.Handle.Value h` carries the same packed representation and gives
generic `DensePoly` algorithms operations that share this cached root.
See {ref "hex-number-field"}[HexNumberField] for fixed-field arithmetic and
{ref "hex-real-algebraic"}[HexRealAlgebraic] for the canonical value API.

# Signs and selected roots with BKR
%%%
tag := "hex-rcf-bkr"
%%%

The underlying sign-determination library can answer a more detailed question
than whether a sentence is true: at the roots of `x² − 1`, which sign patterns
of `x` and `x − 1` occur, and how many times? The checked table below has one
root with signs `(−,−)` and one with `(+,0)`. Every omitted pattern has count
zero. The query order is the order of the two supplied polynomials.

```lean
open Hex Hex.SignDet

private def bkrHead : DensePoly Rat :=
  DensePoly.ofCoeffs #[-1, 0, 1]
private def bkrX : DensePoly Rat :=
  DensePoly.ofCoeffs #[0, 1]

private def bkrTablePasses : Bool :=
  match determine Sturm.orderSign 7 bkrHead
      .negInf .posInf [bkrX, bkrX - 1] with
  | none => false
  | some table =>
    table.rows.toList == [([-1, -1], 1), ([1, 0], 1)] &&
      table.count [0, 0] == 0

#guard bkrTablePasses
```

{name}`Hex.SignDet.determine` returns `none` exactly when the defining
polynomial and interval do not form a valid root domain. An interval with no
roots returns an empty table. With no queries, the count at the empty sign
pattern is the number of roots. To reuse a prepared polynomial and
interval, call {name}`Hex.SignDet.determinePrepared` directly.

The success and correctness theorems are in
`HexSignDetMathlib.TableProducer`. {name}`Hex.SignDet.determinePrepared_success`
proves that the actual prepared BKR producer always supplies a checked table
under the coefficient-interpretation laws.
{name}`Hex.SignDet.determine_correct` identifies every returned count with the
number of mathematical roots having that sign pattern, including zero for
omitted patterns. Both the producer-success and count-correctness results use
the shared proved root-sum theorem.

Derivative signs identify a selected root. Here the positive root of
`x² − 1` is selected by the sign of the first derivative. A second checked
table gives the signs of three other polynomials at that root: `x`, `x − 1`,
and `x² − 2` have signs `+`, `0`, and `−` respectively. The descriptor records
the defining polynomial, interval and context as well as the derivative sign.

```lean
private def positiveRoot : RawDescriptor Rat Nat :=
  ⟨7, bkrHead, .negInf, .posInf, [1], [1]⟩

private def selectedSignsPass : Bool :=
  match Descriptor.build Sturm.orderSign 7 positiveRoot with
  | .ok (.ok root) =>
    match root.buildSigns
        [bkrX, bkrX - 1, bkrX * bkrX - 2] with
    | .ok signs => signs.values.toList == [1, 0, -1] &&
        root.checkSigns [bkrX, bkrX - 1, bkrX * bkrX - 2]
          signs.values signs.evidence &&
        !root.checkSigns [bkrX, bkrX - 1, bkrX * bkrX - 2]
          #v[-1, 0, -1] signs.evidence
    | _ => false
  | _ => false

#guard selectedSignsPass
```

The same operation works over a real number field. Let α be the positive cube
root of 2 constructed above, and work in ℚ(α) using ordinary {name}`Hex.QAdjoin`
arithmetic. The polynomial `(x − α)(x + α)` has two real roots; the positive
first-derivative sign selects α. At that root, `x − 1`, `x − 2` and `x³ − 2`
have signs `+`, `−` and `0`. Repeating the first query repeats its sign in the
same position. An empty query list returns an empty sign vector.

```lean
private abbrev signsField := Hex.QAdjoin cubicGenerator
private def signsAlpha : signsField :=
  cubicGenerator.toQAdjoin
private def signsFieldSign (a : signsField) : Int :=
  (Coefficients.ofField CubeTwo.realAlgebraic a).sign
private def signsX : DensePoly signsField :=
  DensePoly.ofList [0, 1]
private def signsHead : DensePoly signsField :=
  (signsX - DensePoly.C signsAlpha) *
    (signsX + DensePoly.C signsAlpha)
private def signsRoot : RawDescriptor signsField Nat :=
  ⟨7, signsHead, .negInf, .posInf, [1], [1]⟩
private def signsFieldPasses : Bool :=
  match Descriptor.build signsFieldSign 7 signsRoot with
  | .ok (.ok root) =>
    let queries := [signsX - 1, signsX - DensePoly.C 2,
      signsX.natPow 3 - DensePoly.C 2, signsX - 1]
    match root.buildSigns queries, root.buildSigns [] with
    | .ok signs, .ok empty =>
      signs.values.toList == [1, -1, 0, 1] &&
        empty.values.toList == []
    | _, _ => false
  | _ => false

#guard signsFieldPasses
```

Import `HexSignDetMathlib.SelectedProducer` for the success and correctness
theorems. {name}`Hex.SignDet.Descriptor.buildSigns_success` proves that `buildSigns`
always succeeds for a validated descriptor when coefficient arithmetic and
signs have their specified mathematical meaning. It proves preparation and
table construction succeed and rules out every final internal error; successful
output is not a hypothesis. {name}`Hex.SignDet.Descriptor.buildSigns_roots`
also proves that the returned list gives the signs at the original selected
root, in query order. These proofs use the shared root-sum theorem
`HexRealRootsMathlib.Tarski.check_rootSum`.

For one polynomial, a validated descriptor provides an ordinary integer sign.
The same cubic-field example can use this operation directly, receiving only the integer
sign from the checked calculation:

```lean
private def totalSignsFieldPasses : Bool :=
  match Descriptor.validate signsFieldSign 7 signsRoot with
  | some root =>
    [root.signAt (signsX - 1),
      root.signAt (signsX - DensePoly.C 2),
      root.signAt (signsX.natPow 3 - DensePoly.C 2)] == [1, -1, 0]
  | none => false

#guard totalSignsFieldPasses
```

{name}`Hex.SignDet.Descriptor.signAt_success` proves that the underlying
checked calculation succeeds, so its diagnostic zero fallback is unreachable
when the coefficient operations satisfy their interpretation laws.
{name}`Hex.SignDet.Descriptor.signAt_correct` identifies the returned integer
with the evaluation sign at the descriptor's original selected root. Both
results use the same shared root-sum theorem. For several queries, `buildSigns`
shares one table across the list; each `signAt` call constructs its own table.

Completing a partial derivative description supplies every derivative sign
without changing the selected root. Over the same cubic coefficient field,
`P = (x − α)x(x + α)` has roots `−α`, `0` and `α`. Its second derivative is
`6x`, so its positive sign selects α. Completion returns the signs of `P′`,
`P″` and `P‴`, all positive at α, in that order.

```lean
private def completionHead : DensePoly signsField :=
  (signsX - DensePoly.C signsAlpha) * signsX *
    (signsX + DensePoly.C signsAlpha)
private def partialRoot : RawDescriptor signsField Nat :=
  ⟨7, completionHead, .negInf, .posInf, [2], [1]⟩
private def completionPasses : Bool :=
  match Descriptor.validate signsFieldSign 7 partialRoot with
  | none => false
  | some root =>
    match root.buildCompletion with
    | .error _ => false
    | .ok evidence =>
      let full := root.complete
      full.raw.indices == [1, 2, 3] &&
        full.raw.signs == [1, 1, 1] &&
        full.raw.signs == evidence.descriptor.raw.signs &&
        root.raw.completes full.raw

#guard completionPasses
```

Import `HexSignDetMathlib.CompletionProducer` for
{name}`Hex.SignDet.Descriptor.buildCompletion_success` and
{name}`Hex.SignDet.Descriptor.complete_correct`. They prove that completion
succeeds for every validated partial description and retains its original
mathematical root, head, interval and context. This includes an empty partial
word when the interval contains exactly one root. The proofs use the shared
proved root-sum theorem.
They do not require the separate Thom ordering theorem. Each call computes and
checks its full derivative table; use `buildCompletion` directly when you need
the evidence as well as the completed descriptor.

For successive queries at one selected root, retain its prepared domain with
{name}`Hex.SignDet.Descriptor.prepareQueries`. This avoids the initial preparation call on each query list. Table
construction and selected-sign validation still replay the domain evidence
and joint table; the handle carries no measured speedup guarantee. Over the same cubic coefficient field:

```lean
private def preparedSignsFieldPasses : Bool :=
  match Descriptor.validate signsFieldSign 7 signsRoot with
  | none => false
  | some root =>
    match root.prepareQueries with
    | none => false
    | some handle =>
      match handle.buildSigns [signsX - 1, signsX - DensePoly.C 2],
          handle.buildSigns [signsX.natPow 3 - DensePoly.C 2] with
      | .ok pair, .ok zero =>
        pair.values.toList == [1, -1] && zero.value == 0 &&
          handle.signAt (signsX - 1) == 1 &&
          handle.signAt (signsX.natPow 3 - DensePoly.C 2) == 0
      | _, _ => false

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
#guard preparedSignsFieldPasses
```

{name}`Hex.SignDet.Descriptor.prepareQueries_success` proves that preparation
succeeds for validated descriptions under the coefficient laws.
{name}`Hex.SignDet.QueryHandle.buildSigns_roots` and
{name}`Hex.SignDet.QueryHandle.signAt_correct` identify all returned signs at
the original selected root. These results use the shared proved root-sum theorem.
The handle retains the original context, polynomial, interval and derivative selection; copied
certificates must still pass the ordinary literal replay checks.

Re-encoding asks whether the same selected root can be described using a
new defining polynomial and interval. It returns `none` if the target domain
is invalid or excludes that root. Sharing a different root is insufficient:
the source below selects +α from `(x − α)(x + α)`, while the target `x + α`
has only −α. Restricting the original head to `(−2, 0)` also excludes +α.
Both calls return ordinary absence, with no internal error.

```lean
private def absentReencodingPasses : Bool :=
  match Descriptor.validate signsFieldSign 7 signsRoot with
  | none => false
  | some root =>
    let absentHead := match root.buildReencoding
        (signsX + DensePoly.C signsAlpha) .negInf .posInf with
      | .ok none => true
      | _ => false
    let absentInterval := match root.buildReencoding
        signsHead (.finite (-2)) (.finite 0) with
      | .ok none => true
      | _ => false
    absentHead && absentInterval

#guard absentReencodingPasses
```

Import `HexSignDetMathlib.ReencodingProducer` for
{name}`Hex.SignDet.Descriptor.buildReencoding_absent`. It proves this result
for every lawful coefficient interpretation when the selected root is absent
from the target domain. Preparation and joint table construction are proved
from the input; successful output is not assumed. The proof uses the shared
proved root-sum theorem. It needs neither a root-separating interval nor a
Thom ordering theorem. Import `HexSignDetMathlib.ThomReencoding` for
{name}`Hex.SignDet.Descriptor.buildReencoding_success`, which proves actual
success for any valid target polynomial and interval containing the source root.
It uses Tau Ceti Thom injectivity to establish a count-one target word; neither
equality of defining polynomials nor a smaller interval is required.
For an accepted re-encoding,
{name}`Hex.SignDet.Reencoding.root_eq_source` proves that the new descriptor
retains the source root.

Refining the interval can retain the root instead. Here `(1, 3/2)` contains
+α and excludes −α. The producer constructs a complete derivative word and
fresh evidence for those bounds. Evidence from the original whole-line
description is rejected at the refined interval.

```lean
private def refinedCubicRootPasses : Bool :=
  match Descriptor.validate signsFieldSign 7 signsRoot with
  | none => false
  | some root =>
    match root.buildReencoding signsHead (.finite 1) (.finite (3/2)) with
    | .ok (some r) =>
      r.target.raw.lower == .finite 1 &&
        r.target.raw.upper == .finite (3/2) &&
        r.target.raw.signs == [1, 1] &&
        r.target.signAt (signsX.natPow 3 - DensePoly.C 2) == 0 &&
        r.target.raw.check signsFieldSign 7 r.target.evidence &&
        !({signsRoot with lower := .finite 1, upper := .finite (3/2)}).check
          signsFieldSign 7 root.evidence
    | _ => false

#guard refinedCubicRootPasses
```

{name}`Hex.SignDet.Descriptor.buildReencoding_refinement` proves success and
preservation of the selected root for a valid smaller root domain of the same
polynomial containing that root. Its hypotheses describe the input interval;
they do not assume a successful computation. The proof uses the old validated
selection's uniqueness and the proved shared Sturm–Tarski theorem. It applies to
generic lawful coefficients, including non-Archimedean interpretations, without
assuming rational isolating bounds.
{name}`Hex.SignDet.Descriptor.buildReencoding_congr` also covers different stored
coefficients representing the same polynomial, tested by a zero difference;
the producer builds fresh evidence bound to the new representation.
The general
{name}`Hex.SignDet.Descriptor.buildReencoding_success` theorem also covers
changing the mathematical defining polynomial and enlarging the interval.
A different head can include additional roots. Here the source selects +α in
`(0, 2)` with an empty partial word. The target `(x − α)(x + 1)` on the whole
line also contains −1, which was neither a root of the source head nor in its
interval. Re-encoding retains +α and builds fresh evidence for the target.

```lean
private def changedCubicHeadPasses : Bool :=
  let bounded : RawDescriptor signsField Nat :=
    ⟨7, signsHead, .finite 0, .finite 2, [], []⟩
  let target := (signsX - DensePoly.C signsAlpha) * (signsX + 1)
  match Descriptor.validate signsFieldSign 7 bounded with
  | none => false
  | some root =>
    match root.buildReencoding target .negInf .posInf with
    | .ok (some r) =>
      r.target.raw.head == target && r.target.raw.signs == [1, 1] &&
        r.target.signAt (signsX - DensePoly.C signsAlpha) == 0 &&
        r.target.raw.check signsFieldSign 7 r.target.evidence &&
        !r.target.evidence.check signsFieldSign 7 signsHead
          .negInf .posInf r.target.raw.queries
    | _ => false

#guard changedCubicHeadPasses
```

A coefficient conversion lets a selected root participate in queries over a
larger coefficient field. Here the source selects √2 over the rationals. Moving
its descriptor into the existing field ℚ(∛2) allows a query comparing it with ∛2:

```lean
private theorem cubic_zero (q : Rat) :
    (PolyQuot.ofRat q : signsField) = 0 ↔ q = 0 := by
  rw [← Field.value_eq_zero cubicGenerator.rep
      cubicGenerator.rep_mk
      ((AlgebraicNumber.isReal_iff cubicGenerator).mp
        CubeTwo.realAlgebraic.property),
    FieldSpecialize.value_ofRat cubicGenerator.rep
      cubicGenerator.rep_mk
      ((AlgebraicNumber.isReal_iff cubicGenerator).mp
        CubeTwo.realAlgebraic.property),
    Rat.cast_eq_zero]

private def convertedRootPasses : Bool :=
  let raw : RawDescriptor Rat Nat :=
    ⟨7, bkrX * bkrX - 2, .finite 0, .posInf, [], []⟩
  match Descriptor.validate Sturm.orderSign 7 raw with
  | none => false
  | some root =>
    match root.convert PolyQuot.ofRat cubic_zero signsFieldSign 8 with
    | .ok (.ok moved) =>
      moved.raw.context == 8 &&
        moved.signAt (signsX - DensePoly.C signsAlpha) == 1 &&
        moved.signAt (signsX * signsX - DensePoly.C 2) == 0
    | _ => false

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
#guard convertedRootPasses
```

{name}`Hex.SignDet.Descriptor.convert` maps the head and endpoints, retains the
partial derivative selection and builds fresh evidence in the new context.
It reconstructs every derivative query using the target's ordinary operations.
A context identifier here stands for the caller's immutable context data;
changing its binding requires fresh evidence even when all polynomial values
stay the same. No old certificate is copied by this operation.

{name}`Hex.SignDet.Descriptor.convert_success` and
{name}`Hex.SignDet.Descriptor.convert_root` prove success and preservation of the
selected root when both coefficient interpretations are lawful and the
conversion preserves their values. They cover noninjective representations and
assume no Archimedean property or rational isolating intervals. Applying them
to infinitesimal coefficients requires a lawful interpretation into a real
closed field. The nested-infinitesimal fixture tests execution and context
changes; it does not provide that interpretation.
These semantic proofs use the proved shared Sturm–Tarski theorem. An arbitrary
converter still has the builder's ordinary input and internal-error diagnostics.

Root enumeration constructs a full derivative description for each root. This
example uses the same actual cubic coefficient field and enumerates the roots
of `P = (x − α)x(x + α)`. The returned words correspond to `−α`, `0` and `α`:

```lean
private def rootsFieldPasses : Bool :=
  let p := signsHead * signsX
  match Descriptor.buildRoots signsFieldSign 7 p .negInf .posInf with
  | .ok (some roots) =>
    roots.map (fun d => d.raw.signs) ==
      [[1, -1, 1], [-1, 0, 1], [1, 1, 1]]
  | _ => false

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
#guard rootsFieldPasses
```

{name}`Hex.SignDet.Descriptor.buildRoots_coverage` proves that every successful
output covers every mathematical root in the interval exactly once. On valid
domains with no roots, {name}`Hex.SignDet.Descriptor.buildRoots_empty` proves
the actual constructor succeeds with an empty list;
{name}`Hex.SignDet.Descriptor.buildRoots_constant_success` covers nonzero
constant heads. {name}`Hex.SignDet.Descriptor.buildRoots_subsingleton` proves
success on every valid domain containing at most one root, including linear
heads and isolating intervals, without a Thom-order assumption.
{name}`Hex.SignDet.Descriptor.buildRoots_none_iff` characterizes invalid domains
exactly without using the root-sum theorem. The success and coverage results use
the shared proved root-sum theorem. A general proof that
enumeration succeeds on every valid domain and returns roots in mathematical
order remains required. The applicable full-word comparator is proved correct by
{name}`Hex.SignDet.Descriptor.fullOrder_root`. This example checks the
actual output; it does not discharge those general proof obligations.

Two roots can be compared even if their defining polynomials differ. The
comparison constructs a checked common squarefree polynomial and expresses
both root selections in it. This example finds `1 < 2`.

```lean
private def rootTwo : RawDescriptor Rat Nat :=
  ⟨7, bkrX - 2, .negInf, .posInf, [1], [1]⟩

private def orderedRootsPass : Bool :=
  match Descriptor.build Sturm.orderSign 7 positiveRoot,
      Descriptor.build Sturm.orderSign 7 rootTwo with
  | .ok (.ok one), .ok (.ok two) =>
    match one.buildComparison two with
    | .ok result => result.order == .lt &&
        result.common.check 7 positiveRoot.head rootTwo.head
    | _ => false
  | _, _ => false

#guard orderedRootsPass
```

The common-root case needs the shared factor removed before constructing the
squarefree comparison polynomial. The two descriptors below select the same
positive root of `x² − 2`, despite their different defining polynomials.

```lean
private def sqrtTwoRoot : RawDescriptor Rat Nat :=
  ⟨7, bkrX * bkrX - 2, .negInf, .posInf, [1], [1]⟩

private def sharedRoot : RawDescriptor Rat Nat :=
  ⟨7, (bkrX * bkrX - 2) * (bkrX - 3),
    .negInf, .posInf, [1], [-1]⟩

private def commonRootPass : Bool :=
  match Descriptor.build Sturm.orderSign 7 sqrtTwoRoot,
      Descriptor.build Sturm.orderSign 7 sharedRoot with
  | .ok (.ok left), .ok (.ok right) =>
    match left.buildComparison right with
    | .ok result => result.order == .eq &&
        result.common.check 7
          sqrtTwoRoot.head sharedRoot.head
    | _ => false
  | _, _ => false

#guard commonRootPass
```

For two independently selected coefficients, the existing number-field
constructor finds one coordinate field. Here √2 and √3 start as roots of
different polynomials. The check confirms that the common generator is real
and that both converted coordinates retain their original selected algebraic
values, in the supplied order. Converting those coordinates to real algebraic
numbers then checks the exact order √2 < √3 in their selected embeddings.

```lean
private def independentInputs :
    Array Hex.AlgebraicNumber := #[
  Hex.ZPoly.rootNear #p[-2, 0, 1] 1.4,
  Hex.ZPoly.rootNear #p[-3, 0, 1] 1.7]

private def independentRootsPass : Bool :=
  let common := Hex.QAdjoin.common independentInputs
  common.generator.isReal &&
    common.entries.map (·.toAlgebraicNumber) ==
      independentInputs &&
    match common.entries[0]?, common.entries[1]? with
    | some left, some right =>
      let a? := Hex.RealAlgebraicNumber.ofAlgebraic?
        left.toAlgebraicNumber
      let b? := Hex.RealAlgebraicNumber.ofAlgebraic?
        right.toAlgebraicNumber
      match a?, b? with
      | some a, some b => a < b
      | _, _ => false
    | _, _ => false

#guard independentRootsPass
```

The sign-table and descriptor examples run checked producers and finite
certificate checks; the changed sign vector above is rejected. The companion
proves complete real-root counts, selected-root identity and signs using the
proved root-sum theorem `HexRealRootsMathlib.Tarski.check_rootSum`.
The full-word comparison uses Tau Ceti’s delivered Thom identity and order
theorems through the companion. {name}`Hex.SignDet.Comparison.order_root`
proves that all three orders returned by an accepted comparison agree with the
original selected roots. Universal root-list and common-product comparison
production remain separate proof requirements. The
separate common-field conversion preserves the selected algebraic values by
the proved `QAdjoin.common_get` theorem.

# Caller-supplied finite bounds
%%%
tag := "hex-rcf-registered-bounds"
%%%

The optional import also accepts a caller's registered closed real subject.
A {name}`Hex.RCF.RealCoefficients.Registration` contains an executable
approximation and a separate containment theorem for that exact subject.
The `rcf_constant` attribute registers its declaration. Subjects match by
reducible definitional equality; duplicate matches among used subjects are
rejected. Unused providers are not evaluated or included in the certificate.
A registered whole expression is tried before its arithmetic constituents.
In a Lean module, mark the registration and its computational definitions
`@[expose]` so their frozen-result equalities reduce in the ordinary kernel.
A consuming module also needs `meta import` of the caller's registration
module to execute its approximation.
The callback must be total and executable, and its returned literal must be
reducible by the ordinary kernel. Registration checks its declaration's type;
it does not execute or establish those computational properties at import time.
Divisors inside a registered expression must themselves be closed reals or
rationals. Divisions depending on an internal binder, or over another carrier,
are unsupported; their variables are never exported as closed source guards.

This example uses the existing theorem that a sine lies in `[-1,1]`. The
caller supplies that fixed bound; the tactic does not construct an analytic
approximation procedure. The bound suffices for a square plus `2 + sin 1`.

```lean
open Hex.OrderedFn.Oracle

private def callerBounds (_ : Rat) : Bounds := ⟨-1, 1, by decide⟩

private theorem callerContainment
    (δ : Rat) (_ : 0 < δ) :
    Contains (callerBounds δ) (Real.sin 1) := by
  simpa [Contains, callerBounds] using
    And.intro (Real.neg_one_le_sin 1) (Real.sin_le_one 1)

@[rcf_constant] private def callerRegistration :
    Registration (Real.sin 1) where
  version := 1
  approximation := callerBounds
  containment := callerContainment

example : ∀ x : ℝ, x ^ 2 + 2 + Real.sin 1 > 0 := by rcf
example : ∃ x : ℝ,
    x = Real.sin 1 ∧ -2 < x ∧ x < 2 := by rcf
```

The finite path requests width `1/16` once. The actual width here is `2`;
containment does not assert that the request was met. A requested-width theorem
has the separate type
{name}`Hex.OrderedFn.Oracle.ApproximationWidth`, applied to
{name}`Hex.OrderedFn.Oracle.Approximation.ofConstant` with `callerBounds`.
Convergence and relative transcendence are separate hypotheses for total
search. This fixed bound makes no such claim. Finite proofs from containment
need neither hypothesis.

All original divisors are checked before cancellation, coefficient abstraction
or proof search. Thus even an erased division by `sin 1 - sin 1` is invalid.
The supplied interval also cannot certify that `sin 1` is nonzero: a bound
containing zero proves neither equality to zero nor a strict sign.

```lean
/-- error: rcf: original divisor is zero -/
#guard_msgs in
example : ∀ x : ℝ,
    x ^ 2 + 2 + Real.sin 1 +
      0 / (Real.sin 1 - Real.sin 1) > 0 := by
  rcf

/-- error: rcf: original divisor remains unresolved
in supplied bounds -/
#guard_msgs in
example : ∀ x : ℝ,
    x ^ 2 + 2 + Real.sin 1 + 0 / Real.sin 1 > 0 := by
  rcf
```

For direct proof construction, {name}`Hex.RCF.RealCoefficients.Finite.prepare`
returns the shared source formula/equivalence, fixed coefficient order, frozen
bounds and checked original guards. {name}`Hex.RCF.RealCoefficients.Finite.build`
constructs a proof of the source using the frozen facts and checked alias
hypotheses, then transports it to the shared schema. Unrelated caller
hypotheses are excluded from this proof search.
{name}`Hex.RCF.RealCoefficients.Finite.check` checks it and transports it back to
the original goal. The certificate binds the source, used registry/provider versions,
precision request, coefficient subjects and guards. Checking validates ordinary
proofs and frozen callback identities; it does not repeat approximation or root
search. Source coefficients and guards retain the same selected real values.

The existing algebraic handlers retain their documented inputs, including
registered small algebraic composites. Before exact reification, a registered
whole subject outside the exact scalar syntax or exponent envelope selects the
supplied frontend. Once an eligible backend starts, budget and replay failures
stop dispatch. Only providers used by source coefficients and original guards
are evaluated and bound into finite evidence.

This finite path uses nonlinear proof reconstruction from the supplied bounds,
with conjunctions and a proposed ordinary real existential witness. The current
witness is the first collected coefficient, or zero when there are none; it
does not search for witnesses. The precision request stays at `1/16`, without
refinement. It may fail
on a true statement, and such a failure is an unresolved proof attempt, not a
false verdict. False and unresolved goals can both fail proof reconstruction;
this path does not distinguish them by a decision verdict.
Lean's execution limits can also interrupt it. Failures restore
caller state and stop handler dispatch. The existing algebraic cell solver
continues to handle its documented inputs. Registrations alone do not complete
the general coefficient-field decision procedure.

The fresh-module probes in `bench/HexRCF/ProofProbe/Registered/` also prove
`∀ x, x² > π-4`, `∀ x, x²+exp 1 > 2`,
`∃ x, x=exp 1 ∧ 2<x ∧ x<3`, and the guarded
`∀ x, x²+1/(4-π)>0`. Their callers supply coarse bounds
`π ∈ [3,63/20]` and `exp 1 ∈ [27/10,14/5]`, with containment proved from
Mathlib's existing numerical inequalities. These are test registrations;
the optional library supplies no such providers. All four quoted theorem
dependencies are exactly `propext`, `Classical.choice` and `Quot.sound`.

For this fixed four-proof module, the command
`python3 scripts/bench/hexrcf_registered_proofs.py` asks whether these
coarse enclosures suffice for the four ordinary-kernel quotations without
root/cell construction, and measures their aggregate cost over the same
imports. It runs four adjacent
matched-import pairs in alternating AB/BA order and retains every sample.
At source revision `f5790840e`, Lean `v4.35.0-rc3` on the shared `chungus2`
host, pinned to CPU 92 with one Lean thread, fresh module builds took
9.08–9.24 seconds (median 9.16); matched imports took 7.54–8.15 seconds
(median 7.63). The median paired difference was 1.53 seconds. Median peak
resident memory was 3.28 GiB for the proofs and 3.20 GiB for matched imports.
These aggregate builds include elaboration, proof construction and ordinary
kernel checks; they do not isolate individual tactic stages or establish
scaling, convergence or completeness. The
[raw results](https://github.com/kim-em/hex-dev/blob/main/reports/bench-results/hexrcf-registered-f5790840e-chungus2.json)
and [all arm records](https://github.com/kim-em/hex-dev/blob/main/reports/bench-results/hexrcf-registered-f5790840e-chungus2.json.samples.jsonl)
retain compiler output, proof dependencies, artifact sizes and host context.

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
