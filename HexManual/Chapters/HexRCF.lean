/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import VersoManual

import HexRCF
import HexRCF.RealCoefficients
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.Complex.ExponentialBounds
import HexRealClosure
import HexSignDet
import HexSignDetMathlib.SelectedProducer
import HexSignDetMathlib.CompletionProducer
import HexSignDetMathlib.TableProducer
import HexSignDetMathlib.ReencodingProducer
import HexSignDetMathlib.ReencodingRefinement
import HexSignDetMathlib.ThomReencoding
import HexSignDetMathlib.ThomRoots
import HexRationalFn
import HexOrderedFn.Infinitesimal
import HexSignDetMathlib.ComparisonProducer
import HexSignDetMathlib.Convert
import HexRealAlgebraicMathlib.FieldSign
import HexRealClosureMathlib.LocalSample

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
positive rational square roots and positive rational bases with a reciprocal
natural exponent, including Mathlib's `(2 : ℝ) ^ (1 / 3 : ℝ)`.
It also accepts the checked
Hex values `CubeTwo.realAlgebraic` and `CubeTwo.shifted`. For a different
coordinate in a chosen number field, write a `Selected.field` expression with
the field element and its checked chosen root, as shown below. In these
examples, the power in `(2 : ℝ) ^ (1 / 3 : ℝ)` defines a closed coefficient;
the quantified variable still occurs in an ordinary polynomial. Products with
rational constants are supported. Closed division is also supported for the
selected and reconstructed Hex inputs and these checked positive-root aliases.
The adapter checks every original divisor before solving the target,
including divisors erased by cancellation, zero multiplication or an empty
domain. Named square/cube aliases keep their existing direct path when all
original divisors are rational; algebraic division uses the common field.

Visible `RealAlgebraicNumber.ofRat` constructors also retain their proved
rational value. They use the rational decision path after checked source
lowering; mixed expressions may still use the algebraic path. Divisions inside
the rational constructor's input remain original guard obligations. A known
zero guard reports `rcf: original closed divisor is zero`, including when
zero multiplication or an empty domain would otherwise hide it.

```lean
example : ∀ x : ℝ,
    x ^ 2 + (Hex.RealAlgebraicNumber.ofRat (3 / 2)).toReal > 0 := by
  rcf

example : ∀ x : ℝ,
    x ^ 2 / (Hex.RealAlgebraicNumber.ofRat 2).toReal + Real.sqrt 2 + Real.sqrt 3 > 0 := by
  rcf

example : ∀ x : ℝ,
    x ^ 2 + Real.sqrt (Hex.RealAlgebraicNumber.ofRat 2).toReal > 0 := by
  rcf
```

The last example proves the radicand's equality to `2` before identifying its
square root with the positive selected root. Square roots of rational
constructors with zero or negative values reduce through the rational path;
they do not select a positive algebraic root.

Positive rational roots use the same selected-field certificate machinery.
For a rational base `a` and positive natural degree `n`, the frontend records
`a.den * X^n - a.num` and checks a real-axis isolating square with a strictly
positive lower endpoint. The proved root equation and positivity identify
that selected root with `a ^ (1 / n : ℝ)`; approximation proposes the square
but supplies no proof. The base and exponent may also use inverse notation,
and visible rational constructors are lowered in both. Every
original denominator in the base, exponent or surrounding expression remains
a source guard.

```lean
section
set_option maxRecDepth 8192
set_option maxHeartbeats 2400000

example : ∀ x : ℝ,
    x ^ 2 - 2 * Real.sqrt (1 / 2) * x + 1 / 2 ≥ 0 := by
  rcf

example : ∀ x : ℝ,
    x ^ 2 + (5 / 3 : ℝ) ^ (1 / 4 : ℝ) > 0 := by rcf

example : ∃ x : ℝ,
    x ^ 2 = Real.sqrt (1 / 2) ∧ 0 < x ∧ x < 1 := by rcf

example : ∀ x : ℝ,
    x / (2 : ℝ) ^ (1 / 3 : ℝ) =
      ((2 : ℝ) ^ (1 / 3 : ℝ)) ^ 2 * x / 2 := by rcf
end
```

The first example uses the chosen positive square root in a polynomial whose
minimum is zero. The third finds a further root over that coefficient field.
The last checks the cube root's nonzero divisor before using its power equation.
Division by a closed higher-root alias becomes multiplication by its closed
inverse before abstraction, so the shared integer reifier receives no parameter
denominator. Natural powers of the quantified variable keep their usual
polynomial meaning. Nonreciprocal real exponents are outside this alias grammar.
Roots with an algebraic base first authenticate that base in its selected
field. Frozen polynomial, power and sign evidence then identifies the root
with the original expression. For degrees greater than one, this checks the
nonnegative branch; negative bases do not receive a signed-root interpretation.
Degree one is ordinary identity and also accepts negative algebraic bases.

```lean
section
set_option maxRecDepth 16384
set_option maxHeartbeats 2400000

example : ∀ x : ℝ,
    x ^ 2 - 2 * Real.sqrt (Real.sqrt 2) * x +
      Real.sqrt 2 ≥ 0 := by rcf

example : ∃ x : ℝ,
    x = Real.sqrt (3 + Real.sqrt 2) ∧
      2 < x ∧ x < 3 := by rcf

example : ∀ x : ℝ,
    x ^ 2 + Real.sqrt
      (1 / (4 + Real.sqrt 2)) > 0 := by rcf
end
```

These examples respectively use a nested root as a coefficient, locate a
root of a shifted algebraic base, and retain the original divisor guard
inside a root. Cancellation can yield a zero base, but never removes a
zero-divisor obligation. The same authentication supports reciprocal natural
root degrees such as `(3 + Real.sqrt 2) ^ (1 / 3 : ℝ)` and further nesting.
The ordinary proof checks recorded certificates; it does not repeat the
native root or sign searches.

Before common-field
search, `rcf.algebraic.commonDegree` bounds the product of the canonical degrees
of distinct selected generators (default 64), reporting exhaustion through
the shared exponent dimension. This is a conservative admission bound:
aliases for one selected generator count once, but algebraic relations between
different generators can make the actual common degree smaller than the product.
The admission also applies to a single generator. Algebraic-base roots require
the root degree times the degree of the field authenticating their base to
fit the same limit. This conservative bound applies before native root
production, including when cancellation reduces the base's minimal degree.
Repeated uses of exactly the same base share authentication throughout one recursive preparation.
These roots require supported selected-field presentations and irreducibility certificates.
It does not establish complete witness search or bound every later operation.
Authentication follows source order; a terminal failure or exhaustion prevents
authentication of later coefficients, even when a later negative base would decline.

The adapter's source preparation applies its coefficient-size limit to
intermediate arithmetic in rational-root bases, reciprocal exponents and
dyadic endpoints. Cancellation and zero powers do not erase those bounds.

The selected-field constructions below use the real root of `X³ − 2`. The adapter records an
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
by a `def` in the same file. It also accepts the existing checked
{name}`Hex.AlgebraicNumber.ofNormalized` constructor directly, followed by
{name}`Hex.RealAlgebraicNumber.ofAlgebraic` with a reality proof. The original
isolation square authenticates the chosen root. Elaboration executes
canonicalization. Before common-field search, the adapter checks a direct root
witness on the original square. The kernel authenticates its literal square
and polynomial identities rather than replaying canonicalization.
Both identities must reduce in the kernel, including across imports.
A transported certificate without a direct witness is currently rejected.
The example below computes `α² − 1` in the field
of the selected root of `X³ − X − 1` and uses its proved real conversion.
The constructor data must be executable and visible to the frontend; an
arbitrary opaque algebraic value has no implicit reconstruction rule.

Field signs first try exact rational Horner bounds on the authenticated
generator interval. A strictly separated bound proves its sign; exactly
`[0,0]` proves zero. Other zero-containing bounds retain a full rational Sturm
query. Replay checks the recorded branch, and never rescues malformed query
evidence with interval evaluation. The complete algebraic producer still
succeeds on its proved input surface. Indexed sign retrieval below reduces
fresh-module build time on the recorded examples.

A four-round matched comparison on the further-root, reciprocal-root and cubic
examples used raw carriers and favored interval quotation in all twelve pairs,
with median paired
margins 4.513, 4.752 and 13.553 seconds. The reference reconstructs full queries
after interval production, so this measures quotation-mode selection, not a
speedup against older code or isolated kernel time. Shared-host variation and
all completed samples are retained in `reports/hexrcf-interval-proofs.md`.
Those probes now pin raw carriers explicitly; the pin was added after the
measurement. The default is `rcf.algebraic.intervalSigns=true`; the false arm remains a
comparison control. Direct coordinate quotation remains off by default: its
two separate comparisons did not establish a gain.
The comparison control changes evidence from the tactic producers. Quotation and replay
of a supplied frozen table, including the explicit prepared replay API, preserve its
entries regardless of this option.

`rcf.algebraic.singleReplay` is also false by default. It compares one Boolean
certificate replay goal with separately checked conjuncts; source authentication
and the final proof check remain separate. A four-round comparison of the same
three examples used raw carriers and did not establish a speedup. The probes
now explicitly pin that mode; the pin was added after the retained measurement.
Combined replay produced smaller private proof files but used more peak memory. The
[report and retained samples](https://github.com/kim-em/hex-dev/blob/main/reports/hexrcf-replay-proofs.md)
record every completed arm and the exact source and import identities.

`rcf.algebraic.monicCore` is true by default. It normalizes the
proposed carrier core while retaining the original polynomial product and
checking both radical identities. Signed Sturm chains keep their existing
positive scaling. All twelve pairs in a four-round comparison favored this
mode on the same three examples, with lower peak memory. The
[report and retained samples](https://github.com/kim-em/hex-dev/blob/main/reports/hexrcf-carrier-proofs.md)
describe these full-build observations. Successful proposals have checked
soundness and a proved monic core. Radical proposal progress and interpreted
squarefreeness are proved at the actual selected field embedding, using
zero-reflecting coefficient semantics that preserve arithmetic and inversion.
These are radical laws; bounded isolation can still exhaust. The complete
library producer retains raw cores and its existing progress laws. Direct
`produceWithin` calls also retain their raw default; the tactic passes its
monic option explicitly. The false mode retains raw cores as a comparison control. This
normalization does not remove the common-field authentication limitation.

`rcf.algebraic.indexSigns` is true by default. It retrieves field signs
through a frozen tree of positions in the original checked evidence table.
Every hit checks its array bounds and exact key. A missing route uses the
original table lookup, so malformed routing cannot lose a recorded sign;
an absent original entry still fails preflight. The kernel checks the same
sign evidence and uses a proved checker equivalence before the existing
soundness theorem. It does not sort keys during replay.
Two separate four-round comparisons favored indexed lookup in every pair
on the further-root, reciprocal and cubic examples. The preserved-hit mode's
median paired reductions were 3.774, 3.493 and 3.527 seconds, with lower peak
memory and larger private proof files. These are full fresh-module costs,
not isolated lookup timing or an asymptotic claim. The
[report and retained samples](https://github.com/kim-em/hex-dev/blob/main/reports/hexrcf-index-proofs.md)
include every completed arm and their source identities. The false mode keeps
linear retrieval; older comparison probes explicitly pin that mode.

`rcf.algebraic.signRefinements` is zero by default. Setting it to a positive
natural number bounds producer attempts to tighten the generator interval when
Horner signs are inconclusive. The certificate retains the original generator
and checks that the tighter count-one interval selects the same real root.
Replay checks frozen data and never runs refinement. Inconclusive signs keep
full query evidence; invalid proposed evidence is terminal. The
[retained comparison](https://github.com/kim-em/hex-dev/blob/main/reports/hexrcf-window-proofs.md)
found no useful whole-module speedup at a four-step budget, even though the
lower-precision fixed-field case removed full queries. This mode therefore
remains optional. The entire bounded refinement loop is one
native call: cancellation is checked before and after it, not between its
steps. A large chosen budget can therefore delay interruption.

A separate [initial-precision comparison](https://github.com/kim-em/hex-dev/blob/main/reports/hexrcf-precision-proofs.md)
proves the same fixed-field sentence at eight and sixty-four generator bits,
using a checked selected-root equivalence for transport. The full sign queries
fall from three to zero, and the private proof file shrinks by 6,456 bytes.
Four retained rounds give median fresh-module times of 12.689 and 12.556 seconds;
the paired median change is −0.169 seconds, with one slower candidate. Arm-specific constructor checks and the candidate
transport are prebuilt, so their initial elaboration is excluded. This does not
measure the total cost of changing precision or general field reconstruction,
and does not justify a default precision change.

The [four-width study with constructor and transport included](https://github.com/kim-em/hex-dev/blob/main/reports/hexrcf-precision-production-proofs.md)
checks eight, sixteen, thirty-two and sixty-four initial bits through the
actual tactic proof-acceptance routine. All 36 fresh-module arms retain their
output and standard-axiom audit. The variable paired observations justify no
default change. Each timed module proves its own generator validity and
selected-root equivalence; common imported laws and the original target are
prebuilt. This fixed-field experiment does not implement arbitrary field
reconstruction or nested transport.

The [source repeated/shared-root comparison](https://github.com/kim-em/hex-dev/blob/main/reports/hexrcf-common-root-proofs.md)
uses actual `rcf` goals with a squared zero polynomial and an additional
polynomial sharing existing roots. All three checked carriers have four root
sections and five sectors. Sixteen retained arms include the named-√2 frontend preparation,
quotation and kernel acceptance; paired medians increase by 0.890 and 1.266
seconds for these changed inputs, retaining a −8.198-second repeated-input
observation as well. Several input dimensions change together,
so this is not a one-parameter complexity model or a general scaling claim.

For these reconstructed inputs, closed arithmetic is compiled into the common
field after authenticating its source values. A quotient is recorded as a
rational coordinate polynomial and checked by its multiplication identity;
kernel replay does not repeat inverse search. When all source coordinates use
one selected generator, the adapter retains that generator and its existing
power basis; it does not run general common-field search. Polynomial and
isolation-square checks still authenticate every proposed source coordinate.
If the common defining polynomial exactly matches an authenticated source's
polynomial, quotation reuses its supplied `CheckedIrreducible` proof. The
kernel proves equality of the original and literal polynomials and transports
the source instance along that equality; runtime equality alone is insufficient.
This supports source proofs beyond the frontend's
single-witness and quadratic-norm search languages, including a checked real
quartic with a multi-prime certificate. The fresh goal proofs use ordinary
imports, including certificate construction and replay through the owner's
public API. For a new common polynomial, the frontend tries quadratic-norm and free
witness certificates, then the owner's multi-prime certificate producer and
ordinary-kernel quotation. These certificate languages do not cover every
irreducible common defining polynomial. Increasing a search bound need not
resolve a refusal, and their failure does not imply reducibility.
The cubic example below verifies
`x / α = (α² − 1) * x` at the selected positive root of `X³ − X − 1`.
The same example also uses the ordinary `QAdjoin.toAlgebraicNumber`
conversion followed by a reality proof, without the `Coefficients.ofField`
wrapper. Both forms preserve the selected embedding.

The two-square-root examples below combine `Real.sqrt 2` and `Real.sqrt 3`
in one common field and check that each field coordinate names the intended
positive root. This path accepts positive rational radicands as well as
natural literals, and also accepts the positive rational-root aliases above. A lone `Real.sqrt 2` whose original
divisors are all rational uses the earlier single-coefficient path; other
positive natural square roots use the common-field frontend, including
perfect-square radicands. Algebraic divisors contribute generators even when
their quotients cancel, so they can increase the common-field degree. The
two-root examples use a larger heartbeat limit for the quartic common field.
The retained measurements below do not measure that degree increase.
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

private abbrev plasticRep :
    Hex.RefinedIsolation plasticPolynomial :=
  Field.literalRep plasticPolynomial plasticSquare
    (by decide) (by decide)

private abbrev plasticAlgebraic : Hex.AlgebraicNumber :=
  Hex.AlgebraicNumber.ofNormalized plasticPolynomial
    (by rfl) (by decide)
    (by decide) plasticChecked plasticSquarefree
    plasticRep
    (Hex.AlgebraicNumber.ofNormalized?_isSome _ _ _ _ _ _ _)

private def normalizedPlastic : Hex.RealAlgebraicNumber :=
  Hex.RealAlgebraicNumber.ofAlgebraic plasticAlgebraic (by
    apply (Hex.AlgebraicNumber.isReal_iff _).mpr
    exact (congrArg Complex.im
      (Selected.normalized_toComplex
      plasticPolynomial (by rfl) (by decide) (by decide)
      plasticChecked plasticSquarefree plasticRep _)).trans
      (Field.literalRep_real _ _ _ _ (by decide)))

private abbrev plasticCoordinate :
    Hex.QAdjoin normalizedPlastic.toAlgebraic :=
  normalizedPlastic.toAlgebraic.toQAdjoin ^ 2 - 1

private abbrev plasticCoefficient :
    Hex.RealAlgebraicNumber :=
  Coefficients.ofField normalizedPlastic plasticCoordinate

example : ∀ x : ℝ,
    x ^ 2 + plasticCoefficient.toReal > 0 := by
  rcf

example : ∀ x : ℝ,
    x / normalizedPlastic.toReal =
      plasticCoefficient.toReal * x := by
  rcf

private abbrev convertedPlastic :
    Hex.RealAlgebraicNumber :=
  Hex.RealAlgebraicNumber.ofAlgebraic
    plasticCoordinate.toAlgebraicNumber (by
    rw [Hex.AlgebraicNumber.isReal_iff, Hex.QAdjoin.toAlgebraicNumber,
      Hex.PolyQuot.toAlgebraicNumber_toComplex]
    exact Hex.QAdjoin.value_real plasticCoordinate
      normalizedPlastic.property)

example : ∀ x : ℝ,
    x / normalizedPlastic.toReal = convertedPlastic.toReal * x := by
  rcf

example : ∀ x : ℝ,
    x / Real.sqrt 2 = (Real.sqrt 2 / 2) * x := by
  rcf

example : ∀ x : ℝ,
    x ^ 2 + Real.sqrt 4 - Real.sqrt 2 > 0 := by
  rcf

example : ∀ x : ℝ,
    x ^ 2 + 1 / (Real.sqrt 2 + 1) > 0 := by
  rcf

example : ∃ x : ℝ,
    x ^ 2 = 1 / (Real.sqrt 2 + 1) ∧ 0 < x ∧ x < 1 := by
  rcf

/-- error: rcf: original closed divisor is zero -/
#guard_msgs in
example : ∀ x : ℝ,
    x ^ 2 + 0 / (normalizedPlastic.toReal -
      normalizedPlastic.toReal) ≥ 0 := by
  rcf

example : ∃ x : ℝ,
    x ^ 2 = normalizedPlastic.toReal ∧
    1 < x ∧ x < normalizedPlastic.toReal := by
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
root in the interval example. The `fail_if_success` examples show that a false
algebraic statement produces no proof, nonpolynomial syntax in the quantified
variable is rejected, and a cancelled zero divisor remains an invalid input.
`CubeTwo.realAlgebraic` exposes its checked selected-root construction, so
its lone examples use the selected-root frontend. Earlier cubic measurements
record their stated source revision and do not measure this routing change.
The adapter's source reifier preserves explicit coefficient aliases and
original divisor obligations before normalization. Closed values built with
`Selected.real` may be named using `def` in the same file. Across modules, use
`abbrev` or `@[expose] def` so the defining expression remains visible. For
supported sentences, a divisor must be proved nonzero before certificate
construction.

The next construction selects the positive root near 1.675 of `X³ − 4X + 2`.
Combining it with `√37` creates a degree-six common defining polynomial.
The frontend's single-witness and quadratic-norm producers decline that new
polynomial; the public multi-prime certificate route authenticates it before
the goal's root and sign checks.

```lean
private abbrev certificatePolynomial : Hex.ZPoly :=
  Hex.DensePoly.ofList [2, -4, 0, 1]
private abbrev certificateSquare : Hex.DyadicSquare :=
  ⟨Dyadic.ofIntWithPrec 112416129 26, 0, 24⟩

private theorem certificateChecked :
    certificatePolynomial.CheckedIrreducible :=
  Field.checkedIrreducible certificatePolynomial
    (.eisenstein 2 0)
    (by decide +kernel) (by decide)

private theorem certificateSquarefree :
    Hex.HasOnlySimpleRoots certificatePolynomial := by
  let : certificatePolynomial.CheckedIrreducible :=
    certificateChecked
  exact (HexRootsMathlib.hasOnlySimpleRoots_iff_separable
    certificatePolynomial (by decide)).mpr
    (Hex.ZPoly.CheckedIrreducible.separable
      certificatePolynomial)

private abbrev certificateRoot : Hex.RealAlgebraicNumber :=
  Selected.real certificatePolynomial certificateSquare
    (by decide +kernel) (by decide) (by rfl)
    (by decide) (by decide) certificateChecked
    certificateSquarefree (by decide +kernel)

set_option maxRecDepth 8192 in
set_option maxHeartbeats 5000000 in
example : ∀ x : ℝ,
    x ^ 2 + certificateRoot.toReal + Real.sqrt 37 > 0 := by
  rcf
```

The algebraic examples use the proved generic accepted-query soundness theorem
`HexRealRootsMathlib.Tarski.check_rootSum`. Their fixed-field certificate checks
and chosen-root identifications use only Lean's standard logical axioms.
See {ref "hex-number-field"}[HexNumberField] and
{ref "hex-real-algebraic"}[HexRealAlgebraic] for the underlying number APIs.

Visible checked conversions preserve the actual option branch.
`RealAlgebraicNumber.ofAlgebraic?` succeeds for a selected real or rational value,
or an element of `QAdjoin a.toAlgebraic` for a real algebraic generator `a`.
When applied to `AlgebraicNumber.I`, it returns
`none`, so `getD` denotes its stated fallback. An explicit `.re` projection
instead denotes the real part; the real part of `I` is zero.

```lean
example : ∃ x : ℝ,
    x = ((Hex.RealAlgebraicNumber.ofAlgebraic? Hex.AlgebraicNumber.I).getD
      (Hex.RealAlgebraicNumber.ofRat (3 / 2))).toReal ∧ 1 < x ∧ x < 2 := by rcf

example : ∀ x : ℝ,
    x ^ 2 + Hex.AlgebraicNumber.I.re.toReal ≥ 0 := by rcf

example : ∀ x : ℝ,
    x ^ 2 + (4 : Hex.RealAlgebraicNumber).toReal +
      ((-3 : Int) : Hex.RealAlgebraicNumber).toReal > 0 := by rcf
```

The frontend also lowers visible real-algebraic arithmetic, inverses, natural
powers and integer casts using the number library's interpretation theorems.
Supported projections include selected real values, rational values, real
`QAdjoin` coordinates and sums of supported projections. This recognition
does not provide a general procedure for arbitrary complex expressions or
opaque conversion code. Original rational, real-algebraic and supported
real-field divisors remain obligations, including divisors inside an unused
`getD` fallback, before any branch is simplified. Division over other carriers,
raw `PolyQuot.div`/`inv`, integer powers and divisions depending on a binder
inside conversions are rejected.

A fresh-module comparison of the cubic reciprocal uses identical imports and
shared source setup for `Coefficients.ofField` and direct
`QAdjoin.toAlgebraicNumber` conversion. At source `b10ded789`, Lean
`v4.35.0-rc3` on shared `chungus2` CPU 18, four adjacent alternating AB/BA
rounds give median build times 10.441 and 10.443 seconds respectively, with
median peak RSS 3.29 GiB in both arms. The median paired direct-minus-wrapped
margin is +0.013 seconds; margins range from −0.045 to +0.071 seconds and do
not resolve a cost difference. Both private olean files contain 603,000 bytes.
These are fresh-module `lake build` wall times, including Lake startup and
replay, for one identity whose specialized equality atom is zero. There is
no import-only arm or root-search scaling claim.
The [report and retained samples](https://github.com/kim-em/hex-dev/blob/main/reports/hexrcf-division-proofs.md)
record all eight arms and host activity, and retain the separate `b0c583792`
snapshot. Each measurement is tied to its recorded source; later routing and
environment cleanup are outside those measurements. They do not isolate the
cost of checking separate source and target sign tables or establish general
extension performance or total algebraic search.

A separate [fixed-field input report](https://github.com/kim-em/hex-dev/blob/main/reports/hexrcf-scaling-proofs.md)
retains 24 matched-import builds varying variable degree, atom count and integer
coefficient width independently. These root-free carriers do not measure
precision or nested depth. A representative two-field further-root proof,
`∃ x : ℝ, x² = Real.sqrt 2 ∧ 1 < x ∧ x < Real.sqrt 3`, takes 43.672 seconds
at its recorded source on leased CPU 14, including build and profiler overhead.
That source used full Sturm-query quotation and predates interval signs; this
profile does not attribute the cost of the current default.
Its exclusive kernel type-checking category totals 30.1 seconds; the smaller
literal-replay category excludes those child checks. The report retains source
identities, memory, serialized sizes, unique syntax and expanded-reference
counts. It does not claim a complexity law or complete Phase-4 attestation.

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
the shared proved root-sum theorem. Import `HexSignDetMathlib.ThomRoots` for
{name}`Hex.SignDet.Descriptor.buildRoots_success`, which proves actual success
on every valid domain. {name}`Hex.SignDet.Descriptor.buildRoots_roots` proves
that the returned list contains every root exactly once, in strictly increasing
mathematical order. These generic theorems include finite/infinite bounds,
noninjective coefficient storage and non-Archimedean fields.

Infinitesimal coefficients can arise inside the decision procedure. Here ε is
positive and smaller than every positive rational. The roots 0 and ε have no
rational separator. Root enumeration uses their derivative signs to order them,
and the selected-root API distinguishes their polynomial signs exactly.

```lean
private def infinitesimalRootsPasses : Bool :=
  let epsilon : Hex.RationalFn Rat := Hex.RationalFn.X
  let sign := Hex.OrderedFn.Infinitesimal.sign Sturm.orderSign
  let x : DensePoly (Hex.RationalFn Rat) :=
    DensePoly.ofCoeffs #[0, 1]
  match Descriptor.buildRoots sign 7
      (x * (x - DensePoly.C epsilon))
      (.finite (-1)) (.finite 1) with
  | .ok (some roots) =>
    roots.map (fun d => d.raw.signs) == [[-1, 1], [1, 1]] &&
      roots.map (fun d => d.signAt x) == [0, 1] &&
      roots.map (fun d => d.signAt (x - DensePoly.C epsilon))
        == [-1, 0]
  | _ => false

#guard infinitesimalRootsPasses
```

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
    one.compare two == .lt && two.compare one == .gt
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
    | .ok result =>
      result.common.check 7 sqrtTwoRoot.head sharedRoot.head &&
        (left.buildOrder right).toOption == some .eq &&
        left.compare right == .eq
    | _ => false
  | _, _ => false

#guard commonRootPass
```

The same defining polynomial can name one root through different intervals.
Both `(0,2)` and `(1,2)` contain only the positive root of `x² − 2`.
The comparison completes these two descriptions and returns equality directly.
It checks that construction succeeded before inspecting the total result.

```lean
private def sameHeadPass : Bool :=
  match Descriptor.validate Sturm.orderSign 7 sqrtTwoRoot,
      Descriptor.validate Sturm.orderSign 7
        {sqrtTwoRoot with
          lower := .finite 1
          upper := .finite 2
          indices := []
          signs := []} with
  | some left, some right =>
    (left.buildOrder right).toOption == some .eq &&
      left.compare right == .eq
  | _, _ => false

#guard sameHeadPass
```

{name}`Hex.SignDet.Descriptor.compare` is the total root-order operation.
It completes partial descriptors and compares their encodings directly when the
stored defining polynomials agree, even across different intervals. For different
heads it retains the original root selections when
changing their defining polynomial. Import `HexSignDetMathlib.ComparisonProducer`
for {name}`Hex.SignDet.Descriptor.compare_correct` and the equality and strict-order
equivalences {name}`Hex.SignDet.Descriptor.compare_eq_iff`,
{name}`Hex.SignDet.Descriptor.compare_lt_iff` and
{name}`Hex.SignDet.Descriptor.compare_gt_iff`.
{name}`Hex.SignDet.Descriptor.buildComparison_success` proves that the actual
common-polynomial constructor, both joint re-encodings and the full-word
comparison succeed under lawful coefficient interpretations. The total operation's
internal error branch emits a diagnostic and returns `eq`.
{name}`Hex.SignDet.Descriptor.compare_ofError` proves that exact fallback value;
{name}`Hex.SignDet.Descriptor.buildOrder_roots` proves actual success and excludes
that branch under the coefficient laws. The executable operation requires
ordinary coefficient operations and signs, without a companion proof package.
The proofs require canonical zero, allow other stored values to have multiple
representations, and apply to arbitrary ordered real
closed fields, including fields with infinitesimals. They use the proved shared
root-sum semantics and Tau Ceti Thom identity/order foundations.

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

The converted coordinates can also be coefficients of a new sign/root problem.
Write a = √2 and b = √3 in that common field. At the roots of
`(x − a)(x − b)`, the ordered queries `x − a`, `x − b`, and `a − b` have
signs `(0,−,−)` and `(+,0,−)`, each once. The impossible pattern `(0,0,−)`
has count zero. The same check enumerates a before b and compares roots
selected by `x − a` and `x − b`. Both derivative words are `[+]`; their
equality does not identify roots of different defining polynomials.
The sign function below evaluates a field coordinate on the
common generator's certified enclosure, refining it when needed.

```lean
private def commonFieldTablePass
    (common : Hex.QAdjoin.Presentation) : Bool := Id.run do
  if real : common.generator.isReal = true then
    let sign : Hex.QAdjoin common.generator → Int :=
      fun value => value.signApprox real
    let some a := common.entries[0]? | return false
    let some b := common.entries[1]? | return false
    let x : DensePoly (Hex.QAdjoin common.generator) :=
      DensePoly.ofList [0, 1]
    let qa := x - DensePoly.C a
    let qb := x - DensePoly.C b
    let head := qa * qb
    let some table := determine sign 7 head .negInf .posInf
      [qa, qb, DensePoly.C (a - b)] | return false
    let .ok (some roots) :=
      Descriptor.buildRoots sign 7 head .negInf .posInf
      | return false
    let some left := Descriptor.validate sign 7
      ⟨7, qa, .negInf, .posInf, [1], [1]⟩
      | return false
    let some right := Descriptor.validate sign 7
      ⟨7, qb, .negInf, .posInf, [1], [1]⟩
      | return false
    return common.generator.p.natDegree == 4 &&
      table.rows.toList ==
      [([0, -1, -1], 1), ([1, 0, -1], 1)] &&
      table.count [0, 0, -1] == 0 &&
      roots.map (fun d => d.signAt qa) == [0, 1] &&
      roots.map (fun d => d.signAt qb) == [-1, 0] &&
      left.compare right == .lt &&
      right.compare left == .gt
  else return false

#guard commonFieldTablePass
  (Hex.QAdjoin.common independentInputs)
```

Here the common generator has degree four. Coefficient arithmetic uses actual
`QAdjoin` coordinates. The sign function handles rational constants directly and
uses interval evaluation for nonconstant coordinates. If its first two probes are
inconclusive, an integer polynomial satisfied by the coordinate gives a proven
precision bound for the final interval probe.
The theorem {name}`Hex.QAdjoin.signApprox_spec` proves that it returns
the sign in the selected real embedding. The more extensive enumeration,
comparison, re-encoding and replay checks run in the conformance suite against
an independent exact algebraic-number oracle.
The value-preservation theorem {name}`Hex.QAdjoin.common_get` connects the
coordinates to the independently selected original algebraic numbers.
The table, selected-sign, and comparison correctness theorems apply to that
embedding; their proofs use only Lean's standard logical axioms and the proved
shared query and Tau Ceti foundations.

The sign-table and descriptor examples run checked producers and finite
certificate checks; the changed sign vector above is rejected. The companion
proves complete real-root counts, selected-root identity and signs using the
proved root-sum theorem `HexRealRootsMathlib.Tarski.check_rootSum`.
The full-word comparison uses Tau Ceti’s delivered Thom identity and order
theorems through the companion. {name}`Hex.SignDet.Comparison.order_root`
proves that all three orders returned by an accepted comparison agree with the
original selected roots. {name}`Hex.SignDet.Descriptor.buildComparison_success`
proves that the actual comparison constructor succeeds;
{name}`Hex.SignDet.Descriptor.compare_correct` gives the result of the total
operation. Universal root-list production and mathematical sorting are also
proved. The common-field conversion preserves the selected algebraic values by
the proved `QAdjoin.common_get` theorem.

# Specialization and ordinary real enclosures
%%%
tag := "hex-rcf-specialization-enclosures"
%%%

The explicit preparation API is
{name}`Hex.RCF.RealCoefficients.Coefficients.prepare`. It returns authenticated
fixed-field coordinates in the original coefficient order, their identities
with the closed source expressions, and every original divisor before
cancellation. Rational-only sources remain with the existing base solver;
unsupported exact sources return a structured decline, while authentication,
search and kernel failures are terminal.

{name}`Hex.RCF.RealCoefficients.Coefficients.Environment.proveReplay` constructs
and quotes a finite certificate through the public
{name}`Hex.RCF.RealCoefficients.Replay.check_sound` theorem, then checks the proof
against the original goal. A failed attempt restores caller metavariables.
Before production, the API binds the polynomial, selected root, matrix,
quantifier, coefficients and divisor coordinates to their stored expressions.
It checks irreducibility, source and valuation proofs at their required types. Edited records fail input validation before a
false verdict. Validation-only checks leave no unused theorem declarations.
The tactic assembles its freshly constructed data through a private path;
the dispatcher checks its complete original-goal proof. The comparison option
`rcf.algebraic.validateFresh` repeats public validation for fresh tactic data
and defaults to false. Public preparation and replay always validate editable
inputs independently of this comparison control.
The existing `rcf` tactic retains its documented quotation options.

{name}`Hex.RCF.RealCoefficients.Replay.Input` records the coefficient order,
shared formula, quantifier, original divisor coordinates and context. Its type
fixes the defining polynomial and the selected root. Domain restrictions remain
formula atoms. {name}`Hex.RCF.RealCoefficients.Replay.build` uses bounded root/cell
production and checks all original divisors before searching.
{name}`Hex.RCF.RealCoefficients.Replay.check` reads only frozen evidence, returning
an accepted Boolean or a structured binding, divisor, evidence or unresolved
error. It never repeats root isolation, gcd or sign search. An accepted false
verdict is diagnostic and provides no proof of the user's goal.

{name}`Hex.RCF.RealCoefficients.Replay.check_domains` proves that every retained
original divisor is nonzero at the selected embedding, even for a zero atom or
an empty domain. {name}`Hex.RCF.RealCoefficients.Replay.check_spec` identifies the
accepted Boolean with the fixed-field real sentence.

```lean
open Hex Hex.RCF.RealCoefficients

example {p : ZPoly} {s : DyadicSquare}
    {hw : atomWitness p s}
    {hp : (mahlerPrec p : Int) ≤ s.prec}
    [ZPoly.CheckedIrreducible p]
    {Ctx : Type} [DecidableEq Ctx]
    (input : Replay.Input p s hw hp Ctx n)
    (cert : Replay.Certificate p s hw hp Ctx n)
    (accepted : Replay.check input cert = .ok true) :
    input.toProp :=
  Replay.check_sound input cert accepted
```

For an already authenticated exact field,
{name}`Hex.RCF.RealCoefficients.Replay.buildTotal` uses the existing complete
producer rather than a finite refinement limit. It preflights every original
divisor before production and preserves false as a diagnostic.
{name}`Hex.RCF.RealCoefficients.Replay.buildTotal_spec` proves that each valid
input produces an accepted correct verdict, independently of the direct
proposal depth. The nonzero-divisor hypothesis below describes valid input;
certificate acceptance and the verdict are conclusions.

```lean
example {p : ZPoly} {s : DyadicSquare}
    {hw : atomWitness p s}
    {hp : (mahlerPrec p : Int) ≤ s.prec}
    [ZPoly.CheckedIrreducible p]
    {Ctx : Type} [DecidableEq Ctx]
    (input : Replay.Input p s hw hp Ctx n)
    (real : s.meetsRealAxis = true) (depth : Nat)
    (domains : ∀ divisor ∈ input.divisors, divisor ≠ 0) :
    ∃ cert value,
      Replay.buildTotal input real depth = .ok cert ∧
      Replay.check input cert = .ok value ∧
      (value = true ↔ input.toProp) :=
  Replay.buildTotal_spec input real depth domains
```

{name}`Hex.RCF.RealCoefficients.Coefficients.Environment.proveTotalReplay`
quotes the resulting finite evidence and transports the accepted true verdict
to the exact original target. Its fresh Ioc proof regression uses direct depth
zero; the generated proof contains no producer or search call. This explicit
API retains raw carrier production and does not change the bounded `rcf`
default. It does not prove recognition or irreducibility quotation complete
for every closed algebraic source, or make Lean elaboration resource limits
unbounded. The total producer has no finite search budget. Native production
runs synchronously without heartbeat or cancellation polls inside the call;
cancellation is polled after the production result is matched in meta code. Quotation and
kernel checking retain Lean’s ordinary resource limits.

The explicit finite API uses linear recorded-sign lookup and one kernel
decision. The tactic's indexed lookup and split/combined replay options govern
its separate quotation path. Both paths use the same literal evidence reduction
lemmas. Original guard coordinates remain in the finite envelope even after
cancellation; exact nonvanishing and their source identities are checked
separately from the quantifier fold.

This fixed-field API covers the documented exact algebraic fragment. The
caller-registration path below has its own frozen bounds and subject/version
bindings; it does not supply a total field for general root algorithms. General
frontend certification and tower realization remain incomplete.

The shared formula records coefficient parameters and the quantified variable.
Specialization evaluates the parameters in their fixed real embeddings and
combines equal powers of the variable. Leading terms can disappear when
independently named coefficients denote the same value.
{name}`Hex.RCF.RealCoefficients.Specialize.degree` proves that the resulting
polynomial's degree agrees with its real interpretation, including constants
and zero. {name}`Hex.RCF.RealCoefficients.FieldSpecialize.literal_degree` gives
the same guarantee for the literal fixed-field compiler.

{name}`Hex.RCF.RealCoefficients.Specialize.prepare` and
{name}`Hex.RCF.RealCoefficients.FieldSpecialize.prepare` retain all atoms in the
shared traversal, including repeated atoms, zero polynomials and domain guards.
Their `prepare_eval` and `prepare_degrees` laws apply after coefficient
cancellation; filtering zero polynomials for carrier construction does not
remove their Boolean atoms or original divisor conditions.

```lean
open Hex.RCF.RealCoefficients

example (values : Fin n → Hex.RealAlgebraicNumber)
    (p : Hex.RealFormula.Poly (n + 1)) :
    ((HexPolyMathlib.toPolynomial
      (Specialize.polynomial values p)).map
      Hex.RealAlgebraicNumber.toRealHom).natDegree =
      (Specialize.polynomial values p).natDegree :=
  Specialize.degree values p

example (root : Hex.RealAlgebraicNumber)
    (precision : Nat) :
    (rootInterval root precision).isSome = true := by
  obtain ⟨interval, produced, _, _, _⟩ :=
    rootInterval_spec root precision
  rw [produced]
  rfl
```

{name}`Hex.RCF.RealCoefficients.rootInterval_spec` also proves that the root
lies strictly between the returned endpoints and that their distance is at
most `4 · 2⁻precision`. The extra dyadic margin keeps exact rational roots,
including zero, inside an interval of positive width.
{name}`Hex.RCF.RealCoefficients.rootInterval_progress` proves that every
precision schedule tending to infinity eventually reaches any positive width
request. These points and endpoints are ordinary real numbers. The algebraic
tactic doubles fallback precision within its configured refinement budget.

{name}`Hex.RCF.RealCoefficients.proposeIsolations_isSome_iff` establishes
finite proposal production for exactly the nonzero dense heads. The canonical
solver receives exactly the interpreted polynomial. Zero has a universal
root set; a nonzero constant has an empty finite set. This is the direct
canonical-carrier API. The tactic specializes to fixed-field coordinates,
squarefrees its carrier and checks proposed intervals over those coordinates;
its fallback uses these same strict enclosures.

{name}`Hex.RCF.RealCoefficients.isolateAt_progress` proves that every nonzero
squarefree canonical head eventually yields accepted isolation evidence along
any precision schedule tending to infinity. Separation, root-free endpoints,
complete root coverage and interval counts are derived using the owner's
complete sorted root list and the literal Sturm checker.
{name}`Hex.RCF.RealCoefficients.FieldBuild.isolateAt_progress` gives the same
guarantee over original fixed-field coordinates at a checked selected real
embedding, including the complete selected-field fallback after bounded direct
search fails. `FieldBuild.roots_meaning` identifies the owner's root output
with the original real polynomial; `roots_sorted` and `roots_finite` give
its distinct ordered finite list for every nonzero head. `proposeRoots_spec`
and `proposeRoots_accepted` derive complete coverage and accepted replay from
strict enclosures of that list.
The corresponding `isolate` entry points double successive precisions and
return isolation evidence together with its checker acceptance proof and
exact binding to the builder that produced the shared squarefree chain.
The preferred fixed-field search and complete root solving run once.
The fallback passes the polynomial to the existing number-field root driver
in its selected presentation. Refinement repeats interval construction and gap checks;
the accepted Sturm replay evidence is built once after the gaps pass.
These are compiled producers. A quoted proof must recheck the emitted literal
certificate in the ordinary kernel.
Their termination follows from these progress laws for nonzero squarefree
inputs. The bounded `build`/`isolateAt` interfaces remain available for callers
that choose an explicit precision.

{name}`Hex.RCF.RealCoefficients.FieldRootSigns.Table.build_success` proves
that atom-query production succeeds after isolation construction succeeds.
Queries retain the shared squarefree chain and are checked at the same root
interval and original head.
{name}`Hex.RCF.RealCoefficients.FieldBuild.isolateFormula_queries` composes
this query production with the total formula isolation entry point.

{name}`Hex.RCF.RealCoefficients.RadicalCert.build_success_real` proves that
the actual bounded derivative-gcd quotient search produces accepted radical
evidence for every nonzero head under the checked real arithmetic interpretation.
{name}`Hex.RCF.RealCoefficients.RadicalCert.build_squarefree` derives
squarefreeness of the returned core from the producer's exact quotient and the
owner's Yun invariant. It is not a hypothesis supplied to the radical checker.
Nonzero constants are included; zero still has no finite root list.
The core need not be monic: for `X³` the raw derivative gcd yields `X/3`.

The executable `RadicalCert.reduce` entry point takes the proved progress law,
returns the builder's certificate and retains exact production binding plus
literal acceptance. The real interpretation is used only in the proof, so a
fixed field's noncomputable real embedding is not passed to compiled arithmetic.

{name}`Hex.RCF.RealCoefficients.FieldBuild.isolateFormula` composes this
reduction with precision search for the complete shared formula carrier,
including repeated/common roots, zero atoms and formulas without atoms.
The shared formula keeps its guard atoms, whose nonzero endpoint polynomials
enter the carrier. Squarefreeness is derived before isolation; it is not an
extra admission required from the caller.
The complete library pipeline consumes this root envelope through
{name}`Hex.RCF.RealCoefficients.FieldBuild.produce`. This compiled producer
constructs the radical, complete root isolations, every atom query and a finite
rational sign table, returning checker acceptance and a recorded hit for every
replay or open-cell sign operand. Exact duplicate coordinate keys share one
sign-table entry. The chosen literal square fixes the rational count-one
interval used for all coordinate signs. The producer captures a prepared domain
as data before building its sign closure.
{name}`Hex.RCF.RealCoefficients.Field.prepareSign_spec` proves that prepared
rational Tarski queries give the selected real embedding's signs. Search does
not isolate a new algebraic number for each coordinate sign.
{name}`Hex.RCF.RealCoefficients.FieldBuild.build_progress` also proves success
of the bounded builder along every cofinal precision schedule. That builder
also captures its prepared rational sign domain once, rather than converting
each coordinate into a separate algebraic number.

The `Result.allValue` and `Result.anyValue` compiled folds use only recorded
signs. Their `forall_decision` and `exists_decision` theorems prove that the
strict Boolean result is defined and agrees with the real quantified formula.
A valid envelope for a false sentence yields a false diagnostic; it is never
assigned as a proof. These laws cover fixed-field algebraic decision after
source authentication. They do not assert total registered-constant search or
unbounded elaboration of every quoted proof. Kernel quotation still checks the
literal certificate and the exact original-goal equivalence. General nested
joint realization and the remaining adapter evidence obligations are separate.

```lean
example : ∀ x : ℝ,
    x ^ 2 - 2 * Real.sqrt 2 * x + 2 ≥ 0 := by rcf

example : ∃ x : ℝ,
    x ^ 2 = Real.sqrt 2 ∧ 1 < x ∧ x < 2 := by rcf
```

The first example has a repeated root at the selected positive square root;
the second produces a further algebraic root and checks simultaneous sign
conditions on that section. Both use the optional algebraic handler, with
ordinary real sectors between its root sections. The complete `produce` API
accepts a direct bisection depth, defaulting to 256, before its proved
selected-field fallback. Both the complete producer and frontend retain that
field presentation and share its complete root output across precision attempts.
The owner's root driver still constructs exact algebraic roots; this is not
a claim that root solving has no exactification cost.
The existing bounded isolation API retains its
128-level default.
The direct proposal can also fail at its bounded bracketing, pivot or gap
searches; no unchecked interval is accepted.

The tactic uses `produceWithin` with `rcf.algebraic.directDepth` (default 256)
and `rcf.algebraic.maxDoublings` (default 10). The latter bounds fallback
interval attempts at precisions 1, 2, 4, …; a zero limit disables fallback.
This frontend calls the existing fixed-field root driver directly and retains
its selected coordinates, avoiding a redundant common-field reconstruction.
Exhaustion reports `rcf: algebraic interval refinement budget exhausted` and
is terminal. Rejected construction/replay has a different terminal diagnostic.
The complete library producer retains raw cores and its progress/decision laws
are unaffected by the frontend budget or the tactic's monic default. Increasing
the limits permits further refinement;
it does not bypass kernel replay. Lean cancellation is checked before and
after native production. Individual native root computations run until they
return and do not check Lean's cancellation token or elaboration heartbeats.


# Ordinary samples over a selected field
%%%
tag := "hex-rcf-native-samples"
%%%

The native tower API can find roots and choose ordinary real samples over an
already selected algebraic coefficient field. Start with a checked
{name}`Hex.SignDet.Descriptor`; its polynomial, interval and derivative signs
fix the selected root. {name}`Hex.RealClosure.Tower.Model.base` interprets the
rational base, and {name}`Hex.RealClosure.Tower.Model.adjoin` preserves that selection in the child field.
This real interpretation is used in correctness proofs; compiled arithmetic
uses the owner's native stored values.

{name}`Hex.RCF.RealCoefficients.RepresentationSpecialize.prepare` substitutes
those values into the shared formula syntax using their actual arithmetic.
It groups terms by the bound-variable exponent after evaluating coefficient
coordinates directly. Its
{name}`Hex.RCF.RealCoefficients.RepresentationSpecialize.prepare_eval` law
needs arithmetic preservation and zero reflection;
{name}`Hex.RCF.RealCoefficients.RepresentationSpecialize.prepare_degrees`
needs zero reflection alone. These permit unequal stored nonzero expressions
with the same real value. They retain repeated atoms, cancelled zero polynomials and
the two atoms describing a half-open domain. No field instance on native
stored expressions is required.

For example, the following API input describes `X² = α` in `(1, 2]`, with
`α` the fixed selected generator. The repeated square has the same roots.

```lean
open Hex Hex.RealClosure Hex.RealClosure.Tower
open Hex.RCF.RealCoefficients

def sampleRegistry : BaseContext.Registry := fun _ => none
abbrev sampleBase :=
  Context.base (BaseContext.rational sampleRegistry)

noncomputable def sampleReal : Model sampleBase ℝ :=
  Model.base (BaseContext.rational sampleRegistry)
    (Rat.castHom ℝ) ratSign

def sampleFormula : Hex.RealFormula.QF 2 :=
  let x : Hex.RealFormula.Poly 2 := MvPoly.X 1
  let q := x ^ 2 - MvPoly.X 0
  .and (.atom ⟨q, .eq⟩) (.and (.atom ⟨q ^ 2, .ge⟩)
    (.and (.atom ⟨1 - x, .lt⟩) (.atom ⟨x - 2, .le⟩)))

abbrev SampleSelection :=
  Hex.SignDet.Descriptor sampleBase.Value
    Tower.Signature sampleBase.sign sampleBase.signature

example (d : SampleSelection) (x : ℝ) :
    let field := sampleBase.adjoin d
    let realModel := sampleReal.adjoin d
    let values := fun _ : Fin 1 => field.generator
    let prepared := RepresentationSpecialize.prepare
      values sampleFormula
    prepared.map (RepresentationSpecialize.evaluate
      realModel.value realModel.zero_iff x) =
      sampleFormula.polys.map (fun q => q.eval
        (Hex.RealFormula.append
          (fun i => realModel.value (values i)) x)) := by
  dsimp only
  exact RepresentationSpecialize.prepare_eval _ _
    (sampleReal.adjoin d).one (sampleReal.adjoin d).add
    (sampleReal.adjoin d).mul (sampleReal.adjoin d).nat
    (sampleReal.adjoin d).neg _ sampleFormula x
```

{name}`Hex.RealClosure.Tower.Sample.family` takes the specialized polynomial
list. {name}`Hex.RealClosure.Tower.Sample.Family.cells_unique` places every
real point in exactly one section or sector, and
{name}`Hex.RealClosure.Tower.Sample.Family.cell_signs` gives every polynomial's sign at that
same point. Each sector has an ordinary sample in its own compatible context;
{name}`Hex.RealClosure.Tower.Sample.Family.sector_signs` proves the entire sign vector throughout that sector. Here is
the direct same-point conclusion for any family interpreted in `ℝ`:

```lean
example {registry : BaseContext.Registry}
    {parent : Context registry}
    {polynomials : List parent.Poly}
    (family : Tower.Sample.Family parent polynomials)
    (original : Model parent ℝ)
    (sample : Tower.Sample parent)
    (present : sample ∈ family.sectors) :
    ∃ realization : Conversion.Model sample.input original,
      sample.cell.Mem realization.target
        (realization.target.value sample.value) ∧
      sample.signs polynomials = polynomials.map (fun p =>
        (SignType.sign
          ((HexPolyMathlib.Interpret.interpret
            original.value original.zero_iff p).eval
              (realization.target.value sample.value))
          : Int)) := by
  obtain ⟨realization, checked, signs⟩ :=
    family.sector_signs original sample present
  have inside := (Cell.contains_correct realization.target
    sample.cell sample.value).mp checked
  exact ⟨realization, inside, signs _ inside⟩
```

Root sections use their selected boundary as the real witness.
{name}`Hex.RealClosure.Tower.Sample.Family.sections_correct` checks all signs
at that boundary, with the original coefficient interpretation fixed:

```lean
example {registry : BaseContext.Registry}
    {parent : Context registry}
    {polynomials : List parent.Poly}
    (family : Tower.Sample.Family parent polynomials)
    (original : Model parent ℝ)
    (sample : Tower.Sample parent)
    (present : sample ∈ family.sections) :
    ∃ root ∈ family.boundaries,
      sample = Tower.Sample.ofRoot root ∧
      sample.cell.contains sample.value = true ∧
      sample.signs polynomials = polynomials.map (fun p =>
        (SignType.sign
          ((HexPolyMathlib.Interpret.interpret
            original.value original.zero_iff p).eval
              (root.denote original)) : Int)) := by
  exact family.sections_correct original sample present
```

The native root producer already provides complete coverage, multiplicities
and order through {name}`Hex.RealClosure.Tower.Context.roots_spec` and
{name}`Hex.RealClosure.Tower.Context.roots_sorted`. For the
positive selected √2 fixture, the four source atoms above have four distinct
boundaries, four sections and five sectors; the repeated polynomial adds no
extra boundary. The negative selected √2 control has only the two guard
boundaries and rejects the root equation everywhere. A separate mixed-input
control sends a literally duplicated atom, a zero atom and a leading-cancelled
polynomial through the native root/sample producer. The cancelled polynomial
adds a section at zero. Every cell sign and the strict/non-strict domain
relations are checked through the shared Boolean fold.
Another control uses the selected root of `(X² − 2)(X − 3)` in `(1, 2)`.
Its distinct stored expressions `α` and `α³/2` have zero difference; their
leading-term cancellation still produces the correct degree and every cell sign.

{name}`Hex.RCF.RealCoefficients.Samples.run` connects this native family to
the shared Boolean formula and its one real quantifier. It prepares the atom
list once, evaluates a complete sign row for each section or sector, and uses
the existing strict quantifier fold. The result is `some true` or `some false`
under an actual ordinary-real predecessor model. False is a diagnostic result.
{name}`Hex.RCF.RealCoefficients.Samples.run_spec` proves exactly the shared
{name}`Hex.RealFormula.Prenex.toProp` meaning at the fixed coefficient values:

```lean
example (d : SampleSelection) :
    let field := sampleBase.adjoin d
    let realModel := sampleReal.adjoin d
    let values := fun _ : Fin 1 => field.generator
    ∃ result,
      Samples.run values sampleFormula .existsReal =
        some result ∧
      (result = true ↔ ∃ x : ℝ,
        sampleFormula.toProp (Hex.RealFormula.append
          (fun i => realModel.value (values i)) x)) := by
  dsimp only
  exact Samples.run_spec (sampleReal.adjoin d)
    (fun _ : Fin 1 => (sampleBase.adjoin d).generator)
    sampleFormula .existsReal
```

All coefficient coordinates belong to one native parent context, and they
may be different values there. Independently constructed fields require
proved conversion into that common context first. The
{name}`Hex.RCF.RealCoefficients.Samples.section_formula` and
{name}`Hex.RCF.RealCoefficients.Samples.sector_formula` laws interpret the
whole Boolean formula at the same selected boundary or ordinary sector
point; {name}`Hex.RCF.RealCoefficients.Samples.cell_formula` applies throughout
the cell. These compose actual root coverage, cell membership and sign laws,
without adding them as unproved assumptions.

The compiled regressions distinguish positive and negative selected √2 in
`∀ x, x² + α > 0`, and swap two distinct coefficient coordinates to check
that their order changes the answer. They retain repeated/common roots,
zero and cancelled atoms, all six comparisons and Boolean operations, and
equal, reversed and half-open domains. Fresh modules check the public
semantics and its standard axiom inventory. These are correctness regressions;
no timing improvement is claimed for this composition.

For an existing {name}`Hex.RealAlgebraicNumber`,
{name}`Hex.RCF.RealCoefficients.NumberField.run` constructs the native parent context
with the owner's checked number-field factory. Its inputs are the original
{name}`Hex.QAdjoin` coordinates. The factory retains the generator's minimal
polynomial and selected real embedding; packing preserves that embedding.
{name}`Hex.RCF.RealCoefficients.NumberField.value_eq_ofField` identifies the
native interpretation with the frontend's existing
{name}`Hex.RCF.RealCoefficients.Coefficients.ofField` conversion. The following
public law covers every shared one-quantifier formula at those converted
original real values:

```lean
example (generator : Hex.RealAlgebraicNumber)
    (registry : Hex.RealClosure.BaseContext.Registry)
    (values : Fin n → Hex.QAdjoin generator.toAlgebraic)
    (formula : Hex.RealFormula.QF (n + 1))
    (quantifier : Hex.RealFormula.Quantifier) :
    ∃ result,
      NumberField.run generator registry values
          formula quantifier = some result ∧
      (result = true ↔
        (Hex.RealFormula.Prenex.quant quantifier
          (.matrix formula)).toProp
          (fun i => (Coefficients.ofField generator
            (values i)).toReal)) := by
  exact NumberField.run_coefficients generator registry
    values formula quantifier
```

The compiled API regressions select both roots of `X² − 2` and the positive
root of `X³ − 2`, then find further roots of `x² − α` over each original
number field. They test the complete conjunction with the squared atom
`(x² − α)² ≥ 0`, whose repeated roots are shared with `x² − α`, and the
half-open guards `1 < x` and `x ≤ 2`.
Positive √2 and the cube root return true; negative √2 returns false.
Further controls select all three roots of the totally real
cubic `X³ − 3X + 1`, a non-monic quadratic and a rational generator. They
compute the irrational coordinate `α² − α` in both conjugates of `X² − 2`,
swap the coordinate order, and compare a degree-two coordinate with its
negative in the cubic field. They cancel a leading term and retain zero atoms
and exact endpoint, equal and reversed domains. All six comparisons and both
quantifiers are exercised. The public correctness, totality and truth laws
have only the standard three axioms. These compiled controls are diagnostic
examples; they do not supply frozen certificates or quoted source proofs.
This API performs root production and does not complete generic replay or
frontend authentication for that backend. No timing improvement is claimed.

All coordinates supplied to this entry point belong to the same original
number field. Each `run` call constructs its presentation anew.
{name}`Hex.RCF.RealCoefficients.NumberField.runWith` reuses one checked
presentation across formulas; its
{name}`Hex.RCF.RealCoefficients.NumberField.runWith_spec` law preserves the
original selected coordinate values directly. A compiled control evaluates
both quantifiers over the same retained presentation.

Independently constructed contexts can be gathered through the owner's
{name}`Hex.RealClosure.Tower.Shared.gather?` operation. Its checked maps retain
each original owner in input order; repeated owners can reuse the same cached
predecessor. {name}`Hex.RCF.RealCoefficients.Gather.values` applies those maps
to the ordered coefficient coordinates. No new quotient-field representation
or field instance on stored expressions is introduced.

The following computation constructs √2 and √3 independently, gathers them,
and checks `∃ x, x² = √2 ∧ 1 < x ∧ x < √3`. Its variable roots are therefore
computed over the already gathered algebraic coefficient field.

```lean
private def gatheredRoots : Bool := Id.run do
  let x : sampleBase.Poly := DensePoly.ofCoeffs #[0, 1]
  let raw := fun n =>
    ({context := sampleBase.signature,
      head := x * x - DensePoly.C n,
      lower := .finite 1, upper := .finite (1 + 1),
      indices := [], signs := []} :
        SignDet.RawDescriptor sampleBase.Value
          Tower.Signature)
  let some first := SignDet.Descriptor.validate
      sampleBase.sign sampleBase.signature
      (raw (1 + 1)) | return false
  let some second := SignDet.Descriptor.validate
      sampleBase.sign sampleBase.signature
      (raw (1 + 1 + 1)) | return false
  let a := sampleBase.adjoin first
  let b := sampleBase.adjoin second
  let owners := [a.context, b.context]
  let some shared := Shared.gather?
      (.pack (BaseContext.rational sampleRegistry))
      owners | return false
  let coefficients : (i : Fin owners.length) →
      (owners[i]).Value := by
    change (i : Fin 2) →
      ([a.context, b.context][i]).Value
    exact Fin.cases a.generator
      (Fin.cases b.generator (fun i => Fin.elim0 i))
  let v : Hex.RealFormula.Poly 3 := Hex.MvPoly.X 2
  let formula := Hex.RealFormula.QF.and
    (.atom ⟨v ^ 2 - Hex.MvPoly.X 0, .eq⟩)
    (.and (.atom ⟨v - 1, .gt⟩)
      (.atom ⟨v - Hex.MvPoly.X 1, .lt⟩))
  return Samples.run (Gather.values shared coefficients)
    formula .existsReal == some true

#guard gatheredRoots
```

{name}`Hex.RCF.RealCoefficients.Gather.prepare_eval` proves the meaning of
every original atom after transport. {name}`Hex.RCF.RealCoefficients.Gather.run_spec`
relates native production to the shared quantified formula in the original
owner order. {name}`Hex.RCF.RealCoefficients.Gather.gather_subsequence` proves
actual gathering and decision production when each owner's registered keys form
an ordered subsequence of the supplied target's keys and its infinitesimal depth
does not exceed the target's. Thus an owner over `[β]` can enter a target over
`[α, β]`, retaining the same provider identity and version. Reordered or stale
keys do not satisfy this condition. The operation needs a provider realization
of the target and a real model of its base; it does not construct
a new registered base for incompatible owners or infer independence of named
constants. {name}`Hex.RCF.RealCoefficients.Gather.gather_spec` retains the
prefix-compatible API. For separately authenticated source models,
{name}`Hex.RCF.RealCoefficients.Gather.run_original` uses their factory equations
to establish agreement with the common model; no coefficient agreement is
assumed. Their complete theorem axiom inventories use only the standard three
axioms. These laws do not treat the computed Boolean above as a proof of a
source goal. The compiled controls also distinguish the two selected roots of
`X² − 2`, reverse coefficient order, retain a repeated owner, and check zero
and leading-term cancellation. Empty collections retain the rational case.

`Samples.run` performs production, including root finding. Its Boolean output
is not frozen certificate evidence. Turning it into a source-goal tactic
proof still requires checked literal context/root/sign data, exact source
coefficient identities and every original divisor guard. Its real-model
hypothesis does not supply a global real interpretation of symbolic
infinitesimals or discharge their required finite joint realization.

These are ordinary native producer APIs and their real correctness laws.
Integrating their output into frozen tactic replay still needs the owner's
checked literal context and predecessor-sign interfaces. The example proves
the simultaneous signs of these ordinary samples. General finite replay for
nested selected roots and successive infinitesimals still needs one ordinary
real assignment for the complete joint constraint set. Executable all-live
enlargement assembly and its frozen acceptance interfaces remain owner
obligations. Native gathering and shared cache/model transport are available
as above; they do not supply that general enlargement. Frozen context/sign
reconstruction and general joint realization still require the corresponding
owner interfaces.

# Ordinary witnesses from one infinitesimal replay
%%%
tag := "hex-rcf-infinitesimal-replay"
%%%

Internal sample data can contain one infinitesimal without treating it as a
real number. {name}`Hex.RCF.RealCoefficients.Realization.queries` specializes
every shared source atom in the fixed coefficient field and lifts its
coefficients as constant rational functions. It retains atom order, repeated
atoms and domain guards. {name}`Hex.RCF.RealCoefficients.Realization.signs`
proves that specialization at one ordinary parameter gives exactly the source
sign vector at one ordinary real point.

{name}`Hex.RCF.RealCoefficients.Realization.exists_real` combines an accepted
literal BKR replay, a count-one complete sign row and a true shared Boolean
formula. The fixed coefficient field must already have its supplied ordered
embedding into ℝ. The owner's finite realization law supplies one positive
ordinary parameter and one root satisfying all recorded signs together:

```lean
open Hex Hex.RCF.RealCoefficients in
example {F : Type} [Field F] [DecidableEq F]
    [LinearOrder F] [IsStrictOrderedRing F]
    (embedding : F →+* ℝ) (ordered : StrictMono embedding)
    (values : Fin n → F)
    (formula : Hex.RealFormula.QF (n + 1))
    (p : DensePoly (RationalFn F))
    (a b : Endpoint (RationalFn F))
    (r : SignDet.Replay (RationalFn F) Nat)
    (accepted : r.check
      (OrderedFn.Infinitesimal.sign OrderedFn.orderSign)
      7 p a b (Realization.queries values formula) = true)
    (condition : List Int)
    (one : (r.table accepted).count condition = 1)
    (truth :
      Samples.Row.eval formula condition = some true) :
    ∃ x : ℝ, formula.toProp (Hex.RealFormula.append
      (fun i => embedding (values i)) x) :=
  Realization.exists_real embedding ordered 7 values formula
    p a b r accepted condition one truth
```

The conformance example freezes the root of `X − (1 + ε)` and the complete
source guard conjunction `1 < x ∧ x ≤ 2`. Its two BKR children certify the
ordered row `[1, −1]`; the ordinary-kernel proof concludes that an ordinary real
witness satisfies the whole conjunction. A changed context or coefficient,
omitted BKR children, a false row and a truncated row are rejected. The
Tarski root interval has its own open endpoints, while the source's half-open
upper bound remains an atom. No root producer or approximation callback
supplies the frozen certificates.

This is a direct semantic API. Frontend quotation still needs the authenticated
coefficient identities, every original divisor proof and the original-goal
reification equivalence. It does not reconstruct arbitrary tower contexts,
provide a global real embedding of an infinitesimal field, or realize nested
selected roots with successive infinitesimals. Those require the complete
joint owner realization interface.

# A frozen row at an ordinary selected root
%%%
tag := "hex-rcf-selected-row"
%%%

{name}`Hex.RCF.RealCoefficients.SelectedFormula.checkRow` checks one complete
ordered source-atom row at one selected ordinary real root. Supply the fixed
parent's faithful real model, the authenticated coefficients, every original
divisor, the shared formula, the selected-root context and a literal sign
packet. Divisors are checked before the packet. A packet must match the exact
root and ordered specialized polynomial keys; its graph checks the claimed
signs together at that root.

A true row supplies one ordinary witness:

```lean
open Hex Hex.RealClosure Hex.RCF.RealCoefficients in
example {registry : BaseContext.Registry}
    {parent : Tower.Context registry}
    (original : Tower.Model parent ℝ)
    (values : Fin n → parent.Value)
    (guards : List parent.Value)
    (formula : RealFormula.QF (n + 1))
    (context : Algebraic.Context parent.Value Tower.Signature
      parent.sign parent.signature)
    (packet : Algebraic.SignEvidence parent.Value Tower.Signature)
    (accepted : SelectedFormula.checkRow original values guards
      formula context packet = .ok true) :
    ∃ x : ℝ, formula.toProp (Samples.valuation original values x) :=
  SelectedFormula.row_sound original values guards formula context packet accepted
```

{name}`Hex.RCF.RealCoefficients.SelectedFormula.row_domains` proves nonzero
values for the supplied divisors. The frontend must still authenticate their
source identities and retain divisors erased by cancellation. A false row
supplies a counterexample at that point through
{name}`Hex.RCF.RealCoefficients.SelectedFormula.row_false`; it does not decide
that an existential sentence is false. Malformed evidence and incomplete
rows retain separate diagnostics.

The frozen regression constructs the positive root α of `X² − 2`, proves
that its original value is `Real.sqrt 2`, and constructs a further selected
root of `X² − α` on `(1, 2)`. Its shared formula retains the equation and both
strict bounds, with the checked joint row `[0, 1, −1]`. The fresh source proof
concludes `∃ x : ℝ, x² = Real.sqrt 2 ∧ 1 < x ∧ x < 2`. The existing `rcf`
example proves the same sentence through the independent polynomial-quotient
path; the frozen regression exercises the native selected-field representation.

The regression restores the upper descriptor from parsed literal data and
structural graph expansion with `Descriptor.ofChecked`. It supplies checked
predecessor operations for both specialization and replay. Kernel diagnostics
reject native sign/root producers during root and row proof checking; zero
unresolved requests alone would not establish that property. Wrong coefficients,
reversed keys, a forged sign with unchanged keys and graph, a crossed context,
a stale version and an original zero divisor are rejected. Missing arithmetic
intermediates stay unresolved rather than yielding a Boolean verdict.

Rebuilding the complete frozen conformance fixture with owner dependencies warm
took about 140 seconds on the recorded shared host; its largest child used
about 8.8 GiB RSS. These are ordinary build observations, not a scaling or
speedup claim. They include parsing, root and row quotation, refusals and audits.

This is an ordinary selected-root row API, conditional on the supplied faithful
parent model. It provides neither complete root coverage nor a generic frontend
certificate producer, universal sentence decision or nested infinitesimal
realization. Source reification and original-goal transport remain obligations
of a caller integrating the API.

# Caller-supplied finite bounds
%%%
tag := "hex-rcf-registered-bounds"
%%%

The optional import also accepts a caller's registered closed real subject.
A {name}`Hex.RCF.RealCoefficients.Registration` contains an executable
approximation and a separate containment theorem for that exact subject.
The `rcf_constant` attribute registers its declaration. Registrations persist
beyond sections and through imports. Subjects match by
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

example : ∀ x : ℝ,
    x ^ 2 + Real.sqrt 2 + Real.sin 1 > 0 := by rcf
example : ∀ x : ℝ,
    x ^ 2 + 1 / (Real.sqrt 2 + Real.sin 1) > 0 := by rcf
```

Registered bounds also compose with unregistered algebraic coefficients.
For the last two examples, the algebraic approximation proposes rational
endpoints for the selected positive square root. The existing exact algebraic
frontend proves containment by literal replay before those bounds enter the
finite arithmetic. The supplied sine bound then separates the original
divisor from zero. The frozen proof does not rerun algebraic approximation or
root production. Whole-subject registrations still take priority. This
composition remains bounded: an unsupported field presentation or an
unresolved combined enclosure is a failure, not a completeness claim.
Rational values keep exact bounds when the rational frontend recognizes them,
including perfect-square radicals. Within one preparation, repeated identical
closed expressions reuse their checked enclosure proof; the original divisor
checks still run before proof search. Distinct aliases do not automatically
share an enclosure or supply an equality proof.

The finite path requests width `1/16` once. The actual width here is `2`;
containment does not assert that the request was met. A requested-width theorem
has the separate type
{name}`Hex.OrderedFn.Oracle.ApproximationWidth`, applied to
{name}`Hex.OrderedFn.Oracle.Approximation.ofConstant` with `callerBounds`.
Convergence and relative transcendence are separate hypotheses for total
search. This fixed bound makes no such claim. Finite proofs from containment
need neither hypothesis.

For the named constants below, the caller uses existing Mathlib theorems
to supply `π ∈ [3, 63/20]` and `exp 1 ∈ [5/2, 11/4]`. These bounds suffice
for the displayed finite proofs, including the original nonzero divisor
`4 − π`. The imports are `Mathlib.Analysis.Real.Pi.Bounds` and
`Mathlib.Analysis.Complex.ExponentialBounds`. These constant callbacks do
not certify arbitrary requested widths or a convergent search.

```lean
private def callerPiBounds (_ : Rat) : Bounds :=
  ⟨3, mkRat 63 20, by norm_num⟩
private def callerExpBounds (_ : Rat) : Bounds :=
  ⟨mkRat 5 2, mkRat 11 4, by norm_num⟩

@[rcf_constant] private def callerPi :
    Registration Real.pi where
  version := 1
  approximation := callerPiBounds
  containment δ _ := by
    norm_num [Contains, callerPiBounds]
    constructor
    · exact Real.pi_gt_three.le
    · linarith [Real.pi_lt_d2]

@[rcf_constant] private def callerExp :
    Registration (Real.exp 1) where
  version := 1
  approximation := callerExpBounds
  containment δ _ := by
    norm_num [Contains, callerExpBounds]
    constructor
    · linarith [Real.exp_one_gt_d9]
    · linarith [Real.exp_one_lt_d9]

example : ∀ x : ℝ, x ^ 2 > Real.pi - 4 := by rcf
example : ∀ x : ℝ, x ^ 2 + Real.exp 1 > 2 := by rcf
example : ∃ x : ℝ,
    x = Real.exp 1 ∧ 2 < x ∧ x < 3 := by rcf
example : ∀ x : ℝ,
    x ^ 2 + 1 / (4 - Real.pi) > 0 := by rcf

section
set_option maxRecDepth 16384
set_option maxHeartbeats 2400000

example : ∀ x : ℝ,
    x ^ 2 + Real.pi -
      Real.sqrt (Real.sqrt 2) > 0 := by rcf
example : ∀ x : ℝ,
    x ^ 2 + Real.exp 1 -
      Real.sqrt (3 + Real.sqrt 2) > 0 := by rcf
example : ∀ x : ℝ,
    x ^ 2 + Real.pi -
      (3 + Real.sqrt 2) ^ (1 / 3 : ℝ) > 0 := by rcf
example : ∀ x : ℝ,
    x ^ 2 + Real.pi - Real.sqrt
      (1 / (4 + Real.sqrt 2)) > 0 := by rcf
example : ∀ x : ℝ,
    x ^ 2 + 1 /
      (Real.pi - Real.sqrt (Real.sqrt 2)) > 0 := by rcf

@[rcf_constant] private def callerInner :
    Registration (Real.sqrt 2) where
  version := 1
  approximation _ := ⟨1, 2, by decide⟩
  containment _ _ := by
    simp only [Contains]
    constructor
    · norm_num [Real.le_sqrt]
    · norm_num [Real.sqrt_le_iff]

example : ∀ x : ℝ,
    x ^ 2 + Real.pi -
      Real.sqrt (Real.sqrt 2) > 0 := by rcf
end

/-- error: rcf: original closed divisor is zero -/
#guard_msgs in
example : ∀ x : ℝ,
    x ^ 2 + 0 / (Real.pi - Real.pi) ≥ 0 := by rcf
```

These additional examples combine supplied bounds with square and cube roots
of algebraic bases. The real-power example takes the positive cube root of
`3 + √2`; its exact source authentication uses that non-rational base rather
than a rational-root shortcut. Before proposing an enclosure, the frontend
authenticates the source and its selected embedding, checking every original
divisor inside the base. Ordinary literal replay then proves containment in
the proposed rational interval. The mixed-division example also checks that the combined
bounds separate its original divisor from zero. Neither step treats a registered
constant as an executable ordered field, and frozen replay does not repeat
the algebraic search. An unsupported base, exhausted admission or unresolved
divisor remains a failure of this bounded finite path. The final registration
also illustrates a registered subterm inside an algebraic root. The root must
still authenticate exactly without using the subterm provider's bounds;
registering π does not admit `Real.sqrt Real.pi`. The finite certificate retains
and checks the matched provider's frozen subject, request and version.
A registration for the whole coefficient takes precedence over its subterms.

All original divisors are checked before cancellation, coefficient abstraction
or proof search. Thus even an erased division by `sin 1 - sin 1` is invalid.
The supplied interval also cannot certify that `sin 1` is nonzero: a bound
containing zero proves neither equality to zero nor a strict sign.

```lean
/-- error: rcf: original closed divisor is zero -/
#guard_msgs in
example : ∀ x : ℝ,
    x ^ 2 + 2 + Real.sin 1 +
      0 / (Real.sin 1 - Real.sin 1) > 0 := by
  rcf

/-- error: rcf: original closed divisor remains unresolved in supplied bounds -/
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

The CI-built examples in `bench/HexRCF/ProofProbe/Registered/` also prove
`∀ x, x² > π-4`, `∀ x, x²+exp 1 > 2`,
`∃ x, x=exp 1 ∧ 2<x ∧ x<3`, and the guarded
`∀ x, x²+1/(4-π)>0`. Their callers supply coarse bounds
`π ∈ [3,63/20]` and `exp 1 ∈ [27/10,14/5]`, with containment proved from
Mathlib's existing numerical inequalities. These are test registrations;
the optional library supplies no such providers. All four quoted theorem
dependencies are exactly `propext`, `Classical.choice` and `Quot.sound`.

CI builds this four-proof module through `HexRCFProofProbe`. Its guarded axiom
reports check the ordinary-kernel dependency surface on every PR. These examples
show that the coarse caller enclosures suffice without root/cell construction;
they make no timing, convergence or completeness claim.

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
