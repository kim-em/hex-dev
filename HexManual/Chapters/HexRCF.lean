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

The `rcf` tactic proves closed propositions about exactly one quantified real
variable by exact decision. Its input is one universal or existential
quantifier over `ℝ`, or over a half-open interval `Set.Ioc a b`, with no other
free variables. The quantifier body may use Boolean combinations of
comparisons between univariate polynomials with rational coefficients.

The computation uses exact integer and rational arithmetic. It isolates the
real roots that can change an atom's sign, evaluates the formula on the
resulting cells, and emits a certificate for Lean's kernel to check. No
floating-point approximation occurs.

Import `HexRCF` and write `rcf` at the goal:

```lean
example : ∀ x : ℝ, x ^ 2 + 1 > 0 := by
  rcf
```

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

A supported sentence may be false even though reification and certified
decision both succeed. Such a checked `false` verdict never becomes a proof
term: `rcf` reports the relevant false-sentence diagnostic above. An
out-of-fragment goal is different: reification fails before the decision
procedure runs. Both are ordinary tactic failures, so tactic combinators may
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

# The reflected and compiled APIs
%%%
tag := "hex-rcf-reflected-api"
%%%

Most users only need the `rcf` tactic. Programs that construct or inspect
sentences directly use the reflected language below. A comparison applies to
one integer polynomial, formulas combine comparisons, and a sentence adds the
one quantifier supported by the decision procedure.

{docstring Hex.RCF.Cmp}

{docstring Hex.RCF.Atom}

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

{docstring Hex.RCF.BuildResult}

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

# Certificates and the trust boundary
%%%
tag := "hex-rcf-trust"
%%%

The four certificate shapes correspond to empty bounded domains, formulas
with no nonconstant atom polynomial, root-free carriers, and positive-root
cell decompositions:

{docstring Hex.RCF.Certificate}

`HexRCF` is classified as a Mathlib-facing library because its reifier, tactic,
real semantics, and soundness theorem use Mathlib. There is no separate
`HexRCFMathlib` library. By contrast, `HexRCF.DecisionCheck` exposes the
complete compiled search, certificate construction, replay, and
{name}`Hex.RCF.decide` path, with a mechanically checked Mathlib-free import
closure. The soundness theorem remains on the Mathlib-facing side of this
boundary.

Certificate construction runs as compiled elaboration code. That search is
not trusted. The tactic embeds its reflected sentence and a literal
{name}`Hex.RCF.Certificate`, reduces the public Boolean checker
{name}`Hex.RCF.Certificate.check`, and applies the soundness theorem
{name}`Hex.RCF.check_sound`. Lean's kernel also checks the reifier's proof
that the reflected sentence is equivalent to the source goal.

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
comparisons, and Boolean folds on literal data. It does not repeat root
isolation, polynomial gcd computation, or interval refinement. The emitted
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
  used by `HexRCF` during compiled certificate construction. The generalized
  multiplication-only Sturm certificates in `HexRCF` are kernel-replay
  evidence for the resulting root-count facts, not a separate compiled
  isolation algorithm.
