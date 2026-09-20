/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import VersoManual
import HexRealFormulaMathlib
import HexRCF.RealFormula
import Mathlib.Tactic.NormNum

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

set_option pp.rawOnError true

#doc (Manual) "HexRealFormula: a shared language for real arithmetic" =>
%%%
tag := "hex-real-formula"
%%%

# Parameters, binders, and positive denominators

Consider the proposition `∃ x : ℝ, x² / 2 + a*x ≤ 3/2`. The real number `a`
is a free parameter. The existential quantifier chooses `x`; it does not
quantify `a`. Multiplying the atom difference by the positive denominator
`2` gives the integer polynomial `x² + 2*a*x - 3` without reversing its
comparison. A negative divisor must first be handled with its proved sign.

The shared syntax uses lexicographic integer polynomials from
{ref "hex-mv-poly"}[HexMvPoly]. Coordinate `0` denotes `a`; coordinate `1`
denotes `x`, appended after the parameter. The arity of a prenex formula
counts only its free parameters:

```lean
open Hex Hex.RealFormula

def inequality : QF 2 := .atom ⟨MvPoly.X 1 ^ 2 +
  MvPoly.C 2 * MvPoly.X 0 * MvPoly.X 1 - MvPoly.C 3, .le⟩
def problem : Prenex 1 :=
  .quant .existsReal (.matrix inequality)

#guard inequality.degree 1 == 2
#guard problem.toView.prefix == [.existsReal]
#guard inequality.evalRat
  (fun i => if i == 0 then 7/3 else 0)
```

{name}`Hex.RealFormula.Prenex.toProp` interprets a prefix from the front,
appending each chosen value. It supplies no implicit universal closure.
The same convention gives an innermost elimination theorem the form
`∀ ρ, result.toProp ρ ↔ ∃ x, matrix.toProp (append ρ x)`.

# Reification and its proof contract

{docstring Hex.RealFormula.Reify.reify}

The reifier accepts declared real parameters, literal rational coefficients,
literal natural powers, all six comparisons, Boolean connectives,
implication, biconditional, real quantifiers and polynomial bounds. It opens
binders as distinct locals, submits all atom differences to one
{ref "hex-reflect"}[HexReflect] batch, seals once, and proves the map from
ring coordinates to formula coordinates. A shadowed name never identifies
two binders.

For the example, the returned equivalence is a Lean expression of type
`∀ ρ : Fin 1 → ℝ, formula.toProp ρ ↔ ∃ x : ℝ, x²/2 + ρ 0*x ≤ 3/2`.
The implementation may use a larger positive common denominator than `2`;
the proof establishes the interpretation regardless of that scaling.

```lean
open Lean Meta Qq in
run_meta do
  withLocalDeclD `a q(ℝ) fun a => do
    let a : Q(ℝ) := a
    let source := q(∃ x : ℝ,
      x ^ 2 / 2 + $a * x ≤ 3 / 2)
    let result ← Reify.reify! source #[a]
    checkWithKernel result.proof
    unless result.parameters == #[a] do
      throwError "unexpected parameter order"
    unless result.prefixMap == #[(0, .existsReal)] do
      throwError "unexpected prefix"
```

The result contains the closed formula expression, source predicate on free
valuations, complete parameter and binder metadata, normalized prefix map,
sealed ring-coordinate map, and checked equivalence. Quantifier-free sources
also receive a `QF` expression and its equivalence. The scoped frontend tree
is retained so a future tactic can eliminate an inner subformula before
biconditional expansion duplicates its quantifiers.

Selected local hypotheses become explicit antecedents. Other hypotheses do
not become hidden assumptions. `Config.reference` supplies the source syntax
for declines. The ring configuration bounds expressions, exponents,
coefficients, terms and proof reconstruction; `formulaNodes` bounds expanded
formula size. Provider conditions and decline reasons remain structured.

An expression such as `sin x`, `1/x` or `x^k` for symbolic `k` is rejected.
It cannot become an independent quantified variable. Opaque real values may
be introduced as explicitly declared parameters by the caller. Zero divisors,
non-real or dependent binders, higher-order predicates and undeclared
parameters also decline.

# Using the matrix with elimination algorithms

The planned virtual-substitution library consumes `inequality`, retaining
`a` and eliminating the last coordinate `x`. For this example its result
must be true at every parameter value: zero is already a witness.

```lean
example (a : ℝ) : ∃ x : ℝ, x ^ 2 / 2 + a * x ≤ 3 / 2 := by
  refine ⟨0, ?_⟩
  norm_num
```

Virtual substitution is a separate implementation. This library supplies its
input language and proof contract, not an elimination tactic. CAD and covering
tactics can consume the same interfaces without depending on that algorithm.

To use {ref "hex-rcf"}[RCF], specialize `a` to `1`. The polynomial becomes
`x² + 2*x - 3`, and coordinate `0` is now unused. The checked reverse adapter
removes absent parameters before converting to RCF's existing sentence type:

```lean
def specialized : QF 2 :=
  inequality.map (MvPoly.subst fun i =>
  if i == 0 then MvPoly.C 1 else MvPoly.X 1)

open Hex.RCF.RealFormula in
#guard residue? .existsReal inequality == none
open Hex.RCF.RealFormula in
#guard residue? .existsReal specialized ==
  some (.existsReal (.atom
    ⟨DensePoly.ofCoeffs #[(-3 : Int), 2, 1], .le⟩))
```

{name}`Hex.RCF.RealFormula.residue_correct` proves the correspondence at
every original parameter valuation. RCF's certificate API then applies to
the returned sentence. A cubic or higher-degree univariate residue is
eligible; a symbolic coefficient such as `a*x` is not.
For a closed shared sentence with one quantifier,
{name}`Hex.RCF.RealFormula.decide?` invokes RCF's existing certificate
construction, and {name}`Hex.RCF.RealFormula.check_sound` transports an
accepted certificate to shared semantics.

The forward adapter {name}`Hex.RCF.RealFormula.ofSentence` preserves RCF's
half-open bounds `(a,b]` by strict lower and non-strict upper guards, clearing
dyadic denominators positively. Polynomial, formula and sentence translations
have evaluation and interpretation equivalence theorems.

# Structural transformations and checked data

`rename` maps source coordinates to target coordinates; collisions are valid
polynomial substitutions. `drop?` checks that a coordinate is absent.
`moveLast?` checks its index before exchanging it with the final coordinate.
A prefix `swap?` accepts adjacent quantifiers of the same kind and rejects
an existential/universal exchange.

{name}`Hex.RealFormula.QF.nnf_correct` proves pointwise negation-normal-form
correctness. Prenex normalization also dualizes real quantifiers under
negation and proves the required index shifts and freshness. Its theorem
holds for every free valuation.

Kernel encodings carry a version and an explicit arity. Decode checks every
exponent-vector length, including zero terms and unused Boolean branches,
before normalization. DAG decode checks all references and input identifiers,
including unreachable nodes. Validated list formulas evaluate by exact list
arithmetic. Expanded tree size and shared DAG size are distinct measurements.

Rational evaluation is only quantifier-free. In particular, searching rational
samples cannot test `∃ x : ℝ, x² = 2`. The companion theorem
{name}`Hex.RealFormula.QF.evalRat_correct` relates a rational evaluation to
real semantics at the cast valuation; for arity zero this decides the closed
quantifier-free proposition.
