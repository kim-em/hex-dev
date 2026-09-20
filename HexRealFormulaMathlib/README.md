# Reifying and interpreting real formulas

Consider the parameterized proposition

```lean
∃ x : ℝ, x ^ 2 / 2 + a * x ≤ 3 / 2
```

Declare `a` as the sole free real parameter. The shared reifier opens `x` as
a fresh local constant and records the coordinate map `[a, x]`. It proves a
positive-denominator view for the atom difference:

```text
(x² / 2 + a*x - 3/2) * D = P(a,x),  with D > 0.
```

Here `D = 2` and `P = x² + 2*a*x - 3` suffice. The implementation may choose
a larger positive common denominator, so consumers should use the returned
equivalence rather than expect a particular coefficient scaling. Negative
literal divisors are handled with a proved sign change. Zero and symbolic
divisors are rejected.

In a Lean `MetaM` context, call `Hex.RealFormula.Reify.reify source #[a]`,
where `source` and `a` are Lean expressions. The result contains:

* `formula`, a closed expression of type `Prenex 1`;
* `parameters`, source `binders`, the normalized `prefixMap`, and `sealedMap`
  from the ring provider's atom order to the source parameter/binder order;
* `scopedFormula`, preserving the frontend Boolean/binder structure;
* `proof`, a kernel-checked equivalence for every parameter valuation;
* `qf?` and `qfProof?` when the whole source is quantifier-free;
* provider budget usage.

For this example, the proof contract is

```text
∀ ρ : Fin 1 → ℝ,
  Prenex.toProp formula ρ ↔
    ∃ x : ℝ, x² / 2 + ρ 0 * x ≤ 3/2.
```

The returned `source` field is the right-hand predicate on `ρ`. Parameter
expressions supplied by the caller remain in the metadata; opened bound
locals do not escape. Binder identifiers distinguish shadowed names, and
`prefixMap` records duplication caused by biconditional expansion.

The reifier accepts the six comparisons, Boolean connectives, implication,
biconditional, real quantifiers, polynomial bounds, literal natural powers,
and integer/rational literal coefficients. It submits every atom numerator
to one `HexReflect` ring batch, seals once, and proves the coordinate map.
`sin x`, `1/x`, symbolic exponents, opaque functions, undeclared parameters,
non-real or dependent binders, and higher-order predicates decline explicitly.
To use an opaque real value as a parameter, introduce and declare that
parameter yourself.

Selected hypotheses are passed in the `assumptions` argument and become
explicit antecedents. Unselected hypotheses are not used as hidden premises.
`Config.reference` supplies the source syntax for diagnostics. `Config.ring`
sets expression, exponent, coefficient, term and proof limits, and
`formulaNodes` limits expanded formula size. Provider conditions and decline
reasons remain available in the structured error. `reify!` reports the error
at the supplied syntax location.

`Scoped.toPrenex` first handles Boolean polarity, including quantifier
dualization under negation. Its correctness theorem holds at every free
valuation. The scoped form lets future elimination tactics rewrite an
innermost subformula without first duplicating all quantifiers in an `↔`.

## Elimination consumers

The integer matrix from the example can be written directly as:

```lean
def inequality : Hex.RealFormula.QF 2 :=
  .atom ⟨Hex.MvPoly.X 1 ^ 2 + Hex.MvPoly.C 2 * Hex.MvPoly.X 0 * Hex.MvPoly.X 1
    - Hex.MvPoly.C 3, .le⟩
```

The planned [virtual-substitution library](../SPEC/Libraries/hex-virtual-subst.md)
consumes this matrix, with `a` free and `x` last. Its elimination result must
be a `QF 1` accompanied by an equivalence with
`∃ x, inequality.toProp (append ρ x)`. For this particular example, `x = 0`
is always a witness, so a correct elimination result is true for every `a`.
Virtual substitution itself is a separate implementation; this library does
not claim to provide that algorithm.

For RCF, specialize `a` to `1` by substituting `C 1` for coordinate `0`.
The resulting polynomial is `x² + 2*x - 3`, and the parameter coordinate is
now unused. Import `HexRCF.RealFormula` and call
`Hex.RCF.RealFormula.residue? .existsReal specializedMatrix`. It removes
only coordinates proved absent and returns the existing RCF `Sentence`.
`residue_correct` proves equivalence at every original parameter valuation.
The original unspecialized matrix is rejected because its coefficient of
`x` depends on `a`.

For a closed shared sentence with exactly one quantifier, `toSentence?`
performs the translation directly. `decide?` calls RCF's existing certificate
construction, `decide_sound` transports accepted decisions, and `check_sound`
transports a checked literal certificate. Cubic and higher-degree univariate
residues are eligible. Neither translation changes RCF's public sentence type
or its original reifier.

The adapter is an optional development target (`lake build HexRCFRealFormula`).
Import `HexRCF.RealFormula` explicitly; the released `HexRCF` umbrella does not
import the shared frontend while these libraries are incubating.

The opposite direction, `ofSentence`, translates all four RCF sentence
constructors. Bounded sentences retain the exact half-open convention `(a,b]`:
the lower guard is strict and the upper guard is non-strict. Dyadic endpoints
are converted through positive rational denominators. `ofPoly_correct`,
`toPoly_correct`, `ofFormula_correct`, and `ofSentence_correct` prove the
evaluation and interpretation correspondence.

Run the companion checks with:

```sh
lake build +HexRealFormulaMathlib.Conformance \
  +HexRealFormulaMathlib.Arithmetic +HexRealFormulaMathlib.ReifierConformance \
  +HexRCF.RealFormulaConformance
```
