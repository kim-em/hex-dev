# hex-real-formula

Shared polynomial formulas for real arithmetic. Virtual substitution,
cylindrical algebraic decomposition, and cylindrical coverings consume the
same syntax, variable conventions, and interpretation. This is a separate
library, with namespace `Hex.RealFormula`, rather than an algorithm's private
AST. Its Mathlib companion is specified here too.

## Scope and dependencies

`HexRealFormula` is Mathlib-free, depends on `HexMvPoly`, and owns comparison
syntax, Boolean formulas, prenex formulas, variable maps, kernel serialization,
and rational evaluation of quantifier-free formulas. `HexRealFormulaMathlib`
depends on it, `HexMvPolyMathlib`, `HexReflectMathlib`, and Mathlib; it owns real
semantics, normalization proofs, and the shared reifier. Neither library
depends on an elimination algorithm or on `HexRCF`. Algorithm tactics consume
the reifier. The RCF adapter belongs in `HexVirtualSubstMathlib`, avoiding a
cycle and a mandatory RCF dependency for future CAD and covering consumers.

This document specifies new interfaces; it does not register libraries or
claim implementation phases. The conventions of [SPEC](../SPEC.md),
[testing](../testing.md), and [benchmarking](../benchmarking.md) apply.

## Syntax and binding

Use one fixed lawful lexicographic monomial order at the public boundary;
write `Poly n` for `MvPoly n Int cmp` with that order. Other orders convert
explicitly with an evaluation-preservation proof. Atoms compare `p : Poly n`
with zero using `Cmp := eq | ne | lt | le | gt | ge`.

The following signatures are design notation, not existing declarations:

```text
Atom n                 := { p : Poly n, cmp : Cmp }
QF n                   := atom (Atom n) | tt | ff | not (QF n)
                          | and (QF n) (QF n) | or (QF n) (QF n)
Quantifier             := existsReal | forallReal
Prenex n               := { prefix : List Quantifier,
                            matrix : QF (n + prefix.length) }
Sentence               := Prenex 0
QF.toProp              : QF n → (Fin n → ℝ) → Prop
Prenex.toProp           : Prenex n → (Fin n → ℝ) → Prop
```

`n` counts free parameters, not bound variables. Coordinates are ordered as
free parameters followed by bound variables in outermost-to-innermost prefix
order. Interpret a prefix from the front: choose its first real value,
append it to the parameter valuation, and interpret the remaining prefix.
Interpret the matrix by the six real comparisons and ordinary propositional
connectives, evaluating integer coefficients through their cast to `ℝ`.
No implicit universal closure is part of `toProp`.

An innermost elimination consumes `QF (n+1)` and returns `QF n`, appending
the eliminated value at the last coordinate for its theorem. A checked
permutation moves a selected variable there when necessary. Prefix
permutations require a logical justification: adjacent quantifiers of the
same kind commute, arbitrary alternations do not. The APIs `rename`, `lift`,
and `drop` prove interpretation under the corresponding valuation maps;
`drop` requires that the removed coordinate occurs in no atom. Reject an
out-of-range variable at decode time, including in zero or unused terms.

`not` is allowed in output formulas. `nnf` pushes it to atoms, complementing
comparisons (`eq/ne`, `lt/ge`, `le/gt`), with a pointwise equivalence theorem.
Implication and biconditional are frontend constructs expanded into Boolean
connectives with proofs. Conversion to DNF is optional and budgeted; no
consumer may assume a polynomial-size DNF exists. DAG sharing is an execution
optimization with an acyclic, bounds-checked decode into these semantics.

## Kernel form and executable operations

Provide list-form atoms over `Hex.MvPoly.Kernel.PolyList Int`, carrying an
explicit arity and the same formula constructors. `Kernel.PolyList` itself is
an unindexed list: it does not certify exponent-vector lengths or canonical
ordering. The decoder checks every length, normalizes terms, combines
duplicates, and removes zero coefficients. Prove conversion to/from `Poly n`
preserves evaluation. Never infer variable independence from unchecked lists.
The kernel path uses list arithmetic rather than reducing tree-backed
`MvPoly` values. Formula certificates also check every node reference and
input identifier; a hash is a cache lookup key, not an equality proof.

The computational API includes `polys`, `support`, `degree`, `rename`,
`lift`, `drop`, `nnf`, `toKernel`, `ofKernel?`, and `evalRat`. Degree is the
maximum exponent of a specified variable after polynomial normalization;
the zero polynomial has bound zero. `evalRat` interprets a `QF n` at an exact
rational valuation; it does not interpret real quantifiers using rational
quantification. In particular, `∃ x : ℝ, x² = 2` cannot be tested by searching
`ℚ`. For `QF 0`, its rational truth value agrees with its real semantics.

Required companion theorem shapes (with well-formedness hypotheses on raw
kernel data) are:

```text
rename_correct : (rename σ φ).toProp ρ ↔ φ.toProp (ρ ∘ σ)
nnf_correct    : (nnf φ).toProp ρ ↔ φ.toProp ρ
kernel_correct : (toKernel φ).toProp ρ ↔ φ.toProp ρ
evalRat_correct : evalRat φ q = true ↔ φ.toProp (fun i => (q i : ℝ))
```

`rename` maps source coordinates to target coordinates; noninjective maps
are valid substitution maps but do not justify exchanging binders. Prenex
normalization must alpha-rename, shift indices under binders, and establish
freshness before moving a quantifier past a connective. Its theorem preserves
`toProp` for every free valuation, not merely the closed truth value.

## Reification contract

The reifier returns a formula, the complete ordered parameter/binder map,
and a Lean proof relating its `toProp` to the source proposition. It accepts
real polynomial expressions with integer and rational literal coefficients,
literal natural powers, the six comparisons, `True`, `False`, `¬`, `∧`,
`∨`, `→`, `↔`, and real `∀`/`∃`. Bounded real quantifiers expand to guarded
implication or conjunction; their bounds must themselves be polynomial
expressions. Local assumptions selected by a tactic are explicit antecedents.
Unselected hypotheses do not become hidden assumptions of the formula.

Use [hex-reflect](../../HexReflect/SPEC/hex-reflect.md) for the ring layer,
with its [Mathlib adapter](../../HexReflectMathlib/SPEC/hex-reflect-mathlib.md).
Reify all atom differences in one batch after binders have been opened to
distinct local constants. Seal the variable environment once, then use a
proved coordinate map from its atom order to the formula order. A session
must not identify variables from distinct binder scopes or reuse stale local
constants. Reconstruct the source proof while closing those binders.

These requirements go beyond H0; they are new consumer work, not features
already supplied by hex-reflect:

- Recognize comparisons and Boolean/binder syntax and compose interpretation
  proofs, including prenex conversion and quantifier-free subformula output.
- Provide a batch API mapping sealed ring atoms to declared real parameters
  and bound coordinates, with scope and dependency checks and renaming proofs.
  An H0 opaque atom containing a bound variable (for example `sin x`, `1/x`,
  or `x^k` with symbolic `k`) must be rejected, never treated as an independent
  quantified coordinate. The initial frontend rejects non-polynomial opaque
  parameters too; users can introduce an explicit real parameter themselves.
- Normalize rational literals and divisions by nonzero rational constants
  through proved views, then clear denominators by a **positive** common
  denominator per atom before integer-ring reification. A negative divisor
  is handled by its proved sign; zero or symbolic divisors are unsupported.
  H0 currently treats division as opaque, so this view cannot be assumed.
- Thread expression, exponent, term, formula-node, and proof-reconstruction
  budgets through the consumer; preserve provider conditions and decline
  reasons. No undisclosed assumption or native evaluation result is a proof.

Unsupported carriers, higher-order predicates, non-real binders, dependent
binder types, and unrecognized arithmetic decline with a source location.
The frontend may retain a scoped syntax tree before prenex conversion so
that an algorithm can eliminate an innermost quantified subformula and
rewrite by its checked equivalence. This is needed to avoid duplicating
quantifiers unnecessarily in biconditionals. The public algorithm input and
output remain `Prenex n` and `QF n`; the tree is frontend bookkeeping.

## Relation to hex-rcf

[HexRCF.Syntax](../../HexRCF/Syntax.lean) uses `ZPoly`, six comparisons, and
Boolean formulas under one real or half-open dyadic quantifier. Its
[semantics](../../HexRCF/Language.lean) are the one-variable instance of this
language up to explicit translations, not definitional equality. Prove
conversion of `ZPoly` to `Poly 1` commutes with evaluation; translate bounded
`Sentence` constructors by their `(a,b]` guards and positive denominator
clearing. Prove both formula and sentence interpretation equivalences.

The reverse adapter is partial: it accepts a single remaining quantified
coordinate with **no free symbolic parameters** (unused coordinates may be
proved absent and removed). Convert the integer polynomials to `ZPoly` and
invoke RCF's existing certificate/proof API. A degree-three or higher
univariate residue is eligible; a polynomial linear in `x` with symbolic
coefficient `a` is not. RCF's current reifier rejects symbolic coefficients
and additional variables, so it cannot already perform this composition.
Do not replace its public `Sentence` type or hand-written reifier in the
initial implementation of the shared language.

## Conformance, complexity, and manual

Fixtures record arity, exponent vectors, integer coefficients, comparison,
Boolean nodes, prefix order, and the free-variable order; rational samples
use normalized numerator/positive-denominator pairs. Version the schema.
Cover zero arity, unused variables, repeated variables, shadowed binders,
nonadjacent renaming, negative denominators, strict and non-strict bounds,
and malformed lists or DAGs. Independently evaluate Boolean formulas at
rational samples; test binder semantics using manually proved examples and
the elimination oracles in [hex-virtual-subst](hex-virtual-subst.md).
Sample agreement alone never certifies quantified equivalence.

Provide at least typical, edge, and adversarial cases per operation under
[testing](../testing.md). The `core` profile has no external oracle. RCF
round trips are companion tests, including half-open endpoints. Reifier
regressions must distinguish `x` from a shadowed `x` and reject `sin x` rather
than silently treating it as a second variable.

The Phase-4 compiled track covers the listed structural operations and exact
rational evaluation. Measure independent ladders for formula nodes, total
monomials, arity, coefficient bit length, and literal exponents. Structural
traversals are linear in visited syntax plus polynomial work; renaming may
merge terms and requires normalization; rational arithmetic costs are not
unit cost. NNF is linear in the tree input, while frontend biconditional
expansion and prenex conversion are output-sensitive and may duplicate
subformulas. Report expanded tree size separately from shared DAG size.
The companion's reification, semantic proofs, and RCF adapters use fresh
module `lake build` probes with matched import baselines per
[Phase 4](../../PLAN/Phase4.md), not Mathlib-importing LeanBench executables.

The manual introduces a parameterized polynomial inequality, shows its
coordinate map and rational denominator clearing, then uses the same formula
with virtual substitution and the RCF adapter. Explain free parameters versus
quantified variables and display both the source proposition and reification
proof contract. This is the shared frontend tutorial for later CAD and
covering tactics.
