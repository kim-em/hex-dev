# hex-real-algebraic (exact ordered real algebraic numbers)

`hex-real-algebraic` supplies `Hex.RealAlgebraicNumber`, the real subtype of
canonical `AlgebraicNumber`, with executable field arithmetic and exact order.
`hex-real-algebraic-mathlib` identifies its values with the algebraic reals and
proves that it is a real closed ordered field. This document specifies both
libraries; it does not introduce their implementation or release entries.

## Library boundary

Use a new library, depending on
[hex-number-field](../../HexNumberField/SPEC/hex-number-field.md).
That library has shipped and serves complex algebraic arithmetic independently
of an order. The [release manifest](../../scripts/release/released.yml) manages
each library separately. Develop both new libraries here and add them to the
manifest only when ready for publication.

The dependency arrows below point from a library to its dependencies:

```text
hex-real-algebraic         -> hex-number-field
hex-real-algebraic-mathlib -> hex-real-algebraic
                          -> hex-number-field-mathlib -> hex-number-field
                          -> Mathlib
```

`hex-poly`, `hex-poly-z`, `hex-roots`, and dyadic arithmetic are already below
`hex-number-field`; declare their pins too wherever the new library directly
imports them. There is no dependency on `hex-number-field-tower`, `hex-rcf`,
`hex-interval`, or either new library from `hex-number-field`. Both new nodes
can therefore be appended after their existing dependencies without a cycle.
Computational modules, including their core law instances, must have no
transitive Mathlib import. Companion proofs never flow back into that graph.

The public surface includes construction, arithmetic, comparison, `min`, `max`,
`sign`, `abs`, nonnegative square roots, polynomial real roots, `floor`, `ceil`,
dyadic approximation, and rational recognition. Comparison has the semantics
of `AlgebraicNumber.realCompare`. Refine-on-overlap fast paths, lazy
`AlgebraicRoot` comparison, Tarski queries, and quantifier elimination are
separate work; replacement comparison algorithms must prove agreement with
this reference and preserve the public theorems.

## Carrier, construction, and closure

The carrier is exactly the subtype, with no additional root representation:

```lean
def RealAlgebraicNumber := {a : AlgebraicNumber // a.isReal = true}
```

Use `RealAlgebraicNumber` as the namespace for the following proposed names.
`toAlgebraic` projects the underlying canonical value. `ofAlgebraic?` performs
one stored-precision `isReal` test, returning `some ⟨a, h⟩` precisely on success
and `none` on nonreal input. A proof-taking `ofAlgebraic a h` packages an already
known real value without retesting. `ofRoot? r` exactifies `r` through
`AlgebraicRoot.exact` and then calls `ofAlgebraic?`. No implicit coercion from
arbitrary complex algebraic numbers is provided.

Equality is inherited from the canonical carrier: subtype equality is equality
of `toAlgebraic`, and `BEq` delegates to its existing Boolean equality. Proof
fields are erased. Do not introduce approximate equality or an additional
quotient. The existing Boolean algorithm compares minimal polynomials and
tests the stored discs; its agreement with structural Lean equality currently
has its proof in the companion. Supplying Mathlib-free `LawfulBEq` and
`DecidableEq` is an explicit proof obligation below.

Provide `0`, `1`, natural and integer casts, `ofRat`, rational casts, negation,
addition, subtraction, multiplication, inversion, division, natural and integer
powers, and scalar multiplication by `Nat`, `Int`, and `Rat`. Each operation
runs the corresponding `AlgebraicNumber` operation and rechecks `isReal` once
on the canonical result. Powers reuse `natPow` and `intPow`, including repeated
squaring, and check their final result. Inversion and division are total with
`0⁻¹ = 0` and `a / 0 = 0`, as in the underlying field.

The internal total packer uses `ofAlgebraic?` with
`Hex.panicWith zero "RealAlgebraicNumber: nonreal operation result"` as the
fallback. Construct subtype zero directly from the stored zero representative
and its decidable reality test, so this fallback does not depend on itself.
Classify it as **unreachable-by-pipeline-invariant** under
[the fallback policy](../design-principles.md): its only callers are the field
operations and casts on real inputs. Public checked construction propagates
`none`; it never turns a rejected complex input into zero.

Prove `ofAlgebraic?_isSome` from `a.isReal = true`. The companion supplies
`zero_isReal`, `one_isReal`, `ofRat_isReal`, `neg_isReal`, `add_isReal`,
`sub_isReal`, `mul_isReal`, `inv_isReal`, `div_isReal`, `natPow_isReal`,
`intPow_isReal`, and `smul_isReal` for the underlying operations. Cast cases
reduce to `ofRat_isReal`. Their hypotheses are reality of the operands, with
no nonzero hypothesis for inversion. Together with the underlying arithmetic
correspondence and `isReal_iff`, these prove every packer call succeeds and
that `toAlgebraic` commutes with every operation. The analogous Mathlib-free
closure laws are also needed for the core law instances; a companion theorem
alone cannot inhabit an instance in a computational module.

Threading closure proofs through each operation is an alternative. It would
remove the runtime check but require all closure proofs in the computational
dependency graph before even the arithmetic wrappers can be defined. Rechecking
has a fixed extra disc test at the already stored precision and matches the
existing `exact` / `exact?_isSome` design. It is the chosen implementation.

Reuse `conj` on the underlying value and prove `conj_eq : a.conj = a`; its real
branch already returns its argument. Reuse `AlgebraicNumber.approx` for complex
balls. Delegate display to the canonical value. `Repr` emits a checked real
constructor around the underlying round-trip representation, with no printed
proof terms; elaborating it must recover the same subtype value. It must not
use a decimal approximation or a partial `Option.get!` requiring a new
unreachability assumption.

## Order and core instances

`compare a b` is `a.toAlgebraic.realCompare b.toAlgebraic`. The comparison first
uses canonical equality; if unequal, it compares real ball centres at
`AlgebraicNumber.separationPrec (a.p * b.p)`. Merely comparing the stored
centres of two independently canonicalized numbers is insufficient.

Define the operations with these exact conventions:

| Operation | Definition |
| --- | --- |
| `a < b` | `compare a b = .lt` |
| `a ≤ b` | `compare a b ≠ .gt` |
| `DecidableLT`, `DecidableLE` | Decide these finite `Ordering` tests |
| `Ord` | The comparison above |
| `min a b` | `a` if `a ≤ b`, otherwise `b` |
| `max a b` | `a` if `b ≤ a`, otherwise `b` |
| `sign a : Int` | `-1`, `0`, or `1` according as `compare a 0` is `.lt`, `.eq`, or `.gt` |
| `abs a` | `-a` if `a < 0`, otherwise `a` |

Both extrema return their left argument on ties. Expose named `sign` and `abs`
even without Mathlib; the companion's absolute-value notation must use the
same executable operation. Do not define `LE` or `LT` on the ambient complex
carrier. Nonreal input is rejected before any order operation is called.

In the pinned Lean `v4.34.0-rc2`, the core law classes are in namespace `Std`.
Provide `Std.IsLinearOrder` (and its preorder and partial-order parents),
`Std.LawfulOrderLT`, `Std.LawfulOrderBEq`, `Std.LawfulOrderOrd`,
`Std.LawfulEqOrd`, `Std.TransOrd`, `Std.LawfulOrderMin`, and
`Std.LawfulOrderMax`, with the left-leaning min/max laws. They relate all the
operations above to one order; a bare `Ord` instance is not enough.

Provide `Lean.Grind.Field RealAlgebraicNumber` and
`Lean.Grind.OrderedRing RealAlgebraicNumber` on those same arithmetic and order
operations. `OrderedRing` requires ordered addition, `0 < 1`, and preservation
of strict inequalities by positive multiplication on each side. The core
field and linear-order packages together let `grind` use ordered-field laws.
They must remain executable when passed as dictionaries to generic code.

These are **new Mathlib-free proof obligations**, not automatic consequences
of having Mathlib-free class definitions. The existing
[field proof](../../HexNumberFieldMathlib/Field.lean) and
[equality proof](../../HexNumberFieldMathlib/Basic.lean) import Mathlib;
the `Field.toGrindField` bridge available there does not provide a
Mathlib-free field instance. A computational `Laws` module must prove the
closure, canonical equality, field, comparison transitivity, and arithmetic
monotonicity laws from the executable algorithms and their certificates.
Place reusable underlying laws in `hex-number-field` when appropriate. No
axiom, assumed law typeclass, imported companion proof, or `native_decide`
may stand in for these proofs. This work is required before claiming the
Mathlib-free ordered-field interface complete.

Keep the executable definitions independent of the law module. In the
companion, build `LinearOrder`, `Field`, and `IsStrictOrderedRing` using the
same data fields and the real interpretation. The pinned Mathlib expresses an
ordered field with these separate classes. Its generic core bridges must
agree with the explicit core instances. Regression examples must compile
both with only the computational umbrella and after importing the companion;
check arithmetic, numerals, comparisons, extrema, and small `grind` proofs.

## Square roots and polynomial roots

Use the following public square-root forms:

```lean
sqrt? : RealAlgebraicNumber → Option RealAlgebraicNumber
sqrt (a : RealAlgebraicNumber) (h : 0 ≤ a) : RealAlgebraicNumber
```

`sqrt? a` returns `none` exactly when `a < 0`. Otherwise solve `X² - a` with
the real-root API and select its unique nonnegative root. At zero it returns
zero. The proof-taking total form uses the same computation; classify its
fallback as unreachable by `sqrt?_isSome` under `0 ≤ a`. Also name and prove
the internal root-selection success lemma `sqrtRoot?_isSome` under that
hypothesis, so a failed root search cannot masquerade as a negative argument.
Require `sqrt_nonneg`, `sqrt_sq` (`sqrt a h * sqrt a h = a`), uniqueness, and
`sqrt_square` (`sqrt (a*a) h = abs a`, independent of the proof `h`).

Represent `RealAlgebraicPoly` as an `AlgebraicPoly` with an erased proof that
each stored coefficient passes `isReal`. Its array constructor accepts only
real algebraic coefficients, projects them, and uses `AlgebraicPoly.ofArray`
for trailing-zero normalization. A checked conversion from `AlgebraicPoly`
rejects a nonreal coefficient. This reuses the existing normalizer without
assuming `DensePoly AlgebraicNumber` has a Mathlib-free equality dictionary.

`RealAlgebraicPoly.roots` returns a real root set with constructors `.all` and
`.finite`, whose finite entries contain a canonical `RealAlgebraicNumber` and
a positive multiplicity. Preserve `.all` exactly for the zero polynomial;
nonzero constants return `.finite #[]`. Do not collapse these cases through
`RootSet.toArray`, which maps `.all` to an empty array.

Call `AlgebraicPoly.roots` on the underlying polynomial. Its finite entries
contain **lazy** `AlgebraicRoot`s, not `AlgebraicNumber`s. Exactify each entry,
then filter and package it through `ofAlgebraic?`, preserving multiplicity.
Finally sort the retained entries by the real comparison. The result has
distinct roots in strictly increasing order; multiplicities are attached,
not repeated array entries. Prove membership iff polynomial evaluation is
zero, multiplicity agreement, positivity, no duplicates, and sortedness.
The sum of multiplicities is the number of real roots counted with
multiplicity; it need not equal the degree when nonreal roots exist.

For integer inputs, provide `ZPoly.realAlgebraicRoots : ZPoly →
Array RealAlgebraicNumber` by filtering `ZPoly.algebraicRoots` and sorting by
the same real comparison. This convenience API returns distinct roots and
inherits the empty-array convention for every constant, including zero;
state its membership theorem only for `p ≠ 0`. Use `RealAlgebraicPoly.roots`
when the universal root set or multiplicities matter.

## Rational recognition, rounding, and approximation

`toRat? : RealAlgebraicNumber → Option Rat` tests whether the canonical
minimal polynomial has degree one. If so, return the reduced rational
`-p.coeff 0 / p.coeff 1`; the leading coefficient is nonzero. Prove
`toRat?_eq_some : a.toRat? = some q ↔ a = ofRat q`, including `q = 0`.
A polynomial of higher degree gives `none`, even if a low-precision decimal
looks rational. Completeness needs the minimal-polynomial correspondence,
not a search over possible denominators.

`floor` and `ceil` return `Int`, with their usual exact contracts:

```text
ofInt (floor a) ≤ a < ofInt (floor a + 1)
ofInt (ceil a - 1) < a ≤ ofInt (ceil a)
ceil a = -floor (-a)
```

Use `toRat?` first for rational values, rounding with integer arithmetic.
For the general path, `(a.toAlgebraic.approx 2)` gives a closed real enclosure
`[c-r, c+r]` of width at most `1/2`. Compute the integer floors of its dyadic
endpoints. They differ by at most one. If they differ, compare `a` exactly
with the intervening integer to choose its floor, including equality with
that integer. Thus an enclosure touching or crossing an integer never
causes a refinement loop or an arbitrary rounding decision. Prove the
enclosure and width bounds, the candidate bound, and the final floor
inequalities; expose the companion's `FloorRing` using these algorithms.

`approx (a : RealAlgebraicNumber) (prec : Int := 64) : Dyadic` returns the
real centre of `a.toAlgebraic.approx prec`. The companion proves

```text
|a.toReal - Dyadic.toReal (a.approx prec)| ≤ (2 : ℝ) ^ (-prec).
```

Allow negative precisions with exactly the same bound. Also expose the
underlying complex ball when a caller needs its radius. Approximation does
not affect canonical equality, order, or the stored representative. The
error theorem follows from `AlgebraicNumber.approx_mem`, `approx_radius`,
and the real-coordinate projection of the disc bound.

## Companion and proof inventory

Define `toReal a := a.toAlgebraic.toComplex.re`. By `isReal_iff`, its complex
inclusion equals `a.toAlgebraic.toComplex`; hence `toReal` is injective.
Package it as a field embedding and an order embedding. Prove arithmetic and
cast correspondence, `compare_eq`, `lt_iff`, `le_iff`, and correspondence for
`min`, `max`, `sign`, `abs`, `sqrt`, `floor`, `ceil`, and approximation.
The order proofs transport `realCompare_eq` using both subtype witnesses.

Prove `isAlgebraic (a) : IsAlgebraic ℚ a.toReal` using its nonzero stored
integer polynomial. Also prove `range_toReal`: a real number lies in the
range exactly when it is algebraic over `ℚ`. Clear denominators of a nonzero
rational annihilator, use `ZPoly.mem_algebraicRoots_iff`, and package the real
root with `isReal_iff` for surjectivity onto that range.

The [pinned Mathlib source](https://github.com/leanprover-community/mathlib4/blob/85e3a25e006c35636f0e53b0e9296caca2685bc0/Mathlib/FieldTheory/IsRealClosed/Basic.lean)
contains `IsRealClosed` and `IsRealClosed.of_linearOrderedField`. Require an
`IsRealClosed RealAlgebraicNumber` instance now. The constructor takes
nonnegative-square closure and odd-degree-root existence in a `Field` with
`LinearOrder` and `IsStrictOrderedRing`; it also discharges the semireal
condition. Its source still lists a real-number instance as a TODO, so do
not assume `[IsRealClosed ℝ]` is available.

Prove square closure using real square-root existence and the complete
algebraic-coefficient root driver to recover a canonical real witness.
For any Mathlib polynomial over this field of odd natural degree, convert
its finite coefficient support to `RealAlgebraicPoly`, preserving evaluation
and degree. Its image in `ℝ[X]` has a real root by the intermediate value
theorem. `AlgebraicPoly.contains_roots_iff` supplies a lazy algebraic witness
for that complex value; exactification and `isReal_iff` retain it in the
real-root list. This proves odd-degree-root existence without assuming
real-closedness to justify the algorithm. Export both closure theorems as
well as the instance.

The following are existing dependencies, with their actual source locations:

| Needed fact | Existing declaration and source |
| --- | --- |
| Reality test | `AlgebraicNumber.isReal_iff`, [IntegerRoots](../../HexNumberFieldMathlib/IntegerRoots.lean) |
| Exact real comparison | `AlgebraicNumber.realCompare_eq`, [Nearest](../../HexNumberFieldMathlib/Nearest.lean), requiring both reality hypotheses |
| Conjugation | `AlgebraicNumber.conj_toComplex`, [Nearest](../../HexNumberFieldMathlib/Nearest.lean) |
| Canonical equality | `AlgebraicNumber.toComplex_injective`, `beq_iff`, `LawfulBEq`, `DecidableEq`, [Basic](../../HexNumberFieldMathlib/Basic.lean) |
| Canonical arithmetic | `add_toComplex`, `sub_toComplex`, `neg_toComplex`, `mul_toComplex`, `inv_toComplex`, `div_toComplex`, [Lazy](../../HexNumberFieldMathlib/Lazy.lean) |
| Casts, powers, field laws | `ofRat_toComplex`, `natPow_toComplex`, `intPow_toComplex`, `smul_toComplex`, `Field`, [Field](../../HexNumberFieldMathlib/Field.lean) |
| Lazy-root exactification | `AlgebraicRoot.exact?_isSome`, `exact_toComplex`, [Exact](../../HexNumberFieldMathlib/Exact.lean) |
| Integer-root completeness | `ZPoly.mem_algebraicRoots_iff` (nonzero input), `algebraicRoots_nodup`, [IntegerRoots](../../HexNumberFieldMathlib/IntegerRoots.lean) |
| Algebraic-coefficient roots | `AlgebraicPoly.roots?_isSome`, `roots_all_iff`, `contains_roots_iff`, `multiplicity_roots`, `roots_noDuplicates`, [AlgebraicRoots](../../HexNumberFieldMathlib/AlgebraicRoots.lean) |
| Approximation | `AlgebraicNumber.approx_mem`, `approx_radius`, [IntegerRoots](../../HexNumberFieldMathlib/IntegerRoots.lean) |
| Minimal polynomial | `AlgebraicNumber.p_eq_minpoly`, [Basic](../../HexNumberFieldMathlib/Basic.lean) |

Missing facts must be supplied, not presumed:

- No value-sortedness theorem for `ZPoly.algebraicRoots` is present in these
  sources. The implementation sorts by `AlgebraicNumber.rootLe`, which uses
  stored centres after exactification. A theorem `ZPoly.realRoots_sorted`
  would need to establish strict increase of the real values in its filtered
  output. Canonicalization selects representatives for individual minimal
  polynomials, so their stored precisions are not a common separation bound
  for different factors. This property needs a separate correctness audit;
  the new wrapper's explicit `realCompare` sort avoids assuming it.
- `AlgebraicPoly.roots_ordered` exists, but describes `RootSet.Ordered`, a
  deterministic representation order, not the increasing real-value order.
  Prove the new `RealAlgebraicPoly.roots_sorted` after exactification and sorting.
- The subtype closure lemmas, Mathlib-free equality/field/order laws, real
  coefficient normalization and evaluation bridges, `toRat?_eq_some`, the
  rounding lemmas, `range_toReal`, and the real-closedness construction are
  new work. Existing semantic proofs can guide the core proofs but cannot
  be imported into them. A Mathlib-free class signature does not remove
  this dependency constraint.

## Conformance and acceptance

Use python-flint's exact `qqbar` arithmetic and comparisons as the oracle.
The [generic-ring interface](https://python-flint.readthedocs.io/en/latest/_gr.html)
exposes `gr_real_qqbar_ctx` and `gr_complex_qqbar_ctx`; do not assume a
top-level `flint.qqbar` class. Pin the tested binding and FLINT versions and
probe construction, comparison, and root support before running fixtures.
An unavailable exact operation is an explicit oracle failure/skip under the
[testing policy](../testing.md), never a successful decimal comparison.
The [FLINT comparison contract](https://flintlib.org/doc/qqbar.html#comparisons)
provides exact equality and real-part comparison; check reality before using
the latter. cypari2 supplies no real-algebraic ordering oracle. Sage `AA`
examples are informational only, following the rule that Sage is not an oracle.

python-flint `0.9.0` with FLINT `3.6.0` supports the required scalar comparisons,
square roots, and floor/ceil through `_gr`, but its polynomial context exposes
no `roots` method. General root fixtures therefore need a binding for FLINT's
`qqbar_roots_fmpz_poly` and, for algebraic coefficients, `gr_poly_roots_other`
before conformance is complete. Supply this through python-flint or a test-only
binding adapter; do not substitute numerical `acb` root approximations as
the equality/order oracle. The scalar fixtures can run independently, but
passing them alone does not cover the polynomial-root requirement.

Serialize rationals as integer numerator/positive denominator and roots by
integer polynomial plus certified isolating data. The oracle independently
identifies the selected root; do not trust either a printed decimal or the
producer's array index as a cross-system root identity. Record exact ordering,
construction rejection, roots with multiplicities, and operation results.
Check a returned dyadic error bound by exact algebraic inequalities.

Required deterministic fixtures:

- `-√2 < √2`, and both roots against the exact rationals `7071/5000`
  (`1.4142`) and `14143/10000` (`1.4143`), including reversed comparisons.
- The two close roots around `1/256` of the Mignotte polynomial
  `X^8 - 2*(256*X - 1)^2`, with exact ordering and isolations identifying
  each root. Include cross-factor close roots to test comparisons between
  distinct minimal polynomials.
- Equal values from independent constructions: `√8/2 = √2`, `√2*√2 = 2`,
  and `(√2 + 1) - √2 = 1`. Check equality, `.eq`, both non-strict directions,
  neither strict direction, and left-argument selection for both extrema.
- `sqrt (a*a) = abs a` for zero, a negative rational, and both signs of `√2`;
  `sqrt? (-1) = none`.
- All eight roots of `(X²-2)(X²-3)(X²-5)(X²-7)`, initially permuted, sorted
  as `[-√7, -√5, -√3, -√2, √2, √3, √5, √7]`. Also solve a polynomial with
  an irrational real coefficient, such as `X²-√2`, and a repeated-root case.
- Each member of the conjugate pair from `X²+1` is rejected by real
  construction. A polynomial with coefficient `i` is rejected. Filtering
  `X²+1` gives a finite empty real-root set; the zero polynomial gives `.all`.
- `toRat?` on zero, negative rationals, and irrational values; floor/ceil at
  integers, negative fractions, and algebraic values on both sides of an
  integer; approximation at positive, zero, and negative precision; `Repr`
  round trips through the real constructor.

The order sanity cases have these required outcomes (`s` denotes `√2`):

| Operation | Zero | Rational `q = -3/2` against zero | Equal routes `s` and `√8/2` | Nonreal `i` |
| --- | --- | --- | --- | --- |
| `compare` / `Ord` | `compare 0 0 = .eq` | `.lt`; reverse `.gt` | `.eq` | construction returns `none` |
| `<` and its decision | `¬ 0 < 0` | `q < 0`, `¬ 0 < q` | false both ways | no real operand |
| `≤` and its decision | `0 ≤ 0` | `q ≤ 0`, `¬ 0 ≤ q` | true both ways | no real operand |
| `min` | `min 0 0 = 0` | `min q 0 = q` | left argument, equal value | no real operand |
| `max` | `max 0 0 = 0` | `max q 0 = 0` | left argument, equal value | no real operand |
| `sign` | `0` | `-1` | `1` for either route | no real operand |
| `abs` | `0` | `3/2` | `s` for either route | no real operand |

Conformance drivers and fixture emitters belong under `conformance/HexRealAlgebraic/`,
fixtures under `conformance-fixtures/HexRealAlgebraic/`, and the oracle under
`scripts/oracle/real_algebraic_flint.py` when implementation starts. Extend
the existing oracle runner and its single CI job. Acceptance also requires
the named totality and correspondence proofs, `IsRealClosed`, the independent
Mathlib-free law instances, import-DAG checks, and compilable examples before
and after importing the companion. No benchmark result or implementation is
claimed by this SPEC.
