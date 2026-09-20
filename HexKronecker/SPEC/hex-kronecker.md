# hex-kronecker

A deterministic, kernel-reducible polynomial identity checker by Kronecker
substitution.  It complements
[hex-mv-poly](../../HexMvPoly/SPEC/hex-mv-poly.md)'s canonical sparse term
lists: a caller chooses the sparse checker or this dense-box checker from
bounds computed before either representation is evaluated.  No random point
is chosen and a passing check is an exact certificate, not a probabilistic
identity test.

The library is unpublished.  It depends on `HexMvPoly` for `PolyList Int` and
on `HexMatrix` for `Hex.Matrix.Packed`; its import closure contains no Mathlib.
The companion [hex-kronecker-mathlib](../../HexKroneckerMathlib/SPEC/hex-kronecker-mathlib.md) supplies the
denotation, injectivity and tactic theorems.

Here “Kronecker” always means multivariate identity checking by mixed-radix
substitution.  It is distinct from `Hex.ZPoly.mulKronecker`, which multiplies
univariate integer polynomials and unpacks the result, and from the existing
`Hex.Matrix.Packed` dot-product packing, which this checker may use as a
second, independently budgeted layer.

## Expression and bounds

The stable kernel input is independent of Lean's reflected expression type:

```lean
namespace Hex.Kronecker

inductive Expr where
  | int (z : Int)
  | atom (i : Nat)
  | add (a b : Expr)
  | sub (a b : Expr)
  | neg (a : Expr)
  | mul (a b : Expr)
  | pow (a : Expr) (n : Nat)

end Hex.Kronecker
```

An expression is well formed at arity `k` when every atom index is below
`k`.  Its structural degree bound is a list of exactly `k` naturals:
constants have the zero vector, atom `i` has the corresponding unit vector,
negation preserves bounds, addition and subtraction take componentwise
maxima, multiplication adds them, and a power by `n` multiplies them by `n`.
The structural coefficient ℓ¹ bound is

```text
‖z‖₁ = |z|        ‖xᵢ‖₁ = 1        ‖-a‖₁ = ‖a‖₁
‖a ± b‖₁ = ‖a‖₁ + ‖b‖₁
‖a b‖₁ = ‖a‖₁ ‖b‖₁                 ‖aⁿ‖₁ = ‖a‖₁ⁿ.
```

These are bounds on the expanded polynomial, not a normalization request.
They are computed by structural recursion over the tree; `evalKron` later
evaluates the same tree as written.  In particular, cancellation is not used
to make either the degree box or coefficient bound smaller.

For two sides, let `dᵢ` be the maximum of their structural degree bounds and
let `H = ‖L‖₁ + ‖R‖₁`.  For a characteristic-`p` quotient witness `Q`, use
the componentwise maximum of all three degree bounds and
`H = ‖L‖₁ + ‖R‖₁ + p ‖Q‖₁`.  The mixed-radix strides and dense-box size are

```text
s₀ = 1,       sᵢ₊₁ = sᵢ (dᵢ + 1),       D = ∏ᵢ (dᵢ + 1).
```

Thus `code(e) = ∑ᵢ eᵢ sᵢ` is injective for `eᵢ ≤ dᵢ` and is below `D`.
Choose

```text
W = Nat.log2 H + 2,       B = 2^W.
```

This deliberately conservative formula also covers `H = 0` and gives
`2 H < B`.  It is one shared base for the complete check, never a base chosen
from the values obtained after evaluation.

The preflight computes the structural bounds exactly, with saturation.
Every bound operation (the absolute value of a constant, the sums and
products of the ℓ¹ recurrence, power by square-and-multiply with exponent
zero giving `1`, and the dense product `∏ᵢ (dᵢ + 1)`) is monotone in its
arguments, so replacing every intermediate value `v` by `min v S` for a fixed
threshold `S` yields either the exact value, when it is below `S`, or exactly
`S`, which certifies that the exact value is at least `S`.  The ℓ¹ threshold
is `S_H = 2 ^ maxPackedBits`, applied to every subtree bound and to `H`: a
saturated side bound `h` has `Nat.log2 h + 2 > maxPackedBits`, so that
subtree's structural packed-bit bound already exceeds the bit budget.  If
the sum of the two compared side bounds saturates, one side is at least
`S_H / 2`, which also exceeds the signed bit budget.  For quotient checks,
the compared sides are `L̃ - R̃` and `p Q`.  The dense threshold is
`S_D = maxDenseDigits + 1`.
Square-and-multiply stops as soon as an intermediate saturates.  Rejected
inputs therefore never construct a coefficient bound beyond the threshold,
and accepted inputs have exact `H`, `W = Nat.log2 H + 2` and `D`.  No
bit-length estimate stands in for these values: an estimate is an upper
bound and cannot justify a decline.

`Hex.Kronecker.Budget` has exactly two fields, `maxDenseDigits` and
`maxPackedBits`.  Their defaults are `65536` digits and `16777216` bits.  In
particular, a matrix with one independent linear atom in each entry is
eligible through `n = 4` by its digit count and declines at `n = 5`, where
`D = 2^25`.

`SizeBound` is the public preflight report.  It contains `degrees`, `strides`,
`digits := D`, `coefficientBound := H`, `digitBits := W`, `outerSlotBits?`,
`packedBits`, and `limitingStage` (`inner`, `outerRow`, `outerColumn`, or
`result`). It also exposes `innerBits`, the signed inner-value bound before
outer packing. The common outer slot bound makes the full convolution result
dominate its row and column operands, so the current signed-packed preflight
selects `inner` or `result`; the row and column stage constructors remain
available in the report API.

For a polynomial of ℓ¹ bound `h` and largest possible mixed-radix code `c`,
`c * W + Nat.log2 h + 2` bounds its signed packed value.  Expression reports
take the maximum of this quantity over every subtree, not just the root: an
expression such as `a * 0` still evaluates `a`.  Term reports take the maximum
over every supplied polynomial.  Matrix reports additionally derive the
outer signed-dot slot width from the row length and those inner-value bounds,
and `packedBits` is the maximum bit size of an operand or intermediate in the
whole check.  Thus both nested packing levels are covered before evaluation.

`sizeExprEq`, `sizeTermsEq`, `sizeMulTerms`, `sizeMulTree`,
`sizeTreeTermsEq`, and their `Mod` quotient-witness
variants return this record (or a shape/index error) without computing `B^s`,
packing a term, or multiplying packed values.  Arithmetic may saturate only
at the two stated thresholds; a reported accepted bound is exact, while an
overflow diagnostic says `at least <limit + 1>`, which the saturation
certifies, rather than presenting the saturation value as exact.

## Kernel evaluation

For a validated plan, `evalKron` maps atom `i` to `B ^ sᵢ`, maps an integer
constant to itself, and interprets every constructor by the corresponding
`Int` operation.  Literal powers use explicit square-and-multiply recursion;
they do not perform one multiplication per exponent unit.  Every intermediate
power has exponent at most the requested exponent and is included in the
subtree bit bound.  `evalKron` uses structural recursion and evaluates the
input tree as written.  It does not call `Expr.toPoly`, collect like terms,
construct a `PolyList`, or traverse the dense box.

`packTerms` applies the same substitution directly to `PolyList Int`:

```text
packTerms(B, s, P) = ∑(e,c) in P, c * B^code(e).
```

It validates exponent-list length and the common degree box.  Its cost is one
structural pass over the supplied support; it does not materialize zero
digits.  The initial public Boolean checks are:

```lean
checkExprEq   (budget : Budget) (k : Nat) (lhs rhs : Expr) : Bool
checkTermsEq  (budget : Budget) (k : Nat)
    (lhs rhs : Hex.MvPoly.Kernel.PolyList Int) : Bool
checkMulTerms (budget : Budget) (mode : MulMode) (k n r m : Nat)
    (M A C : List (List (Hex.MvPoly.Kernel.PolyList Int))) : Bool
checkMulTree (budget : Budget) (mode : MulMode) (k n r m : Nat)
    (M : List (List (Hex.MvPoly.Kernel.PolyList Int)))
    (A : List (List Expr))
    (C : List (List (Hex.MvPoly.Kernel.PolyList Int))) : Bool
checkTreeTermsEq (budget : Budget) (k : Nat) (lhs : Expr)
    (rhs : Hex.MvPoly.Kernel.PolyList Int) : Bool
```

Each programmatic `check*` function first computes and compares both `digits`
and `packedBits` with the supplied budget, validates shapes and indices, and returns `false` before
packing if any check fails.  `checkMulTerms` reads matrices as row lists,
checks their rectangular dimensions, and checks every row-by-column identity
of `M * A = C`.  Its coefficient bound for output `(i,j)` is
`∑t ‖Mᵢₜ‖₁ ‖Aₜⱼ‖₁ + ‖Cᵢⱼ‖₁`; its common plan takes the componentwise maximum
degrees and maximum coefficient bound over all output coordinates.  Precisely,
the degree bound at `(i,j)` is, componentwise,

```text
max (max_t (degree(Mᵢₜ) + degree(Aₜⱼ))) (degree(Cᵢⱼ)).
```

The quotient-witness form also includes `degree(Qᵢⱼ)` in this maximum and
adds `p ‖Qᵢⱼ‖₁` to the coefficient bound.  Omitting the degree addition would
permit mixed-radix collisions and is not a valid plan.

`checkMulTree` checks the mixed product with term-list rows and expression
tree columns: `∑t packTerms(Mᵢₜ) * evalKron(Aₜⱼ) = packTerms(Cᵢⱼ)`.
Validate rectangular shapes, term exponent arity and every tree's atom
indices. Use the trees' structural per-atom degrees and ℓ¹ bounds in the
same common product plan, including the added degrees of each product.
`sizeMulTree` includes the structural subtree bounds used by `sizeExprEq`;
the same saturation threshold applies to every subtree and product bound.
No entry tree is expanded to a term list. Its `Mod` form checks
`M̃ Ã − C̃ = p Q` with canonical residue term lists on the left and result,
and integer expression trees on the right whose literal leaves satisfy
`Expr.residues p`, the same contract as `checkExprEqMod`. Negation,
subtraction and intermediate tree values need not be canonical residues.
The integer quotient lists are canonical; `sizeMulTreeMod` also includes
the degree and height of `p Q`. Tree-versus-list value equality is
`checkTreeTermsEq`, with `sizeTreeTermsEq` including both operands and every
tree subtree before evaluating their packed values. Their `Mod` forms add
the same residue-leaf and quotient contracts.

After the inner Kronecker packing, a matrix row and column are lists of signed
integers.  `MulMode.plain` uses the existing direct-`List.rec`
`Hex.Matrix.Packed.dotInt`; it is the default because it performs `r`
multiplications on inner-sized integers.  `MulMode.signedPacked` uses
`Hex.Matrix.Packed.columns`, `packSignedCut`, `packSignedCol`, and
`dotIntPacked`.  The existing nonnegative and negated-nonpositive parts turn
a row-by-column dot product into four `Nat.mul`, two `Nat.add`, and one
`Int.sub`, without introducing a new signed representation.

The signed-packed mode is not presumed faster.  Before any inner value is
evaluated, its preflight bounds absolute values from the ℓ¹ bounds, degrees,
base and strides, derives an outer slot width whose checked inequality is
`r * K^2 < 2^V`, and includes the outer operands in `packedBits`.  The
companion reuses `dotIntPacked_eq`; this library neither copies its
implementation nor re-proves its signed-digit argument.  Certificate
consumers may select this mode only in a crossover regime established by the
term-list-product benchmark; otherwise they use `plain`.  Both modes check
the same row-by-column identity and are separately hash-compared.

All checks return `Bool`.  A false value does not distinguish a malformed
input, an exhausted budget, or unequal packed integers; programmatic and
tactic callers run the size/validation preflight first when they need a
structured decline.

The `Kernel` namespace also supplies `exprEq`, `termsEq`, `mulTerms`,
and their `Mod` forms for certificate replay after elaborator preflight.
The mixed forms `mulTree` and `treeTermsEq`, with their `Mod`
variants, use the same separation between preflight and kernel replay.
`treeTermsEqAt` accepts quoted digit bits and strides, checks that they equal
the structural plan, and then evaluates at that point. Its soundness follows
from `treeTermsEq`; supplied point parameters never bypass bound validation.
These forms have no budget argument and no saturation cap. They validate
indices, shapes and residue/quotient inputs, compute only root degree and
coefficient bounds, derive the strides and base, and compare packed values.
They compute no dense digit count, packed-bit report or list of observed
subtrees. The budget controls elaborator resource use; it is not a soundness
premise. Mixed-radix injectivity needs the root degree box and `2 H < B`.

`Kernel.exprEqPlan` accepts a degree vector and digit width from the
elaborator. It checks the vector against the structural root degrees and
checks `2 H < 2^W` before using them. Both expression forms have independent
soundness theorems. The other `Kernel.*_sound` theorems keep the
corresponding universal ring conclusions; the existing programmatic
`check*_sound` statements are unchanged.

For matrix replay, the root bounds include each row-by-column product's
added degrees and summed coefficient products. The optional `innerBits`
and `slotBits` arguments are used only by `signedPacked`: the kernel checks
the packed operands' absolute bounds and `r K² < 2^V` with the existing
`dotValid` predicate. Zero defaults suffice for `plain`. The internal
`Kernel.plan` record uses zero values for unused report fields; it is an
evaluation plan, not a `SizeBound` resource report for callers to inspect.

`Preflight.exprEq` computes exactly the public `sizeExprEq` report, as
proved by `Preflight.exprEq_eq`, using bit-length guards for coefficient
saturation. For a nonzero value, `log2 n < maxPackedBits` tests whether it is
below the coefficient threshold without constructing that threshold.
A multiplication may saturate immediately only when the sum of the two
floor logarithms certifies overflow; otherwise it computes and clips the
product exactly. The threshold is allocated only when saturation actually
occurs. Thus small accepted inputs allocate no two-megabyte cap, while all
accepted reports and certified lower bounds remain unchanged.

## Positive characteristic

Packed arithmetic is always integer arithmetic.  There is no base-`p`
packing and no reduction of a packed integer modulo `p`.

For `0 < p`, lift canonical residue coefficients in `[0,p)` to `Int`.  To
certify `L = R` in characteristic `p`, compiled code supplies a canonical
integer `PolyList` quotient `Q` and the kernel checks

```text
evalKron L - evalKron R = p * packTerms Q.
```

`checkExprEqMod` and `checkTermsEqMod` take `p` and `Q`; the matrix form
`checkMulTermsMod` takes a `MulMode`, dimensions, and one quotient term list
per output entry.  They verify
`0 < p`, canonical residue inputs, quotient and matrix shapes, and the common
bounds stated above.  Balanced-digit injectivity then recovers the integer
polynomial identity `L̃ - R̃ = p Q`, which becomes `L = R` in characteristic
`p`.  The converse supplies completeness: coefficientwise equality modulo
`p` makes the quotient coefficients integral.

The quotient may be sparse or dense; packing it is linear in its actual
support.  Producing it is compiled work and is never replayed in the kernel.
A consumer that has no quotient witness uses the modulus-parametrized
`PolyList Nat` operations of [issue #10257](https://github.com/kim-em/hex-dev/issues/10257).
That fallback expands and reduces term lists coefficientwise and makes no
claim about base-`p` packed multiplication.

## Kernel discipline and soundness boundary

Every definition reduced by a check is `@[expose]`, structurally recursive on
`Expr` or lists, and uses only `Nat`/`Int` arithmetic and Boolean comparisons,
including `Nat.pow`, shifts and masks used by the established packing code.
There is no `Array`, `Vector`, `Fin`, `Finset`, `UInt64`, `dite`, matrix
indexing, well-founded recursion, `implemented_by`, `native_decide`, or
normal-form construction on the kernel path.  Hot list folds are written
with direct `List.rec` or `Expr.rec` when measurement shows the corresponding
`brecOn` equation form is material, following [matrix-tactics §Kernel discipline](../../SPEC/matrix-tactics.md#kernel-discipline).

This Mathlib-free library proves arithmetic identities needed to relate its
own evaluators and the existing packed primitives, but it does not state the
universal commutative-ring denotation theorem.  That theorem, bounded-box
injectivity, `MvPolynomial` factorization, and matrix soundness belong to the
companion.  Bounded-box recovery calls `Hex.Internal.packDigits_inj` after
mixed-radix flattening.  Matrix proofs reuse the row-packing bounds already
factored for `Hex.Internal.mulEqCert_iff` and
`HexMatrixMathlib.dotIntPacked_eq`; a needed generalization is made in
`HexMatrix` rather than copied here.  The full-convolution proof follows
`Hex.Matrix.CharPolyKernel.convolution_eq_of_check` from the packed Berkowitz
certificate, factoring a common lemma if its exact list shape is needed.

## Conformance and benchmarks

`conformance/HexKronecker/Conformance.lean` replays the core Boolean contract,
and `conformance/HexKronecker/EmitFixtures.lean`, registered as
`lean_exe hexkronecker_emit_fixtures`, emits
`conformance-fixtures/HexKronecker/identities.jsonl` cases for expression
equality, term-list equality, integer matrix products, and
characteristic-`p` quotient witnesses.  Cases cover zero atoms, zero and
negative constants, cancellation, powers zero and one, boundary exponents,
rectangular products, rejected shapes and indices, a corrupt quotient, and a
dense-size decline.  A SymPy oracle reconstructs the original expressions or
term lists over `ZZ`, expands them independently, checks the integer or
`p * Q` identity coefficientwise, and checks every reported degree, stride,
digit and bit bound.  `scripts/oracle/kronecker_sympy.py` reads that fixture
and is added as one tuple to `scripts/ci/run_oracles.sh`; no workflow or job
is added.

`bench/HexKronecker/Bench.lean` contains separate checker registrations for
trees and term-list products.  Both sweep atom counts `1, 2, 3, 4, 6, 8` and
per-atom degree bounds `2, 4, 8, 16`.  Accepted points and preflight declines
are separate registrations: decline rows are budget/protocol anchors and make
no complexity claim.  Tree families
hold the constructor pattern explicit and record its multiplication count;
term-list families record input support and matrix inner dimension.  Every
row records the exact `D`, `W`, `packedBits`, input nodes/support, GMP
multiplication count, and a result hash.

The cost claim is output-sensitive in the packed bit size `N`, not in sparse
support products.  Packing is linear in the input tree or supplied supports;
each accepted scalar multiplication is a GMP integer multiplication on at
most `N`-bit values.  A plain outer dot uses `r` inner-sized multiplications;
a signed-packed outer dot uses four multiplications at its reported outer bit
size, and the benchmark hash-compares both modes.  Registrations use
[benchmarking's](../../SPEC/benchmarking.md#choosing-the-complexity-claim) first
applicable mode.  A two-sided parametric claim is used only where the family
fixes the operation count and one GMP multiplication regime while varying
`N`.  A family crossing GMP regimes uses the one-sided quadratic upper bound
from the
[GMP multiplication algorithms](https://gmplib.org/manual/Multiplication-Algorithms)
plus the linear traversal cost, and records observed faster regimes as such.
Atom or degree is never used as a proxy for `N`.

## Consumers

- [hex-poly-det's packed arm](https://github.com/kim-em/hex-dev/issues/10265)
  replaces selected `checkDetPolyList` product identities with
  `Kernel.mulTerms` after this preflight accepts the dense box. Its tree
  certificate uses `Kernel.mulTree` for list transform rows against retained
  input trees, and tree-versus-list equality for the target value.
  The mixed modular API also accepts caller-supplied residue-leaf trees;
  the determinant frontend initially retains its existing residue-list
  route rather than changing residue reification.
- [hex-poly-det-mathlib's closed forms at `n ≤ 3`](https://github.com/kim-em/hex-dev/issues/10264)
  use the expression checker instead of a final `ring` call.
- The three identities in hex-generic-rank's `checkRankPolyList` are a later
  consumer.  They retain term-list checking whenever the dense box is larger.

For a certificate consumer, the hard eligibility predicate is both default
budget comparisons.  The measured crossover table then selects `plain` or
`signedPacked`.  When both the sparse and dense checkers are available, the
consumer also uses the Phase-4 crossover table keyed by `packedBits`, input
supports and matrix inner dimension; that table is fixed from the
preregistered adjacent comparison before the consumer is activated.  A
missing table entry selects the sparse checker.  The consumers depend on this
library; no dependency is added in the reverse direction.
