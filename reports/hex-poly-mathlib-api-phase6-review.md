# HexPolyMathlib API Phase 6 Review

## Scope

Reviewed the Mathlib bridge surface for dense polynomials against
`SPEC/Libraries/hex-poly-mathlib.md` and `PLAN/Phase6.md`.

This review covered:

- `HexPolyMathlib/Basic.lean`;
- `HexPolyMathlib/Euclid.lean`;
- the root import `HexPolyMathlib.lean`;
- downstream consumers in `HexPolyZMathlib`, `HexHenselMathlib`,
  `HexBerlekampMathlib`, and `HexBerlekampZassenhausMathlib` that use
  `toPolynomial`, `ofPolynomial`, `equiv`, degree/leading-coefficient
  transport, divisibility transport, and gcd/xgcd bridge theorems.

This is a review-only Phase 6 slice. It does not edit Lean source.

## Summary

The core bridge is well shaped. `HexPolyMathlib/Basic.lean` exposes
coefficient characterizations for both conversions, arithmetic transport for
zero, one, constants, monomials, addition, multiplication, negation,
subtraction, derivative, round trips, the `DensePoly`/`Polynomial`
`RingEquiv`, degree and leading-coefficient transport, and divisibility
transport. This is enough for downstream proofs to avoid unfolding the
array-backed representation in ordinary conversion goals.

`HexPolyMathlib/Euclid.lean` also has the right normalization story for the
SPEC promise: executable `gcd` and `xgcd` are transported as raw dense outputs
associated to Mathlib's normalized polynomial gcd, not incorrectly stated as
literal equalities. The `toPolynomial_*` theorems are available for callers
working explicitly with conversions, and the `equiv_*` theorems are available
when the ring-equivalence form is cleaner.

The root import is clean and simply re-exports `Basic` and `Euclid`. The
module remains a proof bridge over Mathlib and does not introduce runtime
oracle or executable-path concerns.

I found three concrete Phase 6 polish gaps. None are correctness issues.

## Follow-Up Recommendations

### 1. Fill docstrings on public bridge lemmas

Suggested issue title: `HexPolyMathlib Phase 6: document public conversion bridge lemmas`.

The public bridge API is compact but under-documented relative to the Phase 6
docstring rule. Several exported declarations have no docstring even though
they are the intended user-facing characterization surface:

- `coeff_ofPolynomial`, `coeff_toPolynomial`;
- `ofPolynomial_zero`, `toPolynomial_zero`, `toPolynomial_C`;
- `toPolynomial_add`, `toPolynomial_mul`, `toPolynomial_derivative`;
- `toPolynomial_ofPolynomial`, `ofPolynomial_toPolynomial`;
- `equiv_apply`, `equiv_symm_apply`;
- `natDegree_toPolynomial`, `leadingCoeff_toPolynomial`;
- `toPolynomial_dvd`, `ofPolynomial_dvd`, `toPolynomial_dvd_iff`.

The absence is noticeable because downstream files use these declarations as
the stable bridge API. For example, `HexHenselMathlib/Correctness.lean` uses
`coeff_toPolynomial`, `toPolynomial_mul`, `toPolynomial_add`, and
`leadingCoeff_toPolynomial`; `HexBerlekampZassenhausMathlib/Basic.lean` uses
`natDegree_toPolynomial`, `leadingCoeff_toPolynomial`, and `toPolynomial_dvd`
throughout factorization correctness proofs.

Recommended implementation shape:

- add short docstrings explaining the user-facing role of each conversion,
  arithmetic, round-trip, degree, leading-coefficient, and divisibility lemma;
- keep private fold/diagonal helpers private and undocumented unless their
  names or proof role become non-obvious to maintainers;
- mention on the round-trip lemmas that they are the inverse laws used by
  `equiv`.

Target declaration cluster: `HexPolyMathlib/Basic.lean`, public declarations
from `coeff_ofPolynomial` through `toPolynomial_dvd_iff`.

### 2. Lower unnecessary `CommRing` assumptions on conversion lemmas

Suggested issue title: `HexPolyMathlib Phase 6: generalize conversion round trips and ofPolynomial_mul`.

Most of the conversion characterizations are already stated at the right
generality: `toPolynomial_mul` is over `[Semiring R]`, the additive ring-only
facts use `[Ring R]`, and `equiv` correctly requires `[CommRing R]` because it
is a `RingEquiv`.

The round-trip lemmas and `ofPolynomial_mul` are more restrictive than their
statements appear to need:

- `toPolynomial_ofPolynomial` is currently `[CommRing R] [DecidableEq R]`;
- `ofPolynomial_toPolynomial` is currently `[CommRing R] [DecidableEq R]`;
- `ofPolynomial_mul` is currently proved through `(equiv).symm`, which also
  forces `[CommRing R]`.

The coefficient characterizations that prove these facts are available over
`[Semiring R]`, and `toPolynomial_mul` is already semiring-level. Keeping these
lemmas ring-only makes semiring downstream bridge proofs use stronger local
typeclass assumptions than the conversion API itself requires.

Recommended implementation shape:

- restate `toPolynomial_ofPolynomial` and `ofPolynomial_toPolynomial` over
  `[Semiring R] [DecidableEq R]`;
- prove `ofPolynomial_mul` coefficientwise or through an appropriately
  semiring-level hom surface, if available, rather than through `equiv.symm`;
- leave `equiv` itself at `[CommRing R] [DecidableEq R]`.

Target declaration cluster: `HexPolyMathlib/Basic.lean` round-trip and
`ofPolynomial_mul` block.

### 3. Add conservative `grind` coverage for bridge-normalization goals

Suggested issue title: `HexPolyMathlib Phase 6: tune grind annotations for conversion and Euclid bridge facts`.

The bridge currently has broad `@[simp]` coverage and no `@[grind]`
annotations. The `simp` surface is useful and mostly conservative: coefficient
facts, arithmetic transport, round trips, `equiv_apply`, `equiv_symm_apply`,
degree/leading-coefficient transport, and the raw xgcd Bezout equality all
rewrite in the expected direction.

Phase 6 also calls out `grind` support. Downstream proofs still contain manual
rewrite sequences that are good candidates for small `grind` experiments, such
as coefficient transport through `toPolynomial`, degree/leading-coefficient
transport, and divisibility transport before applying Mathlib polynomial
facts.

Recommended implementation shape:

- try `@[grind =]` on directional equalities such as `coeff_toPolynomial`,
  `coeff_ofPolynomial`, `toPolynomial_add`, `toPolynomial_mul`,
  `toPolynomial_derivative`, `natDegree_toPolynomial`, and
  `leadingCoeff_toPolynomial`;
- try `@[grind]` or leave unannotated for proposition-valued facts such as
  `toPolynomial_dvd`, `ofPolynomial_dvd`, `toPolynomial_dvd_iff`,
  `toPolynomial_gcd_associated`, and `toPolynomial_xgcd_bezout_associated`
  depending on search behavior;
- keep `toPolynomial_xgcd_bezout_raw` as a narrow rewrite if experiments show
  it does not expand xgcd terms unexpectedly.

Target declaration clusters: `HexPolyMathlib/Basic.lean` conversion facts and
`HexPolyMathlib/Euclid.lean` associated-gcd / Bezout facts.

## No Follow-Up Needed

No follow-up is needed for the fundamental conversion surface. The coefficient
lemmas plus zero/one/constant/monomial/add/mul/neg/sub/derivative transport and
round-trip lemmas give callers a sufficient characterization API without
unfolding `toPolynomial`, `ofPolynomial`, or dense-array internals.

No follow-up is needed for the statement shape of `equiv`. It is documented,
uses the right `CommRing` generality for a `RingEquiv`, and has simp lemmas
that expose both application directions. Downstream integer-specialized code in
`HexPolyZMathlib/Basic.lean` can abbreviate it cleanly.

No follow-up is needed for the gcd/xgcd normalization split. The associatedness
lemmas correctly avoid claiming equality with Mathlib's normalized gcd, and the
Bezout bridge exposes the executable raw gcd while providing associated forms
for callers that need Mathlib's `EuclideanDomain.gcd`.

No follow-up is needed for import or namespace hygiene. `Basic.lean` imports
Mathlib polynomial modules plus `HexPoly`, `Euclid.lean` imports `Basic` and
`Mathlib.Algebra.Polynomial.FieldDivision`, and the root import re-exports only
the two intended modules under `HexPolyMathlib`.

## Verdict

`HexPolyMathlib` is close to Phase 6 quality for this slice, but should not be
marked complete until the public bridge lemmas are documented and the small
generality/automation polish items above are addressed. The remaining work is
worker-sized and localized to the existing conversion and Euclidean bridge
declaration clusters.
