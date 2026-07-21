# Algebraic Roots and Number-Field Towers

## Summary

The design extends Hex with factorization-lazy algebraic numbers, polynomial root
APIs over algebraic coefficient fields, explicit towers of number fields, splitting
fields, and conversion of towers to primitive-element presentations.

The implementation is divided into two computational libraries and their Mathlib
companions. The following constraints apply throughout:

- Index tower elements as `NumberTower.Elem T`, allowing each tower to supply the
  arithmetic operations required by polynomial gcds and resultants. The
  law-bearing field package is proved in the Mathlib companion.
- Make tower constructors private and enforce the complex-embedding invariant
  through `ofQAdjoin`, `adjoin?`, and `split?`; prove preservation in the Mathlib
  companion.
- Use `cypari2` and `python-flint` as external oracles. Sage remains local-only
  under repository policy.
- Strengthen `hex-resultant-mathlib` in stages, completing full resultant
  correspondence before tower correctness.

Root identity remains based on `SimpleRoot` and `RefinedIsolation`. “Lazy” means
factorization-lazy: minimal-polynomial computation is deferred until exactification,
while certified root isolation remains eager.

## Public APIs and library split

### `hex-number-field` and `hex-number-field-mathlib`

- Retain canonical `AlgebraicNumber`, `QAdjoin`, and existing source
  compatibility.
- Add `AlgebraicRoot`, storing a primitive, positive-leading-coefficient,
  squarefree `ZPoly`, its `SimpleRoot`, and a matching `RefinedIsolation`. The
  polynomial need not be minimal or irreducible.
- Provide factorization-lazy `add`, `sub`, `mul`, `neg`, `inv`, and division.
  Resultants produce the enclosing polynomial; squarefree normalization and
  bounded ball disambiguation select the represented root.
- Handle zero explicitly in multiplication and inversion. Strip spurious `X`
  factors introduced by the product eliminant; coefficient reversal instead
  trims any degree drop from an original zero constant coefficient and cannot
  itself acquire an `X` factor.
- Add checked `exact? : AlgebraicRoot → Option AlgebraicNumber`, primary total
  `exact : AlgebraicRoot → AlgebraicNumber`, and `AlgebraicNumber.toRoot`.
- Implement semantic `BEq` with a same-polynomial fast path and exactification
  fallback. Add a cheap sound `isZero` test using the polynomial’s zero root and
  stored isolation.
- Introduce opaque `AlgebraicPoly`, constructed from `Array AlgebraicNumber` and
  normalized with semantic `isZero`. Do not use `DensePoly AlgebraicNumber`,
  because its required `DecidableEq` would incorrectly equate structural and
  semantic equality.
- Add a runtime-constructible `ZPoly.CheckedIrreducible` wrapper around the
  shipped Boolean checker; its semantic interpretation remains in the
  factorization companion. Add checked `QAdjoin.roots?` under that wrapper and
  `AlgebraicPoly.roots?`, with primary total `roots` wrappers. Return a
  `RootSet` distinguishing the zero polynomial’s universal root set
  from a finite array of roots with positive multiplicities.
- Run Yun decomposition first and count candidates independently for each
  squarefree component. Filter conjugate-embedding impostors using a named,
  input-computable `evalDisambiguationPrec` bound derived from an evaluation
  eliminant and a certified nonzero lower bound. Lazy binary arithmetic instead
  uses `resultIsolationPrec`, directly from HexRoots separation for its one
  squarefree eliminant.
- Restructure the Mathlib companion around lazy-operation soundness,
  exactification, root completeness, multiplicity, and `_isSome` theorems. Retain
  common-field construction only as an internal mechanism for canonical algebraic
  coefficient polynomials.

### `hex-number-field-tower` and companion

- Add an opaque runtime `NumberTower` with validated levels stored using flattened
  mixed-radix rational coordinates.
- Define `NumberTower.Elem (T : NumberTower)` with canonical coordinates, semantic
  structural equality, and operational arithmetic specialized to `T`. Define
  tower polynomials as `DensePoly (NumberTower.Elem T)`; install the law-bearing
  field package only in the Mathlib companion after proving checker soundness.
- Add dependent result structures:
  - `Extension T`, containing the new tower, inclusion map, generator, and its
    `AlgebraicRoot`.
  - `Factorization T f`, containing normalized irreducible factors and
    multiplicities.
  - `Splitting T f`, containing the extension and complete roots of the embedded
    polynomial.
  - `Flattening T`, containing a canonical primitive `AlgebraicNumber` and mutually
    inverse coordinate maps to its `QAdjoin`.
- Expose only `rat`, `ofQAdjoin`, `adjoin?`, `factor?`, `split?`, and `flatten?`;
  keep raw constructors private.
- Require every level to carry a successful computational factorization check.
  The companion proves both its semantic irreducibility and that the chosen
  complex generator zeros the defining polynomial after all lower generators
  are embedded.
- Implement characteristic-zero Trager factorization recursively: Yun
  decomposition; at each `K(α)/K` level, a deterministic bounded shift search
  for a squarefree one-level relative norm; recursive factorization of that norm
  over `K`; and relative gcd recovery over `Elem T`. Rational factorization is
  only the base case. Include the intermediate-field adversary `X² - 3` in
  `ℚ(√2, √3)`.
- `adjoin?` factors the candidate polynomial over the current tower and selects the
  unique factor containing the requested embedded root. A linear selected factor
  returns an identity extension.
- `split?` repeatedly factors and adjoins a root of each nonlinear factor until the
  embedded polynomial splits completely.
- `flatten?` uses deterministic primitive-element shifts and `HexRowReduce`
  coordinate recovery. Add `hex-row-reduce` as a direct dependency.
- Prove field laws, embedding preservation, Trager factor correctness, split
  completeness, termination bounds, and both flattening round trips in the Mathlib
  companion.

## Resultant prerequisites

- Rewrite `hex-resultant-mathlib` to remove the claim that full correspondence is
  unnecessary.
- Stage 1 proves chain-level common-root and bivariate specialization-vanishing
  results. These discharge lazy arithmetic and root-candidate soundness.
- Stage 2 proves the executable-to-`Polynomial.resultant` correspondence over the
  supported integral domains, plus specialization, norm/root-product, and
  discriminant corollaries.
- Require Stage 2 before tower factorization, splitting, and flattening can be
  marked proved.
- Document which downstream theorem consumes each resultant result, avoiding one
  oversized undifferentiated proof obligation.

## Conformance, performance, and documentation

- Cover at least three cases per public operation, including:
  - equal values represented by different nonminimal polynomials;
  - irrelevant factors and repeated eliminant roots;
  - zero multiplication and inversion;
  - repeated-root polynomials and conjugate-embedding impostors;
  - `ℚ(√2, √3)` arithmetic, factorization, adjoin, splitting, and flattening;
  - identity-extension and forward/backward flattening round trips.
- Use `cypari2` as the primary number-field and tower oracle and `python-flint` for
  integer polynomial resultants, factorization, and certified complex roots. Follow
  multiplicity-bucket comparison and extend the existing single CI job.
- Remove all Sage oracle claims from the number-field and resultant specs.
  Nemo/Hecke may be mentioned only as optional local comparisons.
- Replace optimistic fixed timing claims with component-aware ceilings. Fixed-field
  arithmetic retains a direct budget; lazy arithmetic inherits the measured
  HexRoots ceiling for its produced eliminant degree plus separately measured
  resultant overhead. Inputs producing degree above 20 remain local-profile tests
  until optimization work lands.
- Update the planned-library README to remove its hardcoded SPEC count.
- Correct references: attribute *Accelerated tower arithmetic* to van der Hoeven
  and Lecerf ([published paper](https://www.sciencedirect.com/science/article/pii/S0885064X19300342)),
  and cite Yuan’s successive-extension Trager paper through the [authoring
  institution’s publication page](https://mmrc.amss.cas.cn/xz/MM_Preprints/Vol_25/).

## Assumptions and defaults

- Both new library pairs remain Mathlib-free computationally; semantic proofs live
  only in their companions.
- `AlgebraicNumber` remains the canonical/minimal representation; `AlgebraicRoot`
  is explicitly factorization-lazy.
- All certificate-producing algorithms use bounded `Option` forms, companion
  `_isSome` theorems, and loud total wrappers where a total algebraic operation is
  advertised.
- Tower embeddings are fixed embeddings into `ℂ`, not abstract fields up to
  isomorphism.
- Deterministic ordering, shift enumeration, normalization, and multiplicity
  conventions are normative so fixtures and oracle output remain reproducible.
