# 2026-05-08 00:22 UTC — interactive session (Factorization record SPEC PR)

## Accomplished

Drafted the `Factorization` record SPEC PR on a new branch
`bz-factorization-record-spec` cut off `origin/main` (post-#2563).

### SPEC additions

- `SPEC/Libraries/hex-berlekamp-zassenhaus.md`:
  - Replaced `Array ZPoly` with `Factorization` in the public API:
    `factorSlow : ZPoly → Factorization`,
    `factorFast : ZPoly → Option Factorization`,
    `factor : ZPoly → Factorization`,
    `factorWithBound : ZPoly → Nat → Factorization`.
  - Inserted a new "Output convention: the `Factorization` record"
    section defining the record (signed `scalar : Int` field +
    `factors : Array (ZPoly × Nat)` with multiplicities), the
    `Factorization.product` function, the post-condition contract
    for `factor`'s output (5 invariants), the "don't break content
    into primes" convention with FLINT/SymPy precedent, and an
    explicit edge-case table covering 13 inputs (including `0`,
    `±1`, constant primes, `X`, `X²`, repeated factors, signed
    inputs).
  - Added a "Mathlib-free `Hex.ZPoly.Irreducible` class" section
    with the rationale comment (why a class, not a plain Prop:
    `Fact` is unavailable in our Mathlib-free setting) and
    `isIrreducible` boolean checker built on the `Factorization`
    projections.
  - Updated the Group C `factor_product_of_bound` theorem statement
    to use `Factorization.product` instead of `Array.foldl`.

- `SPEC/Libraries/hex-berlekamp-zassenhaus-mathlib.md`:
  - Updated `factor_product`, `factor_irreducible_of_nonUnit` (the
    corrected form of the broken `factor_irreducible`), and
    `factor_unique` theorem statements to use the `Factorization`
    record API.
  - Documented why `factor_irreducible` had to be downgraded:
    constant content factors like `C 6` are reducible in
    `Polynomial ℤ`, but `Factorization.factors` by SPEC contains
    only irreducible non-unit polynomial factors, so the per-element
    irreducibility claim becomes precisely correct.
  - Added the `Hex.ZPoly.Irreducible_iff_polynomialIrreducible`
    bridge theorem.

- `SPEC/Libraries/hex-poly-z.md`: added `Hex.ZPoly.IsUnit`
  definition + decidable instance.

## Current frontier

The SPEC PR is ready to push and open. After it lands:

- The pending human-oversight issue (deliverable B) can reference
  it from Context.
- The hex-nf branch's references to `Factorization` and
  `Hex.ZPoly.Irreducible` (currently forward references) become
  resolvable.

## Next step

1. Commit this work as a single SPEC commit on
   `bz-factorization-record-spec`.
2. Push to `origin`.
3. Open the PR via `gh pr create`. Title:
   `spec: introduce Factorization record for HexBerlekampZassenhaus.factor`.
4. After PR is open: file the human-oversight issue (deliverable
   B) referencing this SPEC PR.

## Blockers

None. The implementation work to migrate
`HexBerlekampZassenhaus/Basic.lean` to the new API is the
human-oversight issue's deliverable, separate from this SPEC PR.
