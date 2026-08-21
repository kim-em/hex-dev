# Cyclotomic polynomial libraries: SPEC

## Accomplished

Wrote `SPEC/Libraries/hex-cyclotomic.md` for `hex-cyclotomic` and
`hex-cyclotomic-mathlib` (issue #9321), expanding the "Cyclotomic
polynomials" bullet of `SPEC/future-work.md` into a full specification.

Design decisions the SPEC records:

- Every entry point is indexed by a `CheckedFactorization n` from
  hex-int-factor. `checkFactorization` already requires `0 < subject`,
  so `CheckedFactorization 0` is uninhabited and neither a `0 < n`
  argument nor `[NeZero n]` is needed. That corrects the future-work
  bullet, which asked for one of those.
- `n = 1` is the base case of both routes and needs no special handling:
  empty prime list, `radical = 1`, kernel exponent `1`, empty proper
  divisor product.
- The implementation is the prime ladder
  `Φ_{m p} = Φ_m(x^p) / Φ_m` over the distinct primes, followed by one
  substitution `Φ_n = Φ_rad(x^{n/rad n})`. The divisor recursion is the
  reference route only: `O(φ(rad n)² + φ(n))` against `O(n²)`.
- Exactness of the divisions: the total constructor takes
  `DensePoly.divMod`'s quotient, which is a total function and so is not
  a design-principle-8 fallback; the checked constructor uses
  hex-poly-z's `divExact?` and propagates the `Option` rather than
  collapsing it, because the unreachability of `none` is the deep
  theorem and is not available yet. `checkCyclotomicProd` reflects the
  divisor-product identity at a specific `n`.
- No hidden refactorization: the divisor family derives a
  `CheckedFactorization d` per divisor from the one certificate, which
  is a new hex-int-factor prerequisite (`divisorsChecked` plus
  `checkFactorization_of_lowers`, so the primality certificates are not
  replayed `τ(n)` times).
- Sparse output is an adapter at a consumer, not a dependency, because
  Lake has no conditional dependencies and hex-sparse-poly sits below
  this library.
- A conformance boundary comparing `(cyclotomic F_d).eval b` with
  hex-int-factor's `cyclotomicSplit?` part values, including the index
  sets, owned by this library's conformance project since it is the one
  that can import both.

Prerequisites named: `DensePoly.substPow` in hex-poly (direct spread
rather than `compose` with a monomial, which is a factor of `deg p`
slower), `ZPoly.divExact?` in hex-poly-z (already scheduled by
hex-poly-z-gcd), three small additions to hex-int-factor, and
`toPolynomial_substPow` plus the monic division transport in
hex-poly-mathlib.

Also updated `SPEC/Libraries/README.md` (library lists, dependency
lists, a DAG paragraph and diagram, index entry), pointed the
future-work bullet at the new SPEC, and updated the cyclotomic
cross-references in `hex-sparse-poly.md` and `hex-int-factor.md`.

## Current frontier

The SPEC is written; nothing is implemented. `HexIntFactor` and
`HexPrimality` are not in `libraries.yml` yet, so the dependency claims
in the new file are draft prose rather than repository state.

## Next step

Nothing in this library can start before hex-int-factor milestone 2
(the certificate and the divisor-function API). The hex-poly
`substPow` prerequisite is independent and could land at any time; it
also cleans up hex-sparse-poly's dense comparison statements.

## Blockers

None for the SPEC. The implementation is blocked on hex-int-factor.
