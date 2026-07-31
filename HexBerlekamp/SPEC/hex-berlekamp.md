# hex-berlekamp

`hex-berlekamp` factors dense polynomials over a prime field and
checks irreducibility certificates. It depends on `hex-poly-fp`,
exact matrix row reduction, and finite-field arithmetic, and has no
Mathlib dependency.

## Berlekamp matrix

For a monic polynomial `f` of degree `n` over `𝔽_p`, the Frobenius
map on `𝔽_p[X] / (f)` sends `h` to `h^p`. In the basis
`1, X, ..., X^(n-1)`, its matrix is `Q_f`. The kernel of `Q_f - I`
is the fixed space.

If `f` is square-free and has `r` monic irreducible factors, the
Chinese remainder theorem identifies its fixed space with `𝔽_p^r`.
Thus:

- the fixed-space dimension is the number of irreducible factors;
- `f` is irreducible exactly when the fixed space contains only
  constants;
- a nonconstant fixed element splits `f` through the polynomials
  `gcd(f, h - c)` for `c ∈ 𝔽_p`.

The matrix construction is in `BerlekampMatrix.lean`. Exact
nullspace calculation is supplied by the finite-field row-reduction
library.

## Factorization

`Berlekamp.berlekampFactor` computes the fixed space once and applies
its basis vectors to the current factor list. A split replaces one
factor by exact complementary factors, preserving the product.

The result records:

- the monic factors;
- their product;
- the fixed-space witnesses used to split them.

For every monic input, the Mathlib-free theorem
`Berlekamp.prod_berlekampFactor` proves that the returned factors
multiply to the input. `hex-berlekamp-mathlib` proves that the factors
returned from a square-free input are irreducible.

Distinct-degree factorization is provided separately. It partitions a
square-free polynomial into products of irreducible factors of a common
degree, using repeated Frobenius powers and greatest common divisors.

## Rabin irreducibility certificates

A monic polynomial `f` of degree `n` over `𝔽_p` is irreducible exactly
when:

1. `f` divides `X^(p^n) - X`;
2. for every prime divisor `q` of `n`,
   `gcd(f, X^(p^(n/q)) - X) = 1`.

`Berlekamp.rabinTest` evaluates this criterion. The certificate records
modular-power data and Bézout witnesses for the coprimality checks.
The checker reconstructs every modular power and verifies every
Bézout identity.

Certificate generation and Berlekamp factor search are compiled
search procedures. The checker and its correctness theorem determine
the trusted result.

## Tactic surface

The ordinary umbrella supplies `factor_poly` and `irreducibility` for
closed `FpPoly p` expressions at literal prime moduli within the
`ZMod64` bounds.

The parser accepts polynomial variables, constants, numerals,
addition, subtraction, multiplication, negation, and natural powers.
It produces a dense polynomial and a proof of the parsing equality.
The emitted term contains:

- a coefficientwise product check;
- one irreducibility-certificate check per distinct factor;
- no invocation of the factorization search.

`hex-berlekamp-mathlib` adds the same syntax for
`Polynomial (ZMod p)`.

## Mathematical companion

`hex-berlekamp-mathlib` uses the ring equivalence

```text
FpPoly p ≃+* Polynomial (ZMod p)
```

to connect executable arithmetic with Mathlib's polynomial theory.
It proves:

- completeness of the Berlekamp splits on square-free inputs;
- soundness and completeness of Rabin's criterion;
- soundness of the certificate checker;
- correspondence of coefficients, products, divisibility, and
  irreducibility across the equivalence.

## Verification

Changes must pass:

- the root build and trust-surface check;
- finite-field factorization and irreducibility conformance fixtures;
- the external finite-field oracle;
- factor-tactic regression modules;
- benchmark verification for the Berlekamp matrix, distinct-degree
  factorization, Rabin's test, and full factorization.

Performance reports compare only operations with the same
input-output relation. They record the exact source revision,
toolchain, prime, degree, input family, machine, and repetition
protocol.

## References

- E. R. Berlekamp, “Factoring Polynomials Over Large Finite Fields,”
  *Mathematics of Computation* 24 (1970), 713-735.
- V. Shoup, *A Computational Introduction to Number Theory and
  Algebra*, second edition, Chapters 20-21.
- D. Knuth, *The Art of Computer Programming*, Volume 2,
  Section 4.6.2.
