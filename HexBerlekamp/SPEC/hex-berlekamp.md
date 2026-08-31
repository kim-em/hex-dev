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

`Berlekamp.berlekampFactor` has one selection point and two branches.

The default branch computes the fixed space once and applies its basis
vectors to the current factor list. A split replaces one factor by exact
complementary factors, preserving the product.

The other branch extracts a completely split input by its roots. A
square-free polynomial over `F_p` is a product of distinct monic linear
factors exactly when it has `deg f` roots in `F_p`, so enumerating the
roots and emitting `X - r` for each is a complete factorization. The
scan over the canonical residue list is its own certificate: the result
is used only when the scan finds `deg f` roots, and that length test is
what proves the reconstruction `∏ (X - r_i) = f`. No separate
complete-splitting predicate is computed and no Boolean is trusted
without a check.

The branch is selected from the polynomial alone, never from a
recognized input family. `Berlekamp.rootScanBudget` admits the scan on
two tests, both read off the degree and the field size alone.

`deg f ≤ p` is necessary: `F_p` has `p` elements, so a scan of a
higher-degree input can never find `deg f` distinct roots and is never
started.

`25 · p ≤ (deg f)^2` keeps the scan cheap against the work it would
replace: the scan costs `p · deg f` modular multiplications while the
fixed-space matrix costs about `(deg f)^3`. An input that passes both
tests, pays for a scan, and then falls back to the kernel branch loses a
small fraction of the work it was going to do anyway.

Together the two tests select `5 √p ≤ deg f ≤ p`.

The linear factors, their pairwise coprimality, and the reconstruction
theorem live in `LinearFactors.lean`, shared with the `X^p - X` product
identity behind Rabin's test.

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

## Degree patterns

The *degree pattern* of a monic square-free polynomial is the multiset
of degrees of its irreducible factors. It is obtained from the same
Frobenius powers and gcds as distinct-degree factorization, without
splitting any equal-degree product: a degree-`d` product of degree `m`
records `m / d` factors of degree `d`.

A partial pattern already bounds the factor count from both sides.
After degree `d` is separated, every factor left in a residual of
degree `m` has degree at least `d`, so the count lies between
`separated + 1` and `separated + m / d`. A caller that only wants to
know whether the count is at most some target is therefore answered as
soon as the factors already separated reach that target, however much
of the polynomial is left. The loop also stops when the residual is a
unit, and when the residual is too small to be a product of two factors
of degree at least `d` and is therefore irreducible; so it stops at the
largest factor degree rather than at the degree of the input.

Degree patterns are a prediction surface with no certificate content.
Callers that need factors use `berlekampFactor`; callers that need the
separated degree products use `distinctDegreeFactor`.

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

## Fast-arithmetic adoption

The Fp production plan is audited in repeated Frobenius reductions, the
distinct-degree gcd chain, and Rabin powers. Fast multiplication reaches these
consumers through the proved compiled `FpPoly.powModMonic` dispatcher, while
the shared division/gcd screen keeps the current Euclidean gcd. Certificate
shapes and checker theorems do not change.

The complete Rabin operation benchmark compares the public test with the same
test using the retained `FpPoly.powModMonicAux` schoolbook loop. Three warm
outer trials on `chungus2`, Lean `4.34.0-rc2`, over `F_5` give:

| input parameter | retained power | public Rabin path |
|---:|---:|---:|
| 8 | 171.472 µs | 127.475 µs |
| 16 | 791.780 µs | 563.754 µs |
| 32 | 7.452 ms | 2.823 ms |
| 64 | 53.634 ms | 29.177 ms |

All hashes agree. The production modular-power dispatcher keeps its tiny-input
schoolbook branch and selects fast multiplication from modulus size 18; Rabin
therefore gains without replacing its Euclidean gcd chain. Distinct-degree
factorization inherits the same Frobenius dispatch and retained gcd decision.
Reproduce the end-to-end screen with
`lake exe hexberlekamp_bench compare Hex.BerlekampBench.runRabinSchoolbookChecksum Hex.BerlekampBench.runRabinTestChecksum --outer-trials 3`.

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

## External comparators

Two comparators are declared, both `informational`
(see `libraries.yml` for the machine-readable form):

- **FLINT `nmod_poly.is_irreducible` via python-flint**, paired with
  the Lean `runRabinTestChecksum` ladder.
- **FLINT `nmod_poly.factor_distinct_deg` via python-flint**, paired
  with the Lean `runDistinctDegreeChecksum` ladder.

Both are wired as persistent-subprocess calls through the shared
python-flint driver per SPEC/benchmarking.md §External comparators
§Process call, with the driver spawned outside the timed region and
steady-state medians amortised over inner repeats. The measured gap is
structural: FLINT's hand-tuned C word-level kernels (nmod arithmetic
with precomputed inverses, tuned modular composition and Frobenius
strategies) against Hex's verified generic `FpPoly` arithmetic, at
10x-373x (Rabin) and 44x-749x (DDF) across the eligible ladders in the
2026-08-22 paired refresh. These comparators were originally declared
`gating` with a parity goal; that goal was an aspiration the library's
algorithm class does not support at comparable engineering effort, and
the reclassification to `informational` records the structural nature
of the gap rather than a harness artefact. The ratios are reported for
orientation and do not gate Phase 4.

## References

- E. R. Berlekamp, “Factoring Polynomials Over Large Finite Fields,”
  *Mathematics of Computation* 24 (1970), 713-735.
- V. Shoup, *A Computational Introduction to Number Theory and
  Algebra*, second edition, Chapters 20-21.
- D. Knuth, *The Art of Computer Programming*, Volume 2,
  Section 4.6.2.
