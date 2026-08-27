# hex-hensel

`hex-hensel` implements Hensel lifting for dense integer
polynomials. It depends on `hex-poly-fp`, `hex-poly-z`, and modular
arithmetic, and has no Mathlib dependency.

The library contains linear two-factor lifting, quadratic-doubling
lifting, and multifactor lifting. The executable representation is
shared with Berlekamp-Zassenhaus factorization.

## Congruence and reduction

`ZPoly.congr f g m` means that corresponding coefficients of `f` and
`g` are congruent modulo `m`. `ZPoly.reduceModPow f p k` reduces every
coefficient modulo `p^k`.

The reduction functions satisfy the usual laws for addition,
subtraction, multiplication, scaling, and monic polynomials. Conversion
between `ZPoly` and `FpPoly p` uses canonical representatives in
`[0, p)`.

For word-sized moduli, `WordMod` and `toWP` provide the same operations
through Montgomery arithmetic. Their transport theorems show that the
word calculation denotes the ordinary integer reduction.

## Two-factor linear lifting

Suppose

```text
f = g h mod p
```

and Bézout polynomials `s,t` satisfy `s g + t h = 1 mod p`.
One linear step corrects the factorization from modulus `p^k` to
`p^(k+1)`. The correction is computed from the error

```text
(f - g h) / p^k mod p.
```

The result preserves:

- congruence of the lifted factors to the original modular factors;
- the product congruence at the new modulus;
- degree and monicity conditions;
- the Bézout relation needed by the next step.

`linearLift` iterates this construction to a requested exponent.

## Quadratic lifting

Quadratic lifting doubles the available precision. Given a
factorization and Bézout relation modulo `p^k`, one step produces both
relations modulo `p^(2k)`. This reduces the number of precision steps
from linear in `k` to logarithmic in `k`.

`quadraticLift` records the two lifted factors, updated Bézout
polynomials, and their product and coprimality data. The implementation
uses monic division where the mathematical argument requires it and
checks every exact integer division.

### Coefficient-range invariant

`ZPoly.Canonical f m` states that every coefficient of `f` lies in
`[0, m)`. It is the range invariant the modular kernels produce and the
exact hypothesis under which `reduceModPow` is the identity, so it is
what licenses removing a canonicalisation rather than merely reordering
one.

Every field of a quadratic step is built by `addModSquare` or
`subModSquare`, whose last action is the canonical reduction
`reduceModSquare _ m`, so a step at working modulus `m` returns data
canonical modulo `m²`. The word path denotes the same values: its `ofWP`
readback lands in `[0, m²)` and it is proved equal to the bignum path.

The exact-exponent recursion reaches `p^k` from `p^ceil(k/2)`. For even
`k` the step's working modulus squares to exactly `p^k`, so its output is
already canonical at the target and no reduction is needed; for odd `k`
the step overshoots to `p^(k+1)` and the descent is required. Both
outputs of the factor-only last step obey the same invariant, so every
target the multifactor tree passes to a recursive call is canonical and
only the root leaf still reduces.

Each such removal is a `@[csimp]` implementation paired with the
unchanged specification function, so the proof surface reasons about one
algorithm and the compiled code runs the reduced one.

## Multifactor lifting

For a list of pairwise coprime modular factors, multifactor lifting
uses a balanced product tree:

1. split the factor list into two nonempty parts;
2. multiply each part;
3. lift the two products quadratically;
4. recurse inside both lifted products;
5. return the lifted leaves in the original order.

The degree-balanced split avoids an unnecessarily expensive side when
one modular factor dominates the total degree. The public invariants
state:

- preservation of the factor count and ordering;
- monicity of every lifted factor;
- reduction of each lifted factor to its modular ancestor;
- congruence of their product to the target modulo `p^k`;
- coprimality of the complementary product splits.

`multifactorLiftQuadratic` is the primary lifting function used by
integer factorization.

## Direct-coordinate target

For a primitive square-free integer polynomial `f` with leading
coefficient `a`, Berlekamp-Zassenhaus factorization first factors the
monic unit multiple `a⁻¹ f mod p`.

`ZPoly.monicTarget f p k` is the canonical integer polynomial whose
reduction modulo `p^k` represents this unit-normalized modular image.
It remains in the coordinates of `f`; it does not apply the integral
substitution `a^(deg f - 1) f(X/a)`.

The direct Hensel lift used by both classical and lattice
recombination is `ZPoly.directLiftData`. Its lifted-factor indices are
identified with the indices of the selected modular factors.

## Proof responsibilities

The Mathlib-free library proves all executable congruence, product,
degree, list-shape, and invariant-preservation statements.
`hex-hensel-mathlib` supplies the polynomial-ring interpretation:

- coprimality modulo `p` lifts through powers of `p`;
- a successful lift has the expected uniqueness property;
- executable congruence agrees with coefficientwise congruence in
  Mathlib polynomials.

The later Berlekamp-Zassenhaus companion proves the correspondence
between subsets of lifted factors and irreducible integer factors.

## Fast-arithmetic adoption

After [hex-poly-fast](../../SPEC/Libraries/hex-poly-fast.md), the quadratic
multifactor tree reuses its balanced product-tree shape and the `ZPoly`/`FpPoly`
lawful multiplication plans. Complementary-product gcd and Bezout setup use
the fast full or one-sided extended gcd, and repeated division by a fixed node
may cache a `DivPlan`.

This is a benchmark-gated implementation change, not a change to any lifting
invariant. The audit measures complete two-factor and multifactor lifts over
degree, factor-count, coefficient-width, and lift-exponent ladders. A node
uses the fast entry point only where the end-to-end lift improves; small nodes
retain the existing kernels. Product congruence, factor ordering, canonical
coefficient ranges, and exact-division checks remain the public semantics.

The ordered product dispatcher uses the balanced `ZPoly.fastPlan` tree for
factor counts in `[8, 1024)` and the retained left fold elsewhere.  Three warm
outer trials on `chungus2` (AMD EPYC 9455), Lean `4.34.0-rc2`, measured the
shared deterministic linear-factor fixtures as follows (medians):

| factor count | left fold | balanced tree | selected |
|---:|---:|---:|:---|
| 4 | 365 ns | 431 ns | fold |
| 8 | 1.160 us | 1.089 us | tree |
| 128 | 1.873 ms | 326.336 us | tree |
| 768 | 84.687 ms | 71.002 ms | tree |
| 1024 | 157.023 ms | 159.296 ms | fold |

Regenerate the table with `lake exe hexhensel_bench compare
Hex.HenselBench.runPolyProductFoldChecksum
Hex.HenselBench.runPolyProductTreeChecksum --param-floor 4 --param-ceiling
1024 --param-schedule doubling --cache-mode warm --outer-trials 3
--signal-floor-multiplier 1`.  The public `Array.polyProduct` remains the
left-fold specification; a `@[csimp]` theorem proves the compiled dispatcher
extensionally equal to it for every crossover-table choice.

## Verification

Changes must pass:

- the root build and trust-surface check;
- linear, quadratic, and multifactor conformance fixtures;
- the external algebra-system oracle;
- word-sized and arbitrary-precision cross-checks;
- benchmark verification on lift exponents large enough to exercise
  repeated doubling.

Benchmarks report the exact source revision, toolchain, machine,
inputs, and lift exponent. Linear and quadratic lifting are recorded
as distinct operations.
