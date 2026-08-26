# hex-berlekamp-zassenhaus-mathlib

`hex-berlekamp-zassenhaus-mathlib` proves the mathematical
correctness of executable integer polynomial factorization. It
depends on `hex-berlekamp-zassenhaus`, `hex-poly-z-mathlib`,
`hex-hensel-mathlib`, and `hex-lll-mathlib`.

The ordinary umbrella exposes factorization soundness, the
correspondence with `Polynomial ℤ`, and the factor tactics.
`HexBerlekampZassenhausMathlib.All` exposes the complete proof
development.

## Polynomial correspondence

`HexPolyZMathlib.toPolynomial` identifies a dense `Hex.ZPoly` with a
Mathlib polynomial over the integers. It preserves coefficients,
addition, multiplication, degree, content, primitive parts, and
divisibility.

The public irreducibility equivalences are:

```lean
theorem Hex.ZPoly.Irreducible_iff_polynomialIrreducible (f : Hex.ZPoly) :
  Hex.ZPoly.Irreducible f ↔
    Irreducible (HexPolyZMathlib.toPolynomial f)

theorem Hex.ZPoly.isIrreducible_iff (f : Hex.ZPoly) :
  Hex.ZPoly.isIrreducible f = true ↔ Hex.ZPoly.Irreducible f
```

The second theorem supplies the decidable instance for concrete
dense integer polynomials.

## Modular factorization

`ModPFactorization f data` is the semantic contract for selected
prime data. It records:

- primality and admissibility of the modulus;
- equality of the cached polynomial with the reduction of `f`;
- monicity, distinctness, coprimality, irreducibility, and positive
  degree of the modular factors;
- equality of their product with the monic modular image.

`DirectPrimeFacts` combines this contract with the Berlekamp
certificate form and the small-prime bound used in the resultant
estimate.

## Hensel correspondence

`DirectLiftFacts` interprets the executable direct-coordinate Hensel
lift. The proof identifies lifted-factor indices with modular-factor
indices and transports selected products through reduction.

An irreducible integer divisor has a unique modular support.
`DirectSupportPartition` strengthens this statement to the recursive
factorization state: the remaining supports cover the remaining
indices, nonassociated factors have disjoint supports, and associated
factors have the same support.

`DirectFactorCertificate` packages one normalized irreducible factor,
its cofactor, its modular support, and the scaled congruence needed by
the logarithmic-derivative proof.

## Classical completeness

The classical proof follows the executable head-forced subset
iterator. It establishes:

- correctness of every accepted exact division;
- completeness of each fully enumerated cardinality level;
- identification of the first accepted subset with the irreducible
  support containing the distinguished index;
- preservation of the support partition after removing a factor;
- complete irreducibility of a successful returned factor list.

A typed resource decline makes no mathematical claim.

## Lattice completeness

For each local factor `g`, the combined logarithmic derivative (CLD)
is `f g' / g` modulo the Hensel modulus. Additivity turns products of
local factors into sums of CLD coefficient vectors.

The Belabas-Hoeij-Klüners-Steel (BHKS) lattice appends scaled CLD
coefficients to factor-indicator coordinates. Its exact LLL reduction
is cut by Gram-Schmidt length and projected back to the indicator
coordinates.

`SupportShortVectorData` describes a short lattice vector whose first
coordinates are a genuine support indicator.
`CutProjectionHypotheses` states that every genuine indicator lies in
the projected span. The resultant argument proves the reverse
containment: every retained projected row is constant on genuine
supports.

`DirectAdequacy` collects the precision, coefficient recovery,
leading-coefficient invertibility, Hensel lift, and support partition
needed by both arguments. `LatticeTotality` proves that the public
precision returns either recovered factors or a conclusive
irreducibility result whenever direct prime selection succeeds.

## Final factorization theorems

For every dense integer polynomial:

```lean
theorem factorize_product (f : Hex.ZPoly) :
  Hex.Factorization.product (Hex.ZPoly.factorize f) = f
```

For a nonzero input, `factorize_normalized` states that:

- the scalar is the signed content;
- each polynomial factor is primitive and irreducible;
- every leading coefficient and multiplicity is positive;
- distinct entries are not associates;
- the recorded product is the input.

`factorize_unique` shows that two normalized factorizations of the
same input have the same scalar and the same factors with
multiplicities.

The headline product, irreducibility, normalization, uniqueness, and
lattice-totality theorems use only the accepted Lean and Mathlib
foundations reported by the trust-surface check.

## Quadratic norm correspondence

For a commutative ring `K` and `r : K` with `r² = d`, `map_quadNorm`
identifies the executable quadratic norm with the honest polynomial
statement:

```lean
theorem map_quadNorm (g : Hex.ZPoly) (d : ℤ) (r : K) (hr : r ^ 2 = (d : K)) :
  (toPolynomial (Hex.quadNorm d g)).map (algebraMap ℤ K)
    = ((toPolynomial g).map (algebraMap ℤ K)).comp (X - C r)
      * ((toPolynomial g).map (algebraMap ℤ K)).comp (X + C r)
```

`map_iteratedNorm` iterates it: given square roots of every radicand,
the executable `iteratedNorm` maps to `∏_ε (X - c - ∑ᵢ εᵢ rᵢ)` over the
`2ⁿ` sign patterns, which is the polynomial the multiquadratic tower
theorem is about.

`Hex.SquareClass.Independent` says no nonempty sublist of the radicands
has a square product in `ℚ`, and
`independentSquareClasses_iff` shows the executable check
decides it. `associated_toPolynomial_of_check` carries a successful
certificate check to an `Associated` in `Polynomial ℤ`, so the input and
the iterated norm are irreducible together.

The tower theorem is `Hex.SquareClass.irreducible_int_of_map_eq_signPoly`:
a monic integer polynomial whose complex image is the sign-pattern
product of independent square classes is irreducible, because it is the
minimal polynomial of `c + ∑ᵢ √dᵢ`. It writes the product as a
`Finset.prod` over `Fin n → Bool`, which is what lets an automorphism act
by a reindexing equivalence; `map_iteratedNorm` writes it as a
`List.prod` over a fold-built list, which is what the iterated norm
computes. `signPatternPoly_ofFn` proves the two encodings are the same
polynomial, by induction on the number of radicands, splitting the last
sign off with `Fin.snocEquiv` on one side and the last fold step on the
other.

Composing those gives `irreducible_of_check`: a successful
`QuadraticNormCertificate.check` makes its input irreducible in
`Polynomial ℤ`, with no hypothesis on the input, and
`irreducible_of_quadraticNormCertified` says the same of the production
gate. That is what discharges the certificate arm of
`factorClassicalFactors_factor_irreducible`, so a certified singleton is
proved irreducible on the same footing as every other returned factor.

## Factor tactics

The `Polynomial ℤ` tactic support parses a closed polynomial
expression to a dense polynomial while proving the conversion
equality. Compiled factorization searches for:

- small-prime irreducibility witnesses;
- multi-prime degree-obstruction certificates;
- factor covers with one certificate per distinct factor.

The emitted term contains reified data, coefficientwise product
checks, certificate checks, and conversion theorems. The compiled
factorizer itself is not in the emitted proof.

The stronger `irreducibility!` and `factor_poly!` forms may use kernel
evaluation of the decidable factorization theorem on small inputs.
They require all executable definitions to be visible and cannot
evaluate native LLL code.

## Conformance

The library owns an executable runtime: the `factor_poly` /
`irreducibility` elaborators (with their `factor_poly!` /
`irreducibility!` kernel-decide fallbacks) and the reified certificate
checks their emitted terms replay. It is therefore not a
correspondence-only bridge:
`conformance/HexBerlekampZassenhausMathlib/Conformance.lean` is the
`core` conformance profile, built by the `HexConformance` library on
every CI run. It exercises the tactic entry points on committed
`Polynomial ℤ` and `Hex.ZPoly` fixtures across the certificate languages
(single-prime witness, Eisenstein handover, multi-prime degree
obstruction, kernel fallback), pins hand-derived factor lists and factor
counts, checks the decline diagnostics on reducible, zero, unit, and
over-budget inputs, and `#print axioms`-checks the emitted proofs. There
is no external oracle for the tactic surface (mode `always`): every
accepted invocation is kernel-certified, and the compiled factorizer the
tactics run as untrusted search is oracle-checked against python-flint
in the computational sibling's profile
(`conformance/HexBerlekampZassenhaus/`).

## Phase-4 proof evidence

`factor_poly` and `irreducibility` on `Polynomial ℤ` / `Hex.ZPoly` are
elaboration/proof surfaces, not LeanBench executables. Build-only modules
below `bench/HexBerlekampZassenhausMathlib/ProofProbe/` measure
`factor_poly` on products of distinct irreducible quadratics `X² + c`
over `ℤ` at degrees 4, 8, and 12, `irreducibility` on the Eisenstein
binomials `Xⁿ − 2` at degrees 4, 8, and 16, and the kernel-decide
fallback `irreducibility!` on the certificate-declined Swinnerton-Dyer
minimal polynomials at degrees 4 and 8. Each case is adjacent to the
same import-only baseline (whose import block carries the `import all`
executable closure the emitted certificate checks and kernel replays
need, identically in every probe), and degree 8 also has a direct
multiplicity-attribution pair (four distinct quadratics against the
fourth power of one quadratic: same degree and factor count with
multiplicity, all multiplicity). Baseline and kernel-8 same-module
controls are first in manifest `config.order`; execution order rotates
by round. Every probe carries the same large `import all` executable
closure, so the marginal elaboration cost must be substantial before a
module counts as a distinct build magnitude: the degree-16 binomial
reaches only `1.37x` the baseline, under the `2.0x` the shared harness
requires of its two controls, while the degree-8 kernel replay reaches
`2.48x` and is also the only control that brackets the most expensive
substantive arm. The external runner uses six balanced rounds, exact
generated-artifact invalidation, ordinary kernel checking, exact axiom
validation, and complete source provenance.
`HexBerlekampZassenhausMathlibProofProbe` supplies the reduced CI
coverage; `HexBerlekampZassenhausMathlibProofProbeScientific` owns the
larger release arms and remains outside routine CI.

On the named shared release machine a canonical invocation is:

```bash
taskset -c 22 python3 scripts/bench/bz_mathlib_sweep.py --samples 6 \
  --timeout 300 --warm-timeout 900 \
  --shared-host --expected-host chungus2 --cpu 22 \
  --max-core-interference-ratio 0.005 \
  --max-pair-retries 32 \
  --preflight-timeout-seconds 1800
```

The release run preregisters its selected logical CPU and aggregate
interference ratio on the command line; the artifact and headline report
record those exact values. They govern that run rather than the
illustrative CPU number above.

These arms run 6.65 s to 16.60 s, roughly `3x` the sibling
`HexBerlekampMathlib` suite's, so `ratio x wall` exceeds the `0.030 s`
three-tick quantization floor throughout and the ratio, not the floor, is
the binding admission gate. Each arm is correspondingly longer exposed to a
stray scheduler tick on the pinned core or its SMT sibling, so on a busy
shared host the run rejects more pair attempts and can exhaust the default
eight-retry budget on the longest arms. The preregistered response is the
`32`-retry bound this suite's manifest declares, which buys more clean-pair
opportunities at an unchanged admission threshold. Raising the interference
ratio instead would admit dirtier arms and is not the lever to reach for.

The runner enforces the designated-shared-host contract in
`SPEC/benchmarking.md`, including bounded retries of complete rejected
pairs after a bounded quiet-core preflight and a single aggregate
pinned-core/SMT interference ceiling; `--allow-busy` remains
diagnostic-only. Executable factorization arithmetic belongs to the
existing Mathlib-free `HexBerlekampZassenhaus` benchmark. The bridge
declarations have no separable compiled runtime kernel. For the
proof-emitting elaborators there is
`no-comparable-surface-in-named-comparator`: no external tool emits and
kernel-checks the same Lean proof term.

The headline report is
[`reports/hex-berlekamp-zassenhaus-mathlib-performance.md`](../../reports/hex-berlekamp-zassenhaus-mathlib-performance.md);
it cites the committed raw sweep artifact under `reports/bench-results/`
and records the release run's preregistered CPU and interference ratio.

## Verification

Changes must pass:

- the root build and trust-surface check;
- the advertised root-name compile checks;
- `#print axioms` checks for the headline theorems;
- factor-tactic regression modules;
- the integer-factorization conformance and external comparisons;
- the reduced proof-probe build
  (`HexBerlekampZassenhausMathlibProofProbe`) and the sweep manifest
  self-test (`python3 -m unittest scripts/bench/test_bz_mathlib_sweep.py`),
  both of which run on every CI job;
- the release manifest and dependency checks.
