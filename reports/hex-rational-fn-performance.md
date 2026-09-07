# HexRationalFn performance

## Scope and evidence status

The library is active through Phase 3. These fixed LeanBench registrations are
expected-hash anchors and informational crossover measurements, **not Phase-4
scaling evidence**. No asymptotic regression-detection mode is claimed for these
anchors. Under the ordered modes in [the benchmarking policy](../SPEC/benchmarking.md),
Phase 4 remains incomplete: family-specific degree/bit-cost models and profiles
must be established before a performance-coverage claim. A generic timeout is
not an operation-specific absolute budget.

All seven SPEC input families have executable anchors: normalization, addition,
multiplication, coefficient-height, queries, calculus, and certificate-replay.
The seven prepared cases vary residual degree (4, 12), common-factor degree
(0, 2, 4, 12), nonmonic scalar factors, and rational coefficient height
(1, 16, 64, 256 input bits). Addition includes equal and partially shared
denominators, coprime denominators, and total cancellation. Multiplication
includes a coprime-product control and complete cross-cancellation. Queries
include a last-coefficient mismatch and prepared poles. Calculus includes both
the derivative of a canonical fraction and its cube, exercising cancellation
in the quotient-rule normalization. Replay includes prepared rejected and valid
witnesses enlarged by a degree-32 polynomial; generation is timed separately.
All polynomial outputs are hashed in full.

Input and certificate preparation occurs in initialization outside measured calls.
Some family anchors intentionally combine operations (for example the height
anchor includes normalization and powering); their times are aggregate latency,
not isolated-kernel throughput. The `sizes` command checks full multiplication
plan agreement and reports raw/final lengths and coefficient bit lengths.
Prime-field plan agreement is also checked in computational conformance.
Polynomial-part division is a **structural-layer** comparison owned by
HexPolyFast. Certificate operations have
**no-comparable-surface-in-named-comparator**.

## Environment and reproducibility

Measured on an AMD EPYC 9455 (48 physical cores, 96 logical CPUs), Linux x86_64,
Lean 4.34.0-rc2, lean-bench 0.1.0. Each native result below is the median of three
measured child runs after warmup, with an inner-repeat floor of 10 ms.
This is the shared development host `chungus2`, not a controlled dedicated timing runner.
Hardware-dependent conclusions are confined to the measured families.

```sh
lake build hexrationalfn_bench
.lake/build/bin/hexrationalfn_bench sizes
.lake/build/bin/hexrationalfn_bench verify
.lake/build/bin/hexrationalfn_bench run --filter RationalFnBench --export-file /tmp/rationalfn-bench.json
```

The CI integration extends the existing build, bench-verify and oracle steps.
There is no scheduled timing workflow in this checkout to extend; no new workflow
or CI job is introduced.

## Multiplication-plan crossover

Dense rational inputs have coefficient lengths 16, 32, 64, 128 and small integer
coefficients. Results of every plan agree coefficient-for-coefficient. Latencies
include the common full-output hash.

| Length | Schoolbook (µs) | Karatsuba cutoff 8 (µs) |
| --- | ---: | ---: |
| 16 | 49.60 | 46.35 |
| 32 | 197.12 | 155.08 |
| 64 | 776.75 | 500.14 |
| 128 | 3114.20 | 1560.67 |

The first sampled recursive length, 16, already shows an advantage for cutoff 8.
Products at or below the cutoff use the schoolbook base case. The aggregate
cutoff search covers both smaller and larger cutoffs on the same four input pairs:

| Cutoff | Combined latency (µs) |
| --- | ---: |
| 1 | 3660.31 |
| 2 | 2882.60 |
| 4 | 2430.66 |
| 8 | 2300.53 |
| 16 | 2402.61 |
| 32 | 2785.88 |
| 64 | 3471.96 |

Schoolbook takes 4098.02 µs over those pairs. The lowest measured
median is at cutoff 8, bracketed by slower tested cutoffs 4 and 16, so the default
is 8. This does not assert an optimal cutoff for every coefficient field, height,
or degree, or locate an exact degree crossover between the sampled lengths.

## Cancellation versus multiply-then-normalize

Both routes receive identical canonical operands `a/(a+1)` and `(a+1)/a`,
where `a` is a dense monic polynomial. Both must return the complete canonical
pair `(1,1)`. Both routes use the default multiplication plan, and the naive
route uses the same default normalization as the library.

| Degree of a | Cross-cancel (µs) | Multiply then normalize (µs) | Naive intermediate degree |
| --- | ---: | ---: | ---: |
| 1 | 13.08 | 13.32 | 2 |
| 2 | 23.05 | 22.44 | 4 |
| 4 | 37.61 | 46.62 | 8 |
| 8 | 73.10 | 127.11 | 16 |
| 16 | 180.41 | 382.31 | 32 |

Degree 1 is approximately tied; degree 2 favors the naive route slightly.
The first sampled sustained advantage for cancellation is degree 4, with a
larger advantage at degrees 8 and 16. Cross-cancellation forms only constant
output products in this family, avoiding the displayed intermediate degrees.
This is the maximal-cancellation family, not a mixed workload or a per-rung
coprime control. No claim is made that cancellation wins on every small coprime input.

The combined multiplication anchor (including the no-cross-cancellation control)
takes 1838.33 µs versus 3088.43 µs
for multiply-then-normalize, with identical frozen full-result hashes.

## Family latency anchors

These rows execute all seven prepared cases; they are not per-single-fraction times.

| Anchor | Median (µs) |
| --- | ---: |
| Normalization | 1423.81 |
| Addition | 4540.03 |
| Height | 2299.59 |
| Queries | 38.86 |
| Calculus | 972018.65 |
| Generate | 1911.74 |
| Replay | 2455.09 |

The height multiplier is applied only to the raw numerator; the denominator's
scalar stays fixed at -2, so normalization does not cancel the height multiplier.
At input heights 16, 64 and 256, maximum canonical numerator widths are
18, 66 and 258 bits, and the corresponding cubed widths are 55, 199 and 775 bits.
Raw numerators reach 259 bits while polynomial shapes stay fixed. The `sizes`
command reports raw and final widths independently from degree; canonical product
widths are not a proxy for all temporary coefficient
growth inside Euclidean arithmetic. Profiling that growth remains Phase-4 work.

## Independent FLINT comparator

**FLINT fmpz_poly_q via a persistent C driver** is informational.
`scripts/bench/rationalfn_flint.c` calls the public `fmpz_poly_q_` routines for
canonicalisation, add/subtract/multiply/divide, inverse, powers, derivative,
equality and rational evaluation. The Python coordinator uses exact `Fraction`
conversion and compares complete canonical coefficient arrays, not hashes or
samples. `--rows` records both FLINT integer-pair and Hex rational-pair
representation lengths and maximum coefficient widths.

The driver stays alive across requests. Parsing, rational-to-integer conversion,
input canonicalisation for arithmetic, output conversion, and output comparison
are outside the measured operation. Normalization starts from a fresh raw copy
each repetition, with the copy outside timing. Total inverse/division at zero
are explicitly adapted to zero without calling FLINT's rejecting operations;
zero raw denominators and evaluation poles remain failures. Rejected raw
denominators have no measured time and are excluded from timing summaries.
These adapted cases
must not be mistaken for timings of a FLINT inverse/division call.

Example build (requires FLINT development headers and library):

```sh
cc -O2 -Wall -Wextra scripts/bench/rationalfn_flint.c -lflint -o /tmp/rationalfn-flint
python3 scripts/bench/rationalfn_flint.py /tmp/rationalfn-flint \
  conformance-fixtures/HexRationalFn/rationalfn.jsonl --repeats 100 --rows
```

The local comparator uses FLINT 3.6.0 and Clang 22.1.8. The committed QQ fixtures
agree in full. Tiny-fixture timings are close to clock/dispatch overhead and
are only a protocol check, not a competitive throughput claim against
the larger native anchors. A matched large-input throughput ladder is still
needed for Phase 4; representation conversion costs must remain excluded.

The build-only `HexRationalFnMathlib.Tests` checks a nontrivial literal
certificate through the headline theorem using kernel reduction, separately
from the native replay timing. Axiom audits list only `propext`,
`Classical.choice`, and `Quot.sound`.
