# Nested rational-function constants

The ordinary rational-function implementation constructs polynomial one as
`#[1]`, with its normalization supplied by the field law `1 ≠ 0`. Polynomial
embedding uses that direct denominator. One shares this polynomial between its
numerator and denominator; zero has an empty numerator and the direct denominator.
Natural casts and numerals zero and one reuse these instances. The compiler
replacements have ordinary kernel proofs of equality to the original stored
pairs, with no new axioms or admissions. The Mathlib field instance uses the same
cast and retains its proved equality with the computational field dictionary.

Let u(j) and z(j) count construction at extension depth j. The changed source
gives `u(j)=u(j−1)+Θ(1)` and `z(j)=u(j−1)+Θ(1)`, hence Θ(j). Destruction also
visits only the shared chain. The former branching recurrence has dominant
eigenvalue `2+√2`; its retained observations remain in the
[nested sign report](sign-det-nested-signs.md).

## Comparison protocol

The [runner](../scripts/bench/rationalfn_constants.py) declares six trial-major
rounds, adjacent before/after arms with alternating AB/BA order, a 100 ms inner
target and a 30-second child cap. It uses the pinned LeanBench child sampler
without changing field arithmetic. It leases one CPU, records host load,
retains every sample and checks clean source and executable hashes before and
after collection. Host activity does not remove samples or trigger retries.

| Operation | Extension depths | Timed work |
| --- | --- | --- |
| Zero and one | 2, 6, 10 | Ordinary numeral construction and destruction, plus fixed-size stored-pair length consumption. |
| Arithmetic consumer | 1, 2, 3 | Multiply the prepared fraction `(X+1)/(X−1)` by one, add zero, and hash its complete recursive coefficient arrays. |
| Scalar sign | 6, 9, 12 | Existing `Infinitesimal.sign` of the newest positive infinitesimal. |

Dictionary construction, operand preparation and complete literal encoding are
outside timing. Full constructor outputs and arithmetic outputs are separately
checked against independent expected coefficient arrays, including denominators;
shallow constructor lengths alone are not the correctness oracle. The arithmetic
comparison records representative elapsed times rather than asserting a scaling
law: internal coefficient work and recursive hashing vary with depth.

The constructor registration models Θ(d) for the changed source. The downstream
scalar sign registration separately models Θ(2^d), with its remaining constructor
and structural comparison costs accounted for in the
[derivation](sign-det-nested-signs.md). Paired ratios do not establish either
scaling law by themselves.

```sh
python3 scripts/bench/rationalfn_constants.py \
  --before /path/to/baseline-worktree --after /path/to/repaired-worktree \
  --output /path/to/new-captures
```

Both executables must be built from committed source; the baseline includes the
identical new measurement module without the arithmetic repair. Historical
observations are retained unchanged. HexOrderedFn's completed degree families
hold extension depth fixed at one, two or three, so their source bounds remain
valid; this repair changes constants on those families. No HexPoly or
HexOrderedFn implementation is changed.

## Retained results

All observations come from the shared `chungus2` host, Lean 4.35.0-rc3 and
lean-bench `8a37daf107` (the complete harness revision is recorded in each
metadata file). Absolute times describe this host. The
[archive index](data/rationalfn-constants/archive.json) binds each compressed
capture; captures retain source/executable hashes, raw child stdout/stderr,
complete inputs, host context, samples and summaries. CI revalidates archive
hashes, schedules, independent outputs and paired summaries.

The [constructor capture](data/rationalfn-constants/constructors.tar.gz) has
36 observations. Its baseline is `6dd9833f92` and repaired source is
`e4beeb344c`; the measurement module is identical in both. The runtime cast
argument passes through the timed closure, and the compiled closure constructs
both values before passing them to the opaque length consumer.

| Depth | Before median | After median | Median paired speedup |
| --- | ---: | ---: | ---: |
| 2 | 0.518 μs | 0.109 μs | 4.72× |
| 6 | 70.209 μs | 0.246 μs | 284× |
| 10 | 9.610 ms | 0.411 μs | 23,444× |

The [consumer capture](data/rationalfn-constants/comparison.tar.gz) has 108
observations, baseline `9efdf05f3d` and repaired source `e10ef670ea`. Its first
36 observations consume constants constructed during preparation: the compiler
moved construction out of the unit closure. Those rows measure prepared-value
consumption, **not constructor cost**, and establish no constructor speedup.
They remain retained. The separate runtime-argument constructor capture above
repairs that measurement; it does not replace or discard the earlier rows.
The arithmetic and sign rows time their stated operations.

| Operation / depth | Before median | After median | Median paired speedup |
| --- | ---: | ---: | ---: |
| Arithmetic / 1 | 9.977 μs | 9.605 μs | 1.04× |
| Arithmetic / 2 | 35.370 μs | 31.132 μs | 1.13× |
| Arithmetic / 3 | 106.411 μs | 74.511 μs | 1.43× |
| Sign / 6 | 80.121 μs | 7.443 μs | 10.76× |
| Sign / 9 | 3.237 ms | 63.142 μs | 51.23× |
| Sign / 12 | 130.150 ms | 0.513 ms | 253.59× |

The first short scalar-sign validation, at depths 6,9,12, also retains all
18 observations in [its capture](data/rationalfn-constants/sign-short.tar.gz).
The harness returned `consistent_with_declared_complexity`, with no fitted
slope because its post-warmup depth range was too narrow. That result is not a
fitted scaling confirmation. The current four-depth schedule includes depth
four before the warmup exclusion; its post-warmup depths 6,9,12 span a factor
two. No arithmetic implementation changed when extending that validation range.
