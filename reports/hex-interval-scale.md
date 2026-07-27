# Hex interval structural scaling experiment

## Question

The centered-instantiation vertical established one complete proof-facing
certificate with nine program nodes, ten facts, and 74 charged indexed list
lookups. This experiment asks how that transparent reference checker behaves
when certificate dimensions and reference distance grow independently.

The theorem, source interval, target interval, endpoint arithmetic, centered
recipe, equality edge, and one-generation witness remain fixed. Only untrusted
structural payload changes. This isolates storage and validation behavior from
endpoint-backend arithmetic. It does not implement the general propagation
network, duplicate proposal registry, or multi-generation instantiation
recurrence, and it deliberately does not mix Core `Rat` cost into the
structural comparison.

## Workloads and controls

[`Scale.lean`](../HexInterval/Experiment/Scale.lean) defines four transparent,
Mathlib-free workload families over the centered checker.

| Family | Variable | Fixed dimensions | Exact indexed-lookup work |
| --- | --- | --- | ---: |
| `dead-nodes` | total nodes `n = 9..2000` | ten facts | `74` |
| `adjacent` | odd tail `n = 1..491` | nine nodes, `9+n` facts | `71 + 3n` |
| `far` | tail `n = 1..491` | nine nodes, `9+n` facts | `71 + n(n+5)/2` |
| `source-pad` | irrelevant tail `n = 0..490` | nine nodes, `10+n` facts | `74+n` |

The adjacent chain always refers to the immediately preceding fact. The far
chain has the same number of facts and equality edges but repeatedly refers to
fixed fact eight, so reverse traversal grows on every step. The source-padding
chain appends valid facts after the selected result; they are irrelevant to the
proof slice but still cross whole-table validation. Dead nodes enlarge the
whole-program scan without changing any fact reference.

Every workload carries a closed-form budget. Replay independently recomputes
both the scalar cost and a five-component decomposition into program, source,
edge, prior-fact, and result lookups. This counter charges fact/result lookup
distance, but it does not yet charge the equality-recipe checker's separate
program-list lookups. The current recipe performs nine lookups for the selected
center and nine per equality edge, so the reference implementation bounds
their constructor work by `9 * (maxEdges + 1) * maxNodes`; a production checker
must charge them or replace them with validated random access. Conformance
checks exact acceptance, one-step-short rejection, dimensions, and component
counts at the largest committed points.

[`IntervalScaleSpike.lean`](../bench/HexBench/IntervalScaleSpike.lean) measures
five compiled modes:

- `build` constructs the exact requested workload behind a non-inlined generic
  boundary;
- `accept` checks it at the exact lookup budget on even loop iterations and
  with one harmless spare lookup step on odd iterations;
- `below` checks it one lookup step short;
- `bad-tail` preserves lookup shape but corrupts only the last fact's range;
- `early` crosses the relevant structural cap by one constructor.

All list-derived structural limits are computed once, outside the timed loops;
the parity variants inside a loop are constant-time record updates. Both parity
outcomes are asserted before timing. For fact-table `early` cases, the driver
appends one valid irrelevant source fact and caps the table at the original
length. The original selected result
therefore remains in range, and rejection occurs only when `lengthWithin`
encounters the extra constructor. This avoids accidentally measuring the
constant-time result-index guard.

The committed record is
[`hex-interval-scale.json`](bench-results/hex-interval-scale.json). The harness
independently calibrates every mode to a 250 ms inner timing target, takes five
samples in a deterministic balanced coprime-stride order, and runs one case per
process. It verifies exact dimensions, all five lookup counters, stable
checksums, measured repeat counts, the executable hash, all input hashes, and
the complete expected probe output. No calibration reached its round limit.

The two proof-facing probes are import-matched pairs. The ordinary replay arm
checks the largest workload in every family by `decide +kernel`. The forced
`Lean.Kernel.whnf` arm times acceptance of all 21 ladder points after reducing
each workload builder to its outer constructor. Exact artifacts are removed
before every fresh build, pair order alternates, and axiom reports are required
for theorem modules. The harness invokes Lean only through Lake and never uses
`native_decide`.

Reproduce the record with:

```sh
python3 scripts/bench/interval_scale_sweep.py --samples 5 --target-ms 250 \
  --max-calibration-rounds 12
```

## Compiled results

The table reports median microseconds per call at the first and largest point
of each family.

| Family | Dimension | Build | Accept | One step short | Bad tail | Early cap |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| dead nodes | 9 → 2000 nodes | 0.101 → 27.617 | 4.780 → 12.572 | 4.693 → 12.390 | 4.764 → 12.385 | 0.022 → 1.871 |
| adjacent | 10 → 500 facts | 0.124 → 12.757 | 4.787 → 49.327 | 4.647 → 48.914 | 4.725 → 49.013 | 0.032 → 0.480 |
| far | 10 → 500 facts | 0.106 → 3.993 | 4.767 → 163.124 | 4.701 → 162.496 | 4.709 → 162.593 | 0.032 → 0.479 |
| source pad | 10 → 500 facts | 0.111 → 3.917 | 4.752 → 42.731 | 4.682 → 42.287 | 4.789 → 42.530 | 0.033 → 0.480 |

Compiled samples were stable enough for descriptive fits: median coefficient
of variation was 1.92% for construction and 0.67–1.26% for the four checker
modes. One tiny source-padding `below` point was a 21.09% outlier; every other
compiled point was at most 7.44%. Over the committed ladders, construction fit
13.82 ns per dead node, 25.89 ns per adjacent fact, 7.91 ns per far fact, and
7.75 ns per source fact, all with `R² ≥ 0.9997`. With limit construction no
longer timed, early cap rejection fit 0.92–0.93 ns per scanned node or fact
with `R² ≥ 0.9993`.

These fits describe this implementation and ladder; they are not asymptotic
theorems. In particular, adjacent construction does extra alternating-tail
work that the repeated far and source tails do not.

### Reference shape matters

At 500 accepted facts, the exact decomposition is:

| Workload | Program | Source | Edge | Prior fact | Result | Total | Median accept |
| --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| adjacent | 44 | 1 | 491 | 508 | 500 | 1,544 | 49.327 µs |
| far | 44 | 1 | 491 | 120,803 | 500 | 121,839 | 163.124 µs |
| source pad | 44 | 491 | 1 | 18 | 10 | 564 | 42.731 µs |

The far and adjacent certificates have identical node, fact, edge, and result
counts. Far replay is 3.31 times slower because its original-order list
references traverse much farther. Its charged work is 78.9 times larger; that
ratio does not translate directly to wall time because endpoint checks and
other fixed fact work dominate short references. A linear fit of far replay
against charged lookup constructors is 1.28 ns per step with `R² = 0.9985`
over this ladder.

The three 501-fact early controls all take about 0.48 µs, because they fail in
the structural scan before derivation lookup. Construction also goes the other
way: far and source tails cost about 4 µs while the alternating adjacent tail
costs 12.8 µs. These builders reuse closed fact terms differently, so their
construction costs are not a retained-size comparison. Even without that
confounder, neither fact cardinality nor construction time can stand in for
full replay work.

### Late failures really are late

At each largest point, one-step-short and bad-tail replay are within about 1.5%
of exact acceptance. The one-step-short budget reaches the final charged
lookup, while the malformed range is in the final fact. The controls therefore
exercise the intended full-validation surface. Early structural failures are
much cheaper: 14.9% of acceptance for 2,000 dead nodes and between 0.3% and
1.1% for the 500-fact families.

## Ordinary kernel results

Forced kernel reduction of each accepted point had these median endpoints:

| Family | First point | Largest point |
| --- | ---: | ---: |
| dead nodes | 59.4 ms | 734.7 ms |
| adjacent | 26.8 ms | 405.3 ms |
| far | 25.3 ms | 298.6 ms |
| source pad | 25.0 ms | 92.3 ms |

All 21 decisions reduced to `true`. Their median times sum to 2.291 s. These
samples are materially noisier than compiled replay: the median per-case
coefficient of variation is 5.9%, and a small cold case reaches 39.9%. The fixed
within-module case order is also a confounder.

Kernel behavior is not a scaled copy of compiled behavior. The largest far
case has 78.9 times more charged reference constructors than adjacent but
reduces faster. The timed term still constructs the certificate, and the far
and adjacent builders reuse closed terms differently; this experiment therefore
cannot attribute the inversion to lookup reduction itself. Kernel normalization
also sees different expression sharing and reduction structure from the
compiled runtime, and the experiment reduces only the workload's outer
constructor before timing. A normalized-certificate arm is required before
drawing a kernel lookup-cost conclusion.

The ordinary maximum-boundary theorem took median fresh-module wall time
4.225 s against 1.125 s for its import-matched fixed theorem. The median paired
added wall time is 3.120 s, and the median ratio of medians is 3.76. Median peak
RSS is 799.8 versus 796.9 MiB; the median paired delta is only 1.8 MiB, so process
startup dominates that coarse measure.

The forced-WHNF command module took median wall time 4.115 s against 1.520 s,
with a median paired added time of 2.398 s and a ratio of medians of 2.71.
Median peak RSS is 888.3 versus 795.5 MiB, with a median paired delta of
89.9 MiB.

The baseline and checked theorem axiom sets are both exactly
`[propext, Quot.sound]`. There is no `sorryAx`, execution-trust axiom, or use of
`native_decide`. The WHNF modules execute commands and declare no measured
theorem, so their axiom fields are deliberately `null`, not an asserted empty
set.

### Artifacts

| Probe | Public `.olean` | Private `.olean` | Server `.olean` | Object |
| --- | ---: | ---: | ---: | ---: |
| replay baseline | 3,984 | 888 | 1,176 | 3,992 |
| replay checked | 3,984 | 16,256 | 2,240 | 13,232 |
| WHNF baseline | 3,920 | 1,688 | 1,208 | 4,560 |
| WHNF checked | 89,320 | 231,648 | 3,280 | 77,480 |

The replay pair exports the same small theorem shape, so its public `.olean`
size is identical while proof payload accumulates in private and generated
artifacts. The command module retains all 21 generated terms and is much
larger. The JSON record includes source, `.ilean`, generated C, byte sizes, and
SHA-256 hashes as well.

## Decisions

1. The original-order `List` remains a transparent proof-facing reference
   implementation only. Production experiments must compare array, arena, or
   another exact-index representation; they must not accept position-sensitive
   linear lookup without charging every traversal.
2. Resource accounting keeps distinct hard caps for nodes, facts, sources,
   edges, retained bytes, and representation-level lookup work. Fact count is
   not a safe proxy for replay work. A production checker recomputes every cost
   from validated references rather than trusting certificate claims.
   The next structural experiment varies the equality-edge table independently;
   until every edge-to-program lookup is charged or random-access, the current
   `9 * (maxEdges + 1) * maxNodes` fallback is a reference-checker bound, not
   the desired production accounting model.
3. A bounded scan over a list is still linear. If adversarial preflight must be
   independent of submitted length, the selected representation needs cached
   trusted dimensions or a bounded random-access container. The checker must
   document where that trust originates.
4. Certificate construction, compiled replay, and kernel/elaboration replay
   remain separate benchmark phases. One cannot be substituted for another.
5. Late-failure and early-failure controls stay in the suite. A faster reject
   is meaningful only when the harness proves which validation stage rejected
   it.
6. Ordinary kernel replay is feasible at these maximum points but already adds
   seconds and private artifact cost. The next storage experiment includes a
   chunked/compositional replay arm instead of assuming one monolithic decision
   will scale indefinitely.
7. Source-level prohibition of `native_decide`, guarded axiom reports for
   theorem probes, and `null` rather than fabricated axiom claims for command
   probes remain fixed evidence requirements.

## Next vertical: canonical rational endpoints

The immediate endpoint experiment reuses these structural shapes through an
endpoint-erased skeleton. It first proves that Dyadic and rational certificates
erase to exactly the same operation tags, operand and derivation references,
instantiation provenance, generations, equality edges, source/target slots,
and structural budgets. Literal slots remain, but numeric endpoint values do
not enter the structural comparison.

Planning then runs as compiled Mathlib-free Lean over Core `Rat`. Freezing
interns canonical numerator/positive-denominator pairs into a shared raw table.
Transparent replay bounds and decodes the whole table, rejects rather than
normalizes zero denominators or noncoprime entries, preflights every gcd,
shift, and cross-product, and checks integer identities through Core rational
characterization lemmas. The measured phases are skeleton loading, Core `Rat`
planning, interning, serialization, bounded decoding, whole-table validation,
compiled replay, and ordinary-kernel replay.

The first controls are the dyadic-valued centered trace, a genuinely
non-dyadic `x ∈ [1/3, 2/3]` trace, and odd-denominator heights
`h ∈ {8, 32, 128, 512, 2048}` using `d = 2^h - 1`. Structural replication
reuses this experiment's ladders without changing endpoint values. Required
malformed cases include zero and noncanonical denominators, inflated
equivalent fractions, unused oversized entries, wrong arithmetic and
projection results, skeleton mismatch, and every one-step-over resource
boundary.

This vertical uses no Mathlib and no `norm_num`. A later Mathlib companion may
use `norm_num` only to connect surface numeral or cast syntax to a caller-bound
rational leaf; it is not part of planning, projection, decoding, validation,
arithmetic replay, or soundness. No layer uses `native_decide`.

Cancellation-aware cross-products versus exposed normalization, table layout
and uniqueness, wire encoding, projection witnesses, kernel chunk size, and
rational working facts versus immediate dyadic projection remain empirical
questions.

## Limits of the evidence

This experiment does not measure a propagation scheduler, expression
instantiation registry, proposal deduplication, several generations, branch
storage, tactic elaboration, Mathlib semantic proof construction, or endpoint
backend alternatives. Five samples on one host do not set regression
thresholds or prove asymptotic bounds. Whole-process RSS cannot recover
per-check allocation, and the kernel ladder does not isolate workload
normalization from certificate checking. The construction measurements also
reuse closed fact terms and are not retained heap-size proxies. Those are
requirements for the next comparisons, not conclusions to infer from this
record.
