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
edge, prior-fact, and result lookups. Conformance checks exact acceptance,
one-step-short rejection, dimensions, and component counts at the largest
committed points.

[`IntervalScaleSpike.lean`](../bench/HexBench/IntervalScaleSpike.lean) measures
five compiled modes:

- `build` constructs the exact requested workload behind a non-inlined generic
  boundary;
- `accept` checks it at the exact lookup budget;
- `below` checks it one lookup step short;
- `bad-tail` preserves lookup shape but corrupts only the last fact's range;
- `early` crosses the relevant structural cap by one constructor.

For fact-table `early` cases, the driver appends one valid irrelevant source
fact and caps the table at the original length. The original selected result
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
python3 scripts/bench/interval_scale_sweep.py --samples 5 --target-ms 250
```

## Compiled results

The table reports median microseconds per call at the first and largest point
of each family.

| Family | Dimension | Build | Accept | One step short | Bad tail | Early cap |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| dead nodes | 9 → 2000 nodes | 0.095 → 29.062 | 4.820 → 14.294 | 4.696 → 14.178 | 4.782 → 14.127 | 0.041 → 5.617 |
| adjacent | 10 → 500 facts | 0.120 → 14.155 | 4.842 → 51.373 | 4.695 → 51.284 | 4.832 → 50.673 | 0.049 → 1.413 |
| far | 10 → 500 facts | 0.107 → 4.265 | 4.794 → 164.169 | 4.665 → 165.177 | 4.792 → 163.465 | 0.049 → 1.409 |
| source pad | 10 → 500 facts | 0.110 → 3.905 | 4.812 → 44.648 | 4.706 → 44.699 | 4.754 → 44.818 | 0.050 → 1.419 |

Compiled samples were stable enough for descriptive fits: median coefficient
of variation was 1.27% for construction and below 0.81% for every checker
mode; the worst case was 3.91%. Over the committed ladders, construction fit
14.56 ns per dead node, 28.81 ns per adjacent fact, 8.47 ns per far fact, and
7.71 ns per source fact, all with `R² ≥ 0.9997`. Early cap rejection fit about
2.8 ns per scanned node or fact with `R² ≥ 0.9992`.

These fits describe this implementation and ladder; they are not asymptotic
theorems. In particular, adjacent construction does extra alternating-tail
work that the repeated far and source tails do not.

### Reference shape matters

At 500 accepted facts, the exact decomposition is:

| Workload | Program | Source | Edge | Prior fact | Result | Total | Median accept |
| --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| adjacent | 44 | 1 | 491 | 508 | 500 | 1,544 | 51.373 µs |
| far | 44 | 1 | 491 | 120,803 | 500 | 121,839 | 164.169 µs |
| source pad | 44 | 491 | 1 | 18 | 10 | 564 | 44.648 µs |

The far and adjacent certificates have identical node, fact, edge, and result
counts. Far replay is 3.20 times slower because its original-order list
references traverse much farther. Its charged work is 78.9 times larger; that
ratio does not translate directly to wall time because endpoint checks and
other fixed fact work dominate short references. A linear fit of far replay
against charged lookup constructors is 1.29 ns per step with `R² = 0.9987`
over this ladder.

The three 501-fact early controls all take about 1.41 µs, because they fail in
the structural scan before derivation lookup. Construction also goes the other
way: far and source tails cost about 4 µs while the alternating adjacent tail
costs 14.2 µs. Thus neither fact cardinality nor construction time can stand in
for full replay work.

### Late failures really are late

At each largest point, one-step-short and bad-tail replay are within about 1.4%
of exact acceptance. The one-step-short budget reaches the final charged
lookup, while the malformed range is in the final fact. The controls therefore
exercise the intended full-validation surface. Early structural failures are
much cheaper: 39% of acceptance for 2,000 dead nodes and between 0.9% and 3.2%
for the 500-fact families.

## Ordinary kernel results

Forced kernel reduction of each accepted point had these median endpoints:

| Family | First point | Largest point |
| --- | ---: | ---: |
| dead nodes | 32.7 ms | 638.0 ms |
| adjacent | 27.0 ms | 414.8 ms |
| far | 25.5 ms | 300.2 ms |
| source pad | 25.4 ms | 92.9 ms |

All 21 decisions reduced to `true`. Their median times sum to 2.174 s. These
samples are materially noisier than compiled replay: the median per-case
coefficient of variation is 7.6%, and a small cold case reaches 43%. The fixed
within-module case order is also a confounder.

Kernel behavior is not a scaled copy of compiled behavior. The largest far
case has 78.9 times more charged reference constructors than adjacent but
reduces faster. Kernel normalization sees different expression sharing and
reduction structure from the compiled runtime, and the experiment reduces
only the workload's outer constructor before timing. This result does not make
far list references desirable; it requires a separate kernel cost model and a
storage comparison in both execution modes.

The ordinary maximum-boundary theorem took median fresh-module wall time
4.022 s against 1.060 s for its import-matched fixed theorem. The median paired
added wall time is 3.038 s, and the median paired ratio is 3.91. Median peak RSS
is 800.1 versus 803.1 MiB; the median paired delta is only 4.2 MiB, so process
startup dominates that coarse measure.

The forced-WHNF command module took median wall time 3.593 s against 1.400 s,
with a median paired added time of 2.245 s and ratio 2.54. Median peak RSS is
797.5 versus 883.2 MiB, with a median paired delta of 84.0 MiB.

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
normalization from certificate checking. Those are requirements for the next
comparisons, not conclusions to infer from this record.
