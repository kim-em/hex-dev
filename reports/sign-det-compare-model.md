# Reduced and full sign-table construction

`runSmallReduced` and `runSmallFull` construct sign tables for the same prepared
root domain P=X²−1 on the whole line and s copies of X, with s=1,…,5. Both
use direct moment products. The timed bodies include query construction,
matrix solving and checked table production. The reduced arm replays its
recursive support tree; the full arm checks its one full-system node. Untimed
preparation checks both tables against exactly two sign words, all negative
and all positive, each with count one. `inspect-small` separately verifies
literal dimensions and counts, not just matching result hashes.

Both registrations currently use mode 1, a two-sided parametric claim. The
reduced arm declares Θ(s log s) on this two-root family: every balanced
node has a bounded matrix, and its query and sign slots are scanned in Θ(k)
work for a node containing k input polynomials. The full arm declares Θ(27^s)
scalar work from cubic worst-case rational Gauss-Jordan and dense
inverse-identity replay on the 3^s square moment matrix. This is a finite-input
wall-time model, not a bit-complexity claim for
arbitrary s. Rational row reduction may instead dominate; `inspect-full`
records the actual elimination updates and matrix dimensions to assess that
possibility. The inventory below shows fewer row additions than dense
Gauss-Jordan, while the two dense inverse checks still execute cubic loops.
This finite schedule cannot determine which source-level term controls the
wall time at larger inputs. A model mismatch remains an inconclusive result,
not a passing upper bound.

`paired-small` uses the shared LeanBench sampler and summary for each arm. Six
fixed trial-major rounds keep the arms adjacent for every s and alternate
AB/BA order. Each completed arm is flushed before the next child. The Python
wrapper leases one CPU automatically, records host load as context, checks
that every child ran at the clean measured revision, validates the complete
sample stream and retains all verdicts. Each arm targets one second of inner
work and uses the normal tenfold spawn-signal floor; every recorded batch
cleared that floor. No completed sample is discarded or automatically rerun
after an inconclusive result. Pairwise signed differences and ratios are
computed from adjacent samples before taking their medians.

This fixed-degree, fixed-coefficient family has support two. It does not cover
maximal support, growing degree or coefficient bits, nested field depth,
modulo-product comparisons, or descriptor operations. Child RSS includes
untimed preparation; allocation bytes and peak intermediate bits need separate
measurements. The larger sparse-family report covers s=64,…,2048 and is not
replaced by this reduced/full comparison.

## Recorded observations

Clean source `50af811030d4753fade03d854fcdb5a8b481d641` completed all 30 adjacent
pairs (60 arm samples) on shared-host CPU 58 with Lean 4.34.1. Every result
matched the expected complete two-root table. The child environment reported
the same Git revision and `git_dirty = false`; source and executable hashes
matched before and after measurement. No completed sample was discarded. The
Python runner exits nonzero because the full arm's model verdict is
inconclusive; its metadata state is `complete`, and all samples, summaries and
checks are retained.

The reduced arm reports **consistent with declared complexity** on this
schedule: its `s * (Nat.log2 s + 1)` normalized constants range from 52,216
to 73,973 among verdict-eligible inputs. The full arm reports **inconclusive**
for `27^s`: its eligible normalized constants range from 111 to 767. The
registered harness trims the first 20% of input sizes from the verdict, so
s=1 is still measured and reported but excluded from both constant ranges.
Its untrimmed constants are 82,378 for the reduced arm and 3,045 for the full
arm. Including s=1 would make the reduced constant range 1.58, above the
harness's 1.5 narrow-range fallback threshold. The reported reduced verdict
thus depends on that stated warmup trim and noise-floor fallback. The shared
harness reported no slope and used its multiplicative-range fallback for both
arms. This short schedule cannot
distinguish Θ(s log s) from linear growth; the larger sparse-family report
supplies scaling evidence. The full arm's measured growth does not support the
declared `27^s` model here. A consistent finite-range verdict is not an
asymptotic proof, and the full model remains an open performance gate.

| Queries | Reduced median ms | Full median ms | Median paired full/reduced ratio | Pair ratio range |
| ---: | ---: | ---: | ---: | ---: |
| 1 | 0.082 | 0.082 | 0.999 | 0.991–1.006 |
| 2 | 0.260 | 0.559 | 2.147 | 2.134–2.176 |
| 3 | 0.444 | 6.229 | 14.048 | 13.842–14.130 |
| 4 | 0.627 | 93.234 | 148.983 | 146.081–150.474 |
| 5 | 0.826 | 1,592.721 | 1,927.957 | 1,889.043–1,955.451 |

Each ratio is the median of six actual adjacent ratios, not the ratio of arm
medians. Both arms include their own complete certificate check in the timed
body. The near-equality at one query is consistent with both solving and
checking the same three-column leaf system. At five queries the checked full
reference is much slower than checked support reduction on this fixed two-root
family. The child auto-tuned inner repetitions; the raw stream records their
per-call timings and batch durations.

The [raw stream](data/sign-det-compare/50af81103/samples.jsonl) retains every
arm sample and unmodified harness summary; the
[paired summary](data/sign-det-compare/50af81103/summary.json) retains every
signed difference and ratio. The
[metadata](data/sign-det-compare/50af81103/metadata.json) records commands,
host context, source and binary hashes, and reconstruction of the measured
source from the
[archived patch](data/sign-det-compare/50af81103/committed-source.patch).
The [small-input inventory](data/sign-det-compare/50af81103/inventory.log)
records literal dimensions and counts. The report itself is a result, not a
measured source file; the profile runner, both comparison scripts, all benchmark
source files and their library dependency closure are in the recorded source
hash set. The measured revision is a clean local commit after rebasing onto
merged #10436. Its metadata archives a patch against
`81450116cc9bf88089d4b341231019e29ee4f504` and verifies that applying
it reconstructs every measured source hash. A later validation-only change
pins the recorded harness verdict settings in the runner's acceptance checks;
the measured executable and archived data were not changed. The copied data
pass those stronger checks.

## Attribution of the full reference

A [timed-region profile](data/sign-det-compare/profile-50af81103/full-reference.summary.json)
of `runSmallFull 5` used the same executable SHA-256 as the paired comparison,
`4f7b45614d45ab966df26e8d31582690ef41060a8874dbc74f8cd32cd04fcf87`.
It ran from the same clean source revision, on automatically leased CPU 31,
with a five-second target and 999 Hz sampling. Its three timed regions total
4.787 seconds and retain 4,780 benchmark-thread samples. Timing calibration
residual was 0.528 ms, and confidence and both boundary-sensitivity checks
passed. The 35 raw profiling artifacts are retained on the shared host at
`/home/kim/.local/share/hex-bench/sign-det-full-50af81103`; the
[manifest](data/sign-det-compare/profile-50af81103/full-reference.manifest.json)
records their hashes, commands and tool revisions. Untimed preparation lies
outside the analyzed regions.

| Inclusive operation | Percentage of timed samples |
| --- | ---: |
| `solveSystem` | 93.47% |
| `Matrix.inverse?` | 87.97% |
| `Matrix.rowReduce` | 87.95% |
| `eliminateColumn` | 87.28% |
| `Matrix.rowAdd` | 87.15% |
| `System.check` | 6.59% |
| `momentMatrix` | 4.27% |
| `Matrix.mulImpl` | 3.93% |

These inclusive paths overlap and must not be summed. Self attribution is
34.96% GMP, 35.50% allocation routines, 20.63% Lean runtime, 2.30% own Lean
code and 6.61% other; unresolved leaf symbols account for 1.07%.
Allocation routine time is not an allocated-byte measurement. Rational row
reduction dominates the timed full reference, even with its certificate check
included.

## Full-matrix operation inventory

`hexsigndet_bench inspect-full` observes the same literal full moment matrices
for s=1,…,5. At each column it verifies that the current row has a nonzero
diagonal, counts nonzero entries in the other rows, then calls the existing
`Matrix.rowReduceLoop col 1` to execute that column. Pivot search therefore
chooses the current row. Scaling changes only that row; another row's column
entry remains unchanged until its own elimination. Each counted entry invokes
`Matrix.rowAdd` once on the echelon matrix and once on its transform, and each
invocation processes all 3^s entries of its destination row. The inventory
checks the final pivot list and identity echelon and compares the complete
transform with the actual `Matrix.inverse?` result.

| Queries | Eliminated rows | Rational row-add multiply/add pairs | Rational row-scale products | Integer inverse-check multiply/add pairs per `System.check` |
| ---: | ---: | ---: | ---: | ---: |
| 1 | 6 | 36 | 18 | 27 |
| 2 | 54 | 972 | 162 | 729 |
| 3 | 378 | 20,412 | 1,458 | 19,683 |
| 4 | 2,430 | 393,660 | 13,122 | 531,441 |
| 5 | 15,066 | 7,322,076 | 118,098 | 14,348,907 |

For these five inputs, the eliminated-row count equals `2(6^s−3^s)` and the
row-add scalar-pair count equals `4(18^s−9^s)`. This finite inventory does not
prove either formula for arbitrary s. Counts refer to source-level arithmetic
operations, not GMP instructions, allocation bytes or peak intermediate bits.
The inverse-check count follows its dense multiplication's three loop bounds;
it is separate from the rational row-add path observed at each pivot. The timed
full arm executes `System.check` twice, once during production and once during
replay, so the table counts one of those executions. The
[complete per-column counts](data/sign-det-compare/50af81103/inventory-full.jsonl)
come from the same clean revision and executable hash as the paired run; their
[metadata](data/sign-det-compare/50af81103/inventory-full.metadata.json)
records the output hash and verified finite count identities.

The profile and operation inventory explain why the full arm's normalized
`27^s` timing constant declines on this schedule: rational elimination is
costly despite its lower source-level operation count. The two dense checks
still contribute `27^s` arithmetic, so the inventory alone does not refute
that eventual asymptotic term. Neither these five inputs nor the profile
establish a replacement wall-time model; a justified wider schedule or an
independently derived family-specific model needs fresh measurement before the
mode-1 gate can pass. The inconclusive result remains. The
[full-reference model concern](https://github.com/kim-em/hex-dev/issues/10377#issuecomment-5778449031)
is still unresolved. The required degree, coefficient-bit, maximal-support,
nested-field, allocation-byte and proof-checking tracks also remain open.

## Earlier calibration record

The earlier [complete paired run](data/sign-det-compare/6f07e03db/metadata.json)
and [same-binary profile](data/sign-det-compare/profile-6f07e03db/full-reference.manifest.json)
remain archived. That run set the spawn-signal multiplier to one and targeted
only 100 ms per inner batch. All reduced batches and the full arm's s=1,…,4
batches were below the normal tenfold spawn floor, so it is calibration
evidence, not the headline complexity
result. It also crossed a roughly 1.7× host-speed change during trial 2;
neither arm received a passing model verdict. All 60 samples and both
inconclusive verdicts remain intact. The old clean measured revision
`6f07e03db861a870da0872ea3b0f9fdcd0042616` can be reconstructed from
base `2e749387cfff74fa36c07f1c79af5a24f5ab7424` and its archived patch,
even though the rebase removed it from this branch's ancestry. The sole
source-hash difference between that old measurement and the rebased tree is
the #10434 proof and diagnostic additions in `HexSignDet/Descriptor.lean`;
neither benchmark arm uses them. The revised, calibrated registration was
measured separately above, rather than treating the old timing as if it were
from the new executable.
