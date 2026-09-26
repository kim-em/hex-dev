# Reduced and full sign-table construction

`runSmallReduced` and `runSmallFull` construct sign tables for the same prepared
root domain P=X²−1 on the whole line and s copies of X, with s=1,…,5. Both
use direct moment products. The timed bodies include query construction,
matrix solving and checked table production. The reduced arm replays its
recursive support tree; the full arm checks its one full-system node. Untimed
preparation checks both tables against exactly two sign words, all negative
and all positive, each with count one. `inspect-small` separately verifies
literal dimensions and counts, not just matching result hashes.

The reduced arm declares Θ(s log s) on this two-root family: every balanced
node has a bounded matrix, and its query and sign slots are scanned in Θ(k)
work for a node containing k input polynomials. The full arm declares Θ(27^s)
scalar work from cubic worst-case rational Gauss-Jordan and dense
inverse-identity replay on the 3^s square moment matrix. This is a finite-input
wall-time model, not a bit-complexity claim for
arbitrary s. Rational row reduction may instead dominate; `inspect-full`
records the actual elimination updates and matrix dimensions to assess that
possibility. A model mismatch remains an inconclusive result, not a passing
upper bound.

`paired-small` uses the shared LeanBench sampler and summary for each arm. Six
fixed trial-major rounds keep the arms adjacent for every s and alternate
AB/BA order. Each completed arm is flushed before the next child. The Python
wrapper leases one CPU automatically, records host load as context, checks
that every child ran at the clean measured revision, validates the complete
sample stream and retains all verdicts. It sets `signalFloorMultiplier = 1`,
disabling the spawn-floor filter because per-call time is measured inside each
child over auto-tuned repeats; it never discards a completed sample or
automatically reruns an inconclusive result. Pairwise signed differences
and ratios are computed from adjacent samples before taking their medians.

This fixed-degree, fixed-coefficient family has support two. It does not cover
maximal support, growing degree or coefficient bits, nested field depth,
modulo-product comparisons, or descriptor operations. Child RSS includes
untimed preparation; allocation bytes and peak intermediate bits need separate
measurements. The larger sparse-family report covers s=64,…,2048 and is not
replaced by this reduced/full comparison.

## Recorded observations

Clean source `6f07e03db861a870da0872ea3b0f9fdcd0042616` completed all 30 adjacent
pairs (60 arm samples) on shared-host CPU 18 with Lean 4.34.1. Every result
matched the expected complete two-root table. The child environment reported
the same Git revision and `git_dirty = false`; source and executable hashes
matched before and after measurement. No completed sample was discarded, and
no rerun was used. The Python runner exits nonzero because both arms' model
verdicts are inconclusive; its metadata state is `complete`, and all samples,
summaries and checks are retained.

Both arms report **inconclusive** on this narrow schedule. The reduced arm's
normalized constants range from 54,760 to 98,429, and the full arm's from
111 to 1,015. The shared harness reported no slope and used its
multiplicative-range fallback. The sample stream changes speed abruptly by
about 1.7× during trial 2, between s=4 and s=5; both adjacent arms change
together. Trials 0–1 and the first four pairs of trial 2 form the early regime;
the remaining pairs form the late regime. The child also increases its
auto-tuned repeat counts after the change. This is observed host context, not
a reason to discard samples. Mixing the regimes raises the reduced arm's
normalized-constant range above the harness's 1.5 fallback threshold: within
either regime alone, the range is about 1.4. The reduced **inconclusive**
verdict therefore reflects this shift; these conditional ranges are not new
harness verdicts. This short schedule also cannot distinguish Θ(s log s) from
linear growth; the larger sparse-family report supplies scaling evidence.
The full arm's normalized constant falls over much of the schedule in either
regime, so its measured growth does not support the declared `27^s` model.
Neither recorded verdict is a passing upper-bound result.

| Queries | Reduced early/late median ms | Full early/late median ms | Median paired full/reduced ratio | Pair ratio range |
| ---: | ---: | ---: | ---: | ---: |
| 1 | 0.137 / 0.082 | 0.137 / 0.082 | 0.997 | 0.994–1.002 |
| 2 | 0.430 / 0.257 | 0.926 / 0.554 | 2.157 | 2.133–2.166 |
| 3 | 0.738 / 0.440 | 10.419 / 6.161 | 14.053 | 13.851–14.174 |
| 4 | 1.040 / 0.625 | 157.555 / 91.470 | 148.946 | 145.718–151.995 |
| 5 | 1.356 / 0.814 | 2,680.730 / 1,578.197 | 1,953.481 | 1,899.797–1,976.820 |

Early and late medians use respectively three and three samples at s=1–4,
and two and four samples at s=5. Each ratio is the median of six actual
adjacent ratios, not the ratio of arm medians. Both arms include their own
complete certificate check in the timed body. The near-equality at one query is
consistent with both solving and checking the same three-column leaf system.
At five queries the checked full
reference is much slower than checked support reduction on this fixed two-root
family. The signal-floor filter was disabled by configuration; the child still
auto-tuned inner repetitions, whose per-call timings are recorded inside it.

The [raw stream](data/sign-det-compare/6f07e03db/samples.jsonl) retains every
arm sample and unmodified harness summary; the [paired summary](data/sign-det-compare/6f07e03db/summary.json)
retains every signed difference and ratio. The [metadata](data/sign-det-compare/6f07e03db/metadata.json)
records commands, host context, source and binary hashes, and reconstruction
of the measured source from the [archived patch](data/sign-det-compare/6f07e03db/committed-source.patch).
The [small-input inventory](data/sign-det-compare/6f07e03db/inventory.log)
records literal dimensions and counts. The report itself is a result, not a
measured source file; the profile runner, both comparison scripts, all benchmark
source files and their library dependency closure are in the recorded source
hash set.

## Attribution of the full reference

A [timed-region profile](data/sign-det-compare/profile-6f07e03db/full-reference.summary.json)
of `runSmallFull 5` used the same executable SHA-256 as the paired comparison,
`781449ff716dedc46f8f326c0fb73e71fa9041ae0d6bae990c8a93dd06accafb`.
It ran from the same clean source revision, on automatically leased CPU 53,
with a five-second target and 999 Hz sampling. Its three timed regions total
4.749 seconds and retain 4,743 benchmark-thread samples. Timing calibration
residual was 0.861 ms, and confidence and both boundary-sensitivity checks
passed. No rerun was used. The 35 raw profiling artifacts are retained on the
shared host at `/home/kim/.local/share/hex-bench/sign-det-full-6f07e03db`;
the [manifest](data/sign-det-compare/profile-6f07e03db/full-reference.manifest.json)
records their hashes, commands and tool revisions. Untimed preparation lies
outside the analyzed regions.

| Inclusive operation | Percentage of timed samples |
| --- | ---: |
| `solveSystem` | 93.51% |
| `Matrix.inverse?` | 87.98% |
| `Matrix.rowReduce` | 87.94% |
| `eliminateColumn` | 87.05% |
| `Matrix.rowAdd` | 86.84% |
| `System.check` | 6.58% |
| `momentMatrix` | 4.36% |
| `Matrix.mulImpl` | 3.92% |

These inclusive paths overlap and must not be summed. Self attribution is
38.63% GMP, 29.07% allocation routines, 22.83% Lean runtime, 1.94% own Lean
code and 7.53% other; unresolved leaf symbols account for 0.84%.
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

| Queries | Eliminated rows | Rational row-add multiply/add pairs | Rational row-scale products | Integer inverse-check multiply/add pairs |
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
it is separate from the rational row-add path observed at each pivot. The
[complete per-column counts](data/sign-det-compare/6f07e03db/inventory-full.jsonl)
come from the same clean revision and executable hash as the paired run; their
[metadata](data/sign-det-compare/6f07e03db/inventory-full.metadata.json)
records the output hash and verified finite count identities.

The profile and operation inventory explain why the full arm's normalized
`27^s` timing constant declines on this schedule. They do not establish a
replacement wall-time model; the inconclusive result and open performance gate
remain. The [full-reference model concern](https://github.com/kim-em/hex-dev/issues/10377#issuecomment-5778449031)
is still unresolved. The required degree, coefficient-bit, maximal-support,
nested-field, allocation-byte and proof-checking tracks also remain open.
