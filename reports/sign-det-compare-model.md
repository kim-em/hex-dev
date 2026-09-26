# Reduced and full sign-table construction

`runSmallReduced` and `runSmallFull` construct sign tables for the same prepared
root domain P=X²−1 on the whole line and s copies of X, with s=1,…,5. Both
use direct moment products. The timed bodies include query construction,
matrix solving and checked table production. The reduced arm checks recursive
support evidence; the full arm solves the entire ternary system. Untimed
preparation checks both tables against exactly two sign words, all negative
and all positive, each with count one. `inspect-small` separately verifies
literal dimensions and counts, not just matching result hashes.

The reduced arm declares Θ(s log s) on this two-root family: every balanced
node has a bounded matrix, and its query and sign slots are scanned in Θ(k)
work for a node containing k input polynomials. The full arm declares Θ(27^s)
scalar work from the dense inverse-identity check on the 3^s square moment
matrix. This is a finite-input wall-time model, not a bit-complexity claim for
arbitrary s. Rational row reduction may instead dominate; `inspect-full`
records the actual elimination updates and matrix dimensions to assess that
possibility. A model mismatch remains an inconclusive result, not a passing
upper bound.

`paired-small` uses the shared LeanBench sampler and summary for each arm. Six
fixed trial-major rounds keep the arms adjacent for every s and alternate
AB/BA order. Each completed arm is flushed before the next child. The Python
wrapper leases one CPU automatically, records host load as context, checks
that every child ran at the clean measured revision, validates the complete
sample stream and retains all verdicts. It never filters a completed sample
or automatically reruns an inconclusive result. Pairwise signed differences
and ratios are computed from adjacent samples before taking their medians.

This fixed-degree, fixed-coefficient family has support two. It does not cover
maximal support, growing degree or coefficient bits, nested field depth,
modulo-product comparisons, or descriptor operations. Child RSS includes
untimed preparation; allocation bytes and peak intermediate bits need separate
measurements. The larger sparse-family report covers s=64,…,2048 and is not
replaced by this reduced/full comparison.

## Recorded observations

Clean source `e1f8009bbcc2137e5a78783b9c02f9b7da529230` completed all 30 adjacent
pairs (60 arm samples) on shared-host CPU 33 with Lean 4.34.1. Every result
matched the expected complete two-root table. The child environment reported
the same Git revision and `git_dirty = false`; source and executable hashes
matched before and after measurement. No completed sample was discarded, and
no rerun was used. The Python runner exits nonzero because the full arm's
model verdict is inconclusive; its metadata state is `complete`, and all
samples, summaries and checks are retained.

The reduced arm reports `consistent_with_declared_complexity`, with normalized
constants 52,061–73,560. The full arm reports **inconclusive**, with normalized
constants 106–552. The shared harness did not report slopes on this narrow
parameter range and used its multiplicative-range fallback. The full arm's
normalized constant falls across the schedule, so the measurements are faster
than its declared `27^s` model predicts; they are not a passing bound.

| Queries | Reduced median ms | Full median ms | Median paired full/reduced ratio | Pair ratio range |
| ---: | ---: | ---: | ---: | ---: |
| 1 | 0.082 | 0.045 | 0.552 | 0.550–0.556 |
| 2 | 0.259 | 0.403 | 1.559 | 1.550–1.573 |
| 3 | 0.441 | 5.287 | 11.970 | 11.948–12.029 |
| 4 | 0.625 | 84.957 | 136.251 | 134.086–138.513 |
| 5 | 0.822 | 1,516.588 | 1,842.015 | 1,819.588–1,860.969 |

Each ratio is the median of six actual adjacent ratios, not the ratio of arm
medians. The full reference is faster for one query, while the checked reduced
constructor is much faster by five queries on this fixed two-root family.
The [raw stream](data/sign-det-compare/e1f8009bb/samples.jsonl) retains every
arm sample and unmodified harness summary; the [paired summary](data/sign-det-compare/e1f8009bb/summary.json)
retains every signed difference and ratio. The [metadata](data/sign-det-compare/e1f8009bb/metadata.json)
records commands, host context, source and binary hashes, and reconstruction
of the measured source from the [archived patch](data/sign-det-compare/e1f8009bb/committed-source.patch).
The [small-input inventory](data/sign-det-compare/e1f8009bb/inventory.log)
records literal dimensions and counts. The reported ratios are end-to-end
construction timings; they do not establish the full arm's declared growth
model.

## Attribution of the full reference

A [timed-region profile](data/sign-det-compare/profile-e1f8009bb/full-reference.summary.json)
of `runSmallFull 5` used the same executable SHA-256 as the paired comparison,
`249e0d7e287a464d3fd95abe53e0b770e17b0b78732b3849fc191e5fe8ef6bac`.
It ran from the same clean source revision, on automatically leased CPU 15,
with a five-second target and 999 Hz sampling. Its three timed regions total
4.538 seconds and retain 4,530 benchmark-thread samples. Timing calibration
residual was 0.806 ms, and confidence and both boundary-sensitivity checks
passed. No rerun was used. The 35 raw profiling artifacts are retained on the
shared host at `/home/kim/.local/share/hex-bench/sign-det-full-e1f8009bb`;
the [manifest](data/sign-det-compare/profile-e1f8009bb/full-reference.manifest.json)
records their hashes, commands and tool revisions. Untimed preparation lies
outside the analyzed regions.

| Inclusive operation | Percentage of timed samples |
| --- | ---: |
| `solveSystem` | 98.28% |
| `Matrix.inverse?` | 92.45% |
| `Matrix.rowReduce` | 92.43% |
| `eliminateColumn` | 91.39% |
| `Matrix.rowAdd` | 91.24% |
| `System.check` | 3.49% |
| `momentMatrix` | 2.27% |
| `Matrix.mulImpl` | 2.10% |

These inclusive paths overlap and must not be summed. Self attribution is
34.19% GMP, 37.09% allocation routines, 20.11% Lean runtime, 2.08% own Lean
code and 6.53% other; unresolved leaf symbols account for 0.84%.
Allocation routine time is not an allocated-byte measurement. The anticipated
dense cubic integer identity check accounts for a small part of this timed
observation; rational row reduction dominates.

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
[complete per-column counts](data/sign-det-compare/e1f8009bb/inventory-full.jsonl)
come from the same clean revision and executable hash as the paired run; their
[metadata](data/sign-det-compare/e1f8009bb/inventory-full.metadata.json)
records the output hash and verified finite count identities.

The profile and operation inventory explain why the full arm's normalized
`27^s` timing constant declines on this schedule. They do not establish a
replacement wall-time model; the inconclusive result and open performance gate
remain. The [full-reference model concern](https://github.com/kim-em/hex-dev/issues/10377#issuecomment-5778449031)
is still unresolved. The required degree, coefficient-bit, maximal-support,
nested-field, allocation-byte and proof-checking tracks also remain open.
