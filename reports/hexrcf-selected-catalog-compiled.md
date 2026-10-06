# Compiled costs for one supplied selected-root packet

The question is how much cumulative work is performed by lexical checking,
structured parsing and default catalog reconstruction on the adapter's checked
2,911-byte packet. The input represents the positive root of X²−α over the
selected positive root α of X²−2. Its independent ordinary-kernel regression
proves the original nested-root existential at the returned real point.

| Cumulative operation | Median μs | Minimum–maximum μs | Fresh-child peak RSS KiB |
| --- | ---: | ---: | ---: |
| Lexical bounds | 44.080 | 43.891–44.280 | 68,804–69,520 |
| Structured parser | 153.576 | 152.413–155.740 | 69,008–69,536 |
| Default catalog reconstruction | 407.027 | 404.238–408.128 | 69,500–69,936 |

All eighteen samples are retained. The fixed schedule has six trial-major
blocks, alternating forward and reverse order for the three operations. Each
arm contributes one warmed outer sample, autotuned to at least 0.2 seconds.
The IO.Ref input read and Unit→IO shape prevent constant folding. Result
consumption and hashing remain inside the timed batch. Every expected result
hash matched. Preparation, reification, literal creation and proof construction
are excluded from these per-call times. Child RSS includes startup, loaded
literal data, autotuning and the harness; it is not exclusive operation memory.
The collector separately retains whole-invocation wait4 resource observations.

The automatically leased CPU was 44 on chungus2 (AMD EPYC 9455). Host activity
was recorded and no completed sample was removed. These are absolute
observations for three different cumulative operations, not an algorithm
comparison, exclusive-stage subtraction, speedup or scaling study. No rerun was
performed. The first collector could not start because /usr/bin/time was absent;
no sample completed. The corrected collector uses wait4 without changing the
measured executable, input or fixed benchmark configuration.

The driver imports only the constructor byte module, owner RootBytes and
LeanBench. All 442 compiler-listed imports are retained in context.json and none
is Mathlib. The executable build passes 1,713 Lake jobs and all three semantic
smoke checks pass. Reconstruction includes the default owner's native
coefficient decoding/arithmetic and adjunction paths; it is not a strictly
production-free replay measurement. The result does not measure row checking,
root-set coverage, full tactic cost or quotation sharing.

The Hex source revision is d84cecfde40a2c2b09e55e8279793bcc98a3ae9f, with a clean
worktree at collection. Exact source, driver, collector and executable hashes
are in context.json. The benchmark export's git environment names the separate
external harness checkout (704867ddc886c58c30cd07a13bcf56c5d4cc7da4, dirty), not
Hex. Driver and collector snapshots, all raw exports/stdout/stderr, retained
build diagnostics and their digests accompany this report. The source-bound
packet's kernel acceptance is separate evidence from these compiled answers.

The retained [source context](data/hexrcf-selected-catalog-compiled/context.json),
[summary](data/hexrcf-selected-catalog-compiled/summary.json),
[raw samples](data/hexrcf-selected-catalog-compiled/samples.tar.gz),
[driver snapshot](data/hexrcf-selected-catalog-compiled/driver.lean.txt),
[collector snapshot](data/hexrcf-selected-catalog-compiled/collect.py.txt),
[build log](data/hexrcf-selected-catalog-compiled/build.log.gz) and
[digest manifest](data/hexrcf-selected-catalog-compiled/manifest.json) bind this
measurement to its historical source. The snapshots preserve the actual external
harness paths; reuse requires pointing them at the matching source checkout and
Lake-built executable. Later adapter changes are not timed by this record.
