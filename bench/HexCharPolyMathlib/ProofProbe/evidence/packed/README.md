The paired shipping sweep is `report.json`; `paired-logs.tar.gz` contains
its unmodified Lake output. The report records the baseline commit, source
hashes, CPU lease, host load, order, kernel time and end-to-end time for every
sample. `Quoted` is the scalar list checker. `Original` runs in the frozen
baseline checkout; `Packed` runs the new Mathlib frontend.

`diagnostic-reports.json` retains all diagnostic results, including failed
builds, interrupted samples and operational timeouts. `diagnostic-probes.tar.gz`
contains their raw logs, measured source snapshots, and the representative
`perf`/Lean diagnostic attribution. These are single-run diagnostic observations
on their recorded CPUs, not paired speedup estimates. Every completed sample
is retained; none is rejected on account of host load.

The diagnostic variants cover cached packed columns, native module compilation,
materialization through literal entries, expression sharing, named certificate
data, shift-based packing, and full convolution. The final checker uses cached
packed columns, native production from literal entries, shift-based packing,
and one packed multiplication for each full Toeplitz convolution. Expression
sharing and named data did not improve the observed kernel time. The
`entry-profile` directory records failed builds and is not a timing result.
The initial `packed-comparison` has an explicitly recorded interrupted sample;
the two later interpreted-function variants hit the 300-second timeout.

To inspect a log or measured source without extracting everything:

```bash
tar -tzf paired-logs.tar.gz
tar -xOzf paired-logs.tar.gz 0-32-Quoted-Packed.log
tar -tzf diagnostic-probes.tar.gz
```

The representative size-32 kernel profile in
`entries-profile/kernel-perf.txt` attributes about 48% of samples to expression
equality traversal, another 8% to `is_equal`, and about 11% to
big-integer comparison (`lean_nat_big_eq` and `__gmpz_cmp`). That variant checks Toeplitz
multiplication as a linear combination of shifted columns. The full-convolution
certificate removes those repeated shifted expressions: its only product check
is `pack previous * pack column = pack fullProduct`, followed by comparison of
the required prefix. All coefficients, including the unused high coefficients,
are bounded and authenticated by the injectivity proof.
