# Wider complete-support matrix checking

This registration measures the existing `System.check` on complete ternary
moment systems at dimensions 243,729,2187,6561. The finite problem and cubic
coefficient-operation declaration are unchanged. The earlier size-3-through-729
solve/check observations and their inconclusive verdicts remain separate.

Preparation uses the existing library Kronecker product on witnesses obtained
from its ordinary one-column solver. It concatenates rows and columns in that
same order, gives every sign pattern count one, and computes moments using
the existing finite-observation operation. It does not implement a second
solver or Tarski-query kernel. Untimed inspection compares the entire system
with the ordinary solver at dimensions 1,3,9,27,81,243,729.

Before timing, larger inputs check the complete ordered row/column lists,
all counts, and the closed finite-observation moment formula: each exponent
coordinate contributes 3,0,2 at exponents 0,1,2 respectively, and the complete
moment is their product. Both exact inverse and count identities pass the
actual checker. The input guard also pins the denominator to 2^s, where
r = 3^s. A passing inverse identity with this fixed denominator determines
the integer inverse uniquely. The inventory records inverse/denominator/value bits, dimensions
and input/result hashes. No polynomial-root oracle is claimed at these sizes.

Only `System.check` is timed. It still performs all r³ integer multiply/add
pairs in the dense inverse identity, including zero entries. Other checker
work is O(r² log r) on this family. The declared model remains `r^3`; no
exponent, normalization constant or tolerance is fitted to old measurements.
The fixed four-rung schedule has six trial-major rounds and the unchanged
100 ms repeat target and shared harness settings. The operational child cap
is 3600 seconds. The old size-729 check was about one second; cubic extrapolation
to 6561 is roughly 730 seconds for planning, not a promised duration or
scientific budget. Host, bit costs and memory effects can differ. A timeout
is retained as a failed collection; a complete inconclusive result is retained
with that verdict. A native peak RSS around
2 GiB and a total collection lasting roughly 1.5–3 hours are planning
estimates, not observations. Larger matrices exceed typical CPU caches,
which can change the finite-range constant.

The preparation change avoids repeating large rational inversion for a
checker-only measurement. It does not change the timed checker, optimize the
library solver or resolve the separate complete-solve finding. The larger
integer witnesses are supplied data; matching the ordinary solver in the
overlap verifies their literal comparability.

Run:

```sh
lake build hexsigndet_bench
.lake/build/bin/hexsigndet_bench inspect-maximal-matrix-tensors
python3 scripts/bench/sign_det_matrix_wide.py --output /path/to/new-captures
```

The output must be new and outside the worktree. The collector uses the shared
automatic CPU lease, records host load, retains all completed observations
and binds clean source, executable and pinned harness before and after the
run. It retains the complete 1-through-729 overlap comparison and performs full
input guards before collecting the 24 timing points. A failure exits 2,
an inconclusive result exits 1 and Ctrl-C exits 130. SIGTERM, SIGHUP and SIGQUIT
exit with 128 plus the signal number unless inherited as ignored. For a
started runner, cancellation signals its entire process group and reaps the
leader before releasing the CPU lease; descendant exit may finish afterward.
An interruption during process startup can escape this cleanup. Once collection
has begun, the collector records these outcomes and final source bindings;
an interruption at the boundary of finalization can leave an unfinished record;
errors and signals before metadata creation leave no metadata.
The runner does not export its prepared-input hash. The inventory hash is
linked to timed children through the same binary and deterministic preparation.
Child peak RSS includes startup and preparation; it is not an isolated
callback allocation or live-object count. This protocol alone establishes no
performance result or Phase-4 completion.


## First larger checker collection

The first collection uses source 6b977999bc5b4008cea31ce4f9edfbe1bc3c6658,
rather than the revised collector described above. Its
[original metadata](data/sign-det-matrix-wide/6b977999bc-first/timing/metadata.json),
[24 timing observations](data/sign-det-matrix-wide/6b977999bc-first/timing/timings.json)
and [complete source reconstruction](data/sign-det-matrix-wide/6b977999bc-first/archive.json)
are retained without modifying the original records.

All 24 points returned the expected true check. The fixed cubic model remains
**inconclusive**, with normalized slope −0.166523 against tolerance ±0.15.

| Dimension | Median callback time (s) |
| ---: | ---: |
| 243 | 0.051484 |
| 729 | 0.986365 |
| 2187 | 22.949557 |
| 6561 | 578.715180 |

The original collector checks the denominator's bit length; it does not have
the newer exact-denominator guard or an overlap stage. The deterministic
tensor construction supplies denominator 2^s. A
[separate overlap capture](data/sign-det-matrix-wide/6b977999bc-first/overlap/metadata.json)
compares the whole literal witness against ordinary solving at every dimension
1 through 729. Its before/after binary hash equals the timing binary hash.
Both collectors, the full source tree patch and each recorded source hash
are verified in the archive.

The original collector's exit code 1 does not distinguish inconclusive
results from failures; its completed metadata state, successful points and
retained verdict establish this collection's outcome. The sole unchanged rerun is retained below under the shared-host policy. These observations
do not establish successful cubic scaling or Phase-4 completion.


## Sole unchanged rerun

The [original rerun metadata](data/sign-det-matrix-wide/6b977999bc-first/unchanged-rerun/metadata.json)
and [all 24 raw points](data/sign-det-matrix-wide/6b977999bc-first/unchanged-rerun/timings.json)
retain the same clean source revision, source hashes, binary and harness as the
first collection. Every point returned the expected successful check. The
cubic verdict remains inconclusive, with residual slope −0.155112, just outside
the unchanged ±0.15 interval. No further unchanged rerun is permitted.

| Dimension | First median (s) | Rerun median (s) |
| ---: | ---: | ---: |
| 243 | 0.051484 | 0.051217 |
| 729 | 0.986365 | 0.984929 |
| 2187 | 22.949557 | 22.863537 |
| 6561 | 578.715180 | 600.740774 |

Both slopes are negative, so the observed growth is slower than the declared
cubic model on this range. The larger sample does not establish the required
consistency gate merely because its slope is close to the interval. All 48
completed points remain included. Native process peak RSS includes startup
and preparation; it is not callback live memory. These results leave the
matrix timing gate open.

The successive three-fold-size ratios correspond to descriptive exponents
about 2.69, 2.87 and 2.94 in the first collection and 2.69, 2.86 and 2.97 in
the rerun. The retained per-spawn signal floors were about 28.9 and 40.4 ms,
compared with about 51 ms at the smallest rung, with multiplier one. The
falling constants and increasing exponents suggest lower-order costs on this
range; they do not establish subcubic checking. No point is excluded and no
model is fitted from these ratios.

Recheck the archive with:

    python3 -m scripts.bench.sign_det_matrix_archive reports/data/sign-det-matrix-wide/6b977999bc-first --reconstruct-source

The validator uses the hash-bound historical collector’s declaration and
validators. The reconstruction test requires the recorded main ancestor and
therefore full Git history, as fetched by CI.
