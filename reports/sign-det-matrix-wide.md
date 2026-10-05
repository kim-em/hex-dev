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
and preparation; it is not callback live memory. The original harness findings are retained; the finite-range investigation
below supplies their disposition without changing either verdict.

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


## Finite-range explanation

A short representative profile uses the same unchanged revision `6b977999bc`,
compiled binary and source hashes as both timing collections. It samples one
cold `runTensorCheck` call at dimensions 243 and 729, using stock `perf` at
2000 Hz. The [archive](data/sign-det-matrix-attribution/6b977999bc/archive.json)
retains both raw perf recordings, operation-window sidecars, result records,
leaf and attempted stack exports, the binary's symbol table, retained load mappings, collector and
checksums. All completed captures are included. These are attribution captures,
not new scaling samples or another unchanged timing rerun.

The exact monotonic callback windows contain 119 and 2711 leaf samples,
respectively. The compiled dense integer dot-product loop accounts for 66
(55.5%) and 1960 (72.3%). These are direct leaf counts, not inclusive caller
attribution. The attempted dwarf stack export often has no frames; no recovered
stack attribution is claimed. Startup and preparation fall outside the windows.
All in-window samples belong to one thread of the profiled child.
The small capture has substantial sampling uncertainty; even the larger
profile supplies approximate relative costs, not exact phase times.

`System.check` performs exactly r³ dense multiply/add pairs. Its other work
includes constructing r² moment entries of length s, distinctness checks on
length-s words, matrix-vector multiplication and literal equality. This is
O(r²s) work on this family. List construction and small exponentiation incur
allocation and runtime calls; they cost more per source operation than the
compiled machine-integer dot-product loop. The retained leaf counts include
list zip/map, exponentiation, GMP and allocator functions. Thus non-cubic
work is material on the smallest inputs, rather than an unexplained constant.

The source predicts that non-cubic work's contribution to time/r³ decreases
between 1/r and s/r, while the dense loop's contribution is approximately
constant before memory effects. Treating non-dense leaves as lower-order work
is an attribution assumption supported by the source: the dot-product operands
and sums stay in machine integers here, no big-integer dot-product helpers
appear, and the remaining matrix operations are quadratic.

The table shows both profile bases, using s/r decay. Ratios mean
(T/r³ at the target)/(T/r³ at the base). Profile weights are independent of
the scientific timings; these are rough predictions, not a fitted model.

| Profile base | Target | Predicted ratio | First observed ratio | Rerun ratio |
| ---: | ---: | ---: | ---: | ---: |
| 243 | 729 | 0.733 | 0.710 | 0.712 |
| 243 | 2187 | 0.624 | 0.611 | 0.612 |
| 243 | 6561 | 0.581 | 0.571 | 0.596 |
| 729 | 2187 | 0.831 | 0.862 | 0.860 |
| 729 | 6561 | 0.764 | 0.805 | 0.837 |

For the smaller profile, a rough binomial 95% interval for the dense share is
47–64%, giving a predicted final ratio of about 0.50–0.67. The larger profile's
sampling interval is about 71–74%; its predictions undershoot the observed
ratios by about 4–9%. Pure 1/r decay from the smaller base predicts ratios
0.703, 0.604 and 0.571 instead; the exact choice of lower-order term does not
substantially change the rough conclusion. These intervals ignore sample
correlation, and are descriptive uncertainty estimates, not acceptance tests.
The two profiles predict the direction and approximate scale of the decline;
they do not supply a precise timing law. Large matrices exceed CPU caches,
which can raise the dense-loop constant and oppose the declining overhead.
No measured cache attribution is claimed.

The scientific runs used warm callbacks. These profiles use one cold call,
user-mode cycles only and dwarf stack sampling. Their windows lasted 59.7 ms
and 1361.2 ms, about 16% and 38% longer than the first warm medians. Sampling,
first-touch allocation and unsampled kernel faults can change the proportions.
Transferring their leaf shares to the warm runs is an assumption. The observed
normalized decline is consistent with the source explanation at this rough
precision, with these explicit sampling and cache limits.

Under [Choosing the complexity claim](../SPEC/benchmarking.md#choosing-the-complexity-claim),
this supplies the finite-range disposition of the inconclusive findings. The actual cubic
operation bound and checker implementation are retained. No point, exponent,
tolerance, warmup setting or original verdict changes. A further collection
solely to move the fitted slope across ±0.15 would add little useful evidence;
no larger matrix ladder is required for that purpose. Other Phase-4 families
and explicit comparisons still require their own evidence.

Validate the archived operation windows, source/binary agreement, successful
answers and leaf summaries with:

    python3 -m scripts.bench.sign_det_matrix_attribution reports/data/sign-det-matrix-attribution/6b977999bc

The validator parses retained records without executing archived Python. The
original source reconstruction and all 48 scientific points remain checked
by `sign_det_matrix_archive`.

Leaf exports are reproduced from each raw recording using `perf script --ns
--no-demangle --hide-call-graph -i perf.data -F pid,tid,time,ip,sym,dso`;
adding `--show-mmap-events` also exports the load mappings. The validator
checks executable text leaf addresses against their mapped image and retained
`nm -S --defined-only` symbol intervals. PLT trampolines are checked by mapping
only and remain non-dense; system-library leaves do not enter the dense count.
The computational source closure contains 275 files; the timing archive
additionally hashes five collector/documentation files, which are excluded
explicitly from the closure comparison. These are the same clean revision.
