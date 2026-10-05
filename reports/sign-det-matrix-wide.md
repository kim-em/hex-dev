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
actual checker. The inventory records inverse/denominator/value bits, dimensions
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
or inconclusive result remains a retained finding. A native peak RSS around
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
an inconclusive result exits 1 and an interrupt exits 130, with the reason
recorded in metadata.
The runner does not export its prepared-input hash. The inventory hash is
linked to timed children through the same binary and deterministic preparation.
Child peak RSS includes startup and preparation; it is not an isolated
callback allocation or live-object count. This protocol alone establishes no
performance result or Phase-4 completion.
