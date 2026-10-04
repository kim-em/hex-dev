# Direct rational leaves after the bit-length square-root initializer

The clean measured source is `16cff198bb`. Canonical degree-one inputs have
primitive coefficient height 262144, 524288, 1048576 and 2097152 bits and tend
to 1/3. The frozen native executable and immutable source snapshots are retained.
The operation timer excludes canonical preparation; whole-parent elapsed time
includes all child preparation and execution. These boundaries are distinct.

| Registration | Retained points | Residual slope | Verdict | Median at 2097152 bits |
| --- | ---: | ---: | --- | ---: |
| Direct recognition | 16 | +0.015245 | Two-sided linear pass | 57.990 µs |
| Rational floor | 16 | −0.013195 | Two-sided linear pass | 24.644 µs |
| Rational ceiling | 16 | −0.017619 | Two-sided linear pass | 24.070 µs |

All three use the declared fixed trial-major schedule, four outer trials, 100 ms
batch target, signal multiplier one and a 600-second whole-child safeguard.
No rows are removed or budget-truncated. No load filter, quiet-core preflight
or unchanged rerun is used. These results admit only their named operation
families on this source; they are not a controlled before/after ratio.

Canonical preparation remains expensive: the full recognition parent took
2263 seconds despite microsecond operation times. The initializer fixes the
excessive Newton start in the former preparation diagnostic; general degree-one
factorization and canonical isolation remain in the call path.

[Completed snapshot](completed-snapshot.json) records source, native hash,
leased CPU and host activity. It is explicitly a snapshot of the first three
completed registrations. The former-quotient-control run remains in
the persistent collection named there; no result is inferred until
its export completes. Their evidence and representative operation attribution
remain required before full family admission. The underlying compiler and
operation declarations are retained as source snapshots.

[Size plot](plots/rational-height.svg) shows all completed points and their
median curves. Regenerate it with:

```sh
python3 scripts/plots/real-algebraic-readiness.py --kind height \
  --input reports/bench-results/real-algebraic-rational-height-after-sqrt \
  --output reports/bench-results/real-algebraic-rational-height-after-sqrt/plots
```
