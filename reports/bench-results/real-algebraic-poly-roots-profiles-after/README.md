# Polynomial-root attribution after early nonreal rejection

These operation-only captures use source `edb3ef956`, with the proved early
rejection of nonreal lazy roots. The actual `RealAlgebraicPoly.roots` calls
cover `X^8−2` and `X^4−√2`, with prepared coefficient inputs.

| Fixture | Retained kernel samples | Calibration residual ms | Allocation % | Inclusive isolation % | Inclusive exactification % |
| --- | ---: | ---: | ---: | ---: | ---: |
| Rational degree 8 | 1250 | 0.978 | 38.80 | 96.08 | 76.72 |
| Quadratic degree 4 | 1235 | 0.730 | 36.92 | 96.36 | 76.36 |

Both pass kernel-window sample-count, calibration and ±5 ms sensitivity checks.
Inclusive phases overlap and must not be added. Although the nonreal roots
are rejected early, retained real roots still invoke `AlgebraicRoot.exact?`.
Repeated canonical isolation remains the dominant cost. The computational
fix changes only the owned real wrapper; it does not replace parent arithmetic
or canonical representatives. This attribution explains a remaining concern,
not a performance admission or an absolute budget.

The [earlier attribution](../real-algebraic-poly-roots-profiles/README.md),
all raw captures and the controlled timing pairs remain retained.
[retention.json](retention.json) checks all raw artifact hashes and records
the exact persistent executable. Manifests preserve commands, source hashes,
versions, CPU/host context, calibration and sensitivity diagnostics.
Raw perf data, original and normalized profiles, sidecars, symbols and logs
remain under `/home/kim/.local/state/hex/issue-10577-profiles/` at their recorded
paths. No quiet-core preflight, load rejection or unchanged rerun was used.

[source-equivalence.json](source-equivalence.json) identifies every fingerprinted
source against `89bed09cf`, including the definitionally equal predicate alias
and the unregistered manual-probe additions. The original measured commits
remain reachable through the pushed `issue-10577-root-measurement-source`
branch. Timings remain attributed to their recorded sources. The current
collector gained its clean-checkout preflight after these measurements; the
original collector is retained in [collection-driver.py.txt](collection-driver.py.txt). Profile manifests that say
`dirty: true` accompany unchanged computational snapshots and exact binaries.
