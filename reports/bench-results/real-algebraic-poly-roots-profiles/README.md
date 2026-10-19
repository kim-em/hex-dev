# Direct polynomial-root representative attribution

These native profiles cover the actual `RealAlgebraicPoly.roots` pipeline on
`X^8−2` and `X^4−√2`, using source `c6b821d7b` before early nonreal rejection.
They explain the poor external size comparisons; they do not attest the
subsequent optimized implementation or establish a scientific timing budget.

| Fixture | Retained kernel samples | Calibration residual ms | Allocation % | Inclusive isolation % | Inclusive exactification % |
| --- | ---: | ---: | ---: | ---: | ---: |
| Rational degree 8 | 801 | 0.853 | 42.07 | 95.51 | 89.89 |
| Quadratic degree 4 | 1285 | 0.696 | 40.78 | 95.72 | 84.82 |

Both kernel-window captures pass sample-count, calibration and ±5 ms sensitivity
checks. Inclusive phases overlap and must not be summed. `ofRoot?` formerly
exactified every lazy root before checking reality, including the nonreal
conjugate pairs. Canonical exactification re-isolates the minimal polynomial
and chooses its stored representative. These profiles identify that repeated
isolation as the dominant cost; allocation is a contributing overlapping share.

[capture.py](capture.py) leases a CPU automatically and keeps every completed
capture. The manifests record commands, versions, host context, source hashes,
diagnostics and all raw checksums. [retention.json](retention.json) checks every
raw artifact and records the exact persistent executable for symbolization.
Raw perf data, normalized and filtered profiles, sidecars, symbols, source
snapshots and command logs remain under
`/home/kim/.local/state/hex/issue-10577-profiles/` at the recorded paths.
