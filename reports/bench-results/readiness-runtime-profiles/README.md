# Reduced-query and scalar square-root attribution

These captures use ordinary compiled, Mathlib-free benchmark executables.
Input preparation, warmup, hashing and startup lie outside the kernel sidecars.
Raw perf data, original/normalized/filtered samply profiles, kernel sidecars,
ELF symbols and command logs remain at the persistent paths in each manifest.
[retention.json](retention.json) verifies every recorded raw artifact hash.
No quiet-core preflight, load exclusion or unchanged profile rerun is used.

| Fixture | Kernel samples | Calibration residual ms | Allocation self share | Dominant inclusive phase |
| --- | ---: | ---: | ---: | --- |
| Reduced query, degree 262144 | 4333 | 0.346 | 8.63% | `modImpl` / `modArrayAuxImplGo` 90.79% |
| Square root of the positive root of `X⁴−2` | 970 | 0.652 | 38.35% | Complex isolation 96.70%; exactification 42.68% |

Both captures pass sample count, calibration and ±5 ms sensitivity checks.
Inclusive percentages overlap and must not be added. The reduced-query profile
confirms that the remainder-only worker, rather than an allocated literal
quotient, dominates the kernel. Its growing coefficients still require
quadratic bit work on the registered family.

The scalar square-root profile attributes the costly operation to parent
canonical construction and isolation. General number-field presentations account
for substantial work as well. It is concrete evidence of a remaining algorithmic
concern, not a fixed-budget admission. It does not claim every arithmetic or
polynomial-root family has a current representative capture.

Measured source is `20e29ae762`; source and executable hashes, profiler revision,
CPU leases 19/20, host context and exact commands are in the manifests. Reproduce
with `scripts/profile/readiness_capture.py`. These source-scoped captures do not
replace the preserved historical profiles or waive missing raw-profile coverage.
