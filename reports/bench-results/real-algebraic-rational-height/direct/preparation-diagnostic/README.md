# Rational fixture preparation diagnostic

The unchanged compiled first rung at 262144 bits produced no kernel observation
in a single preparation probe. It was terminated with SIGTERM after
969.496897 seconds; stdout was empty. This was a diagnostic child invocation,
not a scientific scaling run. Its command, source and executable hashes,
CPU affinity, load observations and exit status are retained in
`../fixture-probe/metadata.json`. No completed sample is discarded.

Both completed perf attachments are retained at the persistent root recorded
in `artifacts.json`, together with the exact executable and checksums. The
20-second captures used 999 Hz / 8 KiB and 99 Hz / 65528-byte DWARF stacks.
Both identify GMP limb arithmetic but fail to unwind the Lean callers; they
are diagnostic evidence, not operation-only Phase-4 attribution or a confidence
claim. A separate native backtrace identifies the sampled worker's caller:

`ofRat → AlgebraicRoot.exact? → ZPoly.factorize → firstDirectPlan? →
scoutBetterPattern → directDegreeScore → defaultFactorCoeffBoundImpl →
ceilSqrt → floorSqrt → sqrtAux → sqrtStep → GMP division`.

`HexArith/Nat/Sqrt.lean` starts Newton iteration at `n`, and the factorization
prime planner repeatedly computes this coefficient-norm bound. The backtrace
establishes that this worker was in that preparation path; it does not measure
its aggregate fraction of total preparation. The fixture approaches 1/3,
so moving away from a dyadic boundary did not remove the preparation problem.
No cost is attributed exclusively to root isolation.

The four-rung rational-height declaration remains unmeasured and unadmitted.
Its 600-second operational child cap cannot be justified by this probe.
Historical completed rational-height observations and failures are retained
at their original sources. The direct recognition proof and mathematical
consumers do not depend on resolving this transitive preparation concern.

The transitive implementation is HexArith, used by HexPolyZ's Mignotte bound
and the Berlekamp–Zassenhaus prime planner. Issue #9809 concerns HexPolyFp
performance and does not own this square-root implementation. No transitive
phase metadata or implementation is changed by this diagnostic evidence.
