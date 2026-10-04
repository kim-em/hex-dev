# Complete local benchmark verification

[The current wrapper log](opus-followup-owned-smoke.log) passes all 196 scalar
and 93 Sturm registrations plus the coefficient-fixture check. The prebuilt
local wrapper takes 72 seconds for real algebraic and one for Sturm, 73 total
under the existing 600-second operational safeguard. The per-library soft
warning remains in the log. This is runtime/result wiring evidence on the
[recorded source hashes](verification.json), not a hosted CI result, scientific
timing admission or whole-repository headroom claim.

[The follow-up Lean build](opus-followup-lean.log) passes 9339 jobs, including
public remainder correspondence tests, ordinary-kernel axiom guards and both
parities of the square-root initializer. The [benchmark build](opus-followup-bench-build.log)
also passes; its inherited diagnostics remain retained.

[The earlier verifier log](scalar-196.log) passes the same 196 scalar
registrations on the annihilation-guard implementation measured at `a3ddc9473f`.
The descriptive 432-arm collection separately retains the frozen executable
and source snapshots. Required CI on the final PR revision remains necessary.

The [source admission audit](named-admission-audit.log) checks 295 mandatory
adapter/conformance roots and their union of 1103 local modules. The CI scanner
walks shared dependencies once within an audit; it still rejects missing local
imports, shadowed adapters and admissions and rereads sources on each new audit.
The ten lexer/graph regression tests pass.
