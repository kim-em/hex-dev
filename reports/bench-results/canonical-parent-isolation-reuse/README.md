# Canonical parent-isolation reuse

Canonical addition and multiplication now consume the certified isolation
arrays already produced while selecting their eliminant roots. When the chosen irreducible
factor is the enclosing polynomial, `exactIn?` reuses those arrays; proper
factors retain their own isolation. Ordinary-kernel equalities identify the
complete checked and total results with the former pipelines, including the
canonical representative and failures. Common-field rational/add/mul consumers
use the same producer. The stored representations and arithmetic are unchanged.
This does not implement the forward comparison strategies or direct-radical
representation migration.

## Measurements

[Scalar metadata](scalar/metadata.json) and [canonical metadata](canonical/metadata.json)
identify clean compiled sources `98cab2feb5` and `630a40345b`, frozen binary
hashes, source snapshots, leased CPU and host activity. Four trial-major blocks
alternate adjacent AB/BA order. All 48 scalar and 24 canonical arms complete,
with matching expected fingerprints. Separate frozen-binary verification below
checks runtime panic behavior. All completed observations are retained; there is no unchanged rerun or load rejection.
Operand preparation and separate warmup are excluded. Result guards remain
timed; benchmark sources and operational caps are identical between arms.
The full library build ran concurrently on the shared host.

| Operation | Size | Before median ms | After median ms | Median adjacent Before/After ratio |
| --- | ---: | ---: | ---: | ---: |
| Scalar add | degree 2 | 0.920 | 0.487 | 1.913 |
| Scalar add | degree 4 | 9.062 | 4.572 | 1.993 |
| Scalar add | degree 8 | 324.336 | 160.229 | 2.014 |
| Scalar sqrt | degree 2 | 12.495 | 11.061 | 1.136 |
| Scalar sqrt | degree 4 | 196.658 | 163.850 | 1.198 |
| Scalar sqrt | degree 8 | 8957.468 | 7115.180 | 1.268 |
| Canonical add | output degree 4 | 9.820 | 4.937 | 1.996 |
| Canonical mul | output degree 2 | 1.062 | 0.564 | 1.885 |
| Common powers | exponent limit 16 | 25.073 | 18.097 | 1.388 |

Scalar degree is the operand degree. Canonical sum/product have quadratic
operands; the output degrees differ. Common powers times actual construction
of the powers through exponent 16 in the quadratic field, with prepared gamma.
The latter three cases are fixed observations, not size models. Ratios are
medians of adjacent ratios; every individual ratio exceeds one. These are
host-specific improvements on the named fixtures, not general speed bounds.

[Scalar PNG](plots/scalar-comparison.png), [SVG](plots/scalar-comparison.svg)
and [PDF](plots/scalar-comparison.pdf) show all points, medians and observed
min–max ranges against retained FLINT qqbar and Z3 RCF references.
Those external curves reuse [the earlier scalar capture](../real-algebraic-scalar-annihilation/README.md).
They are not contemporaneous paired arms. External annihilation/sign arithmetic,
JSON and cleanup differ from the native canonical-polynomial/sign guard.
The severe gap persists. [Canonical cases](plots/canonical-cases.svg) show the
three distinct fixed fixtures. [analysis.json](plots/analysis.json) retains
every row and adjacent ratio.

Compiled provenance is `metadata.sources.Before/After`, not the exporter's
`env.git_commit`, which observes the collector checkout for both binaries.
The measured commits are reachable through
`evidence/issue-10577-parent-prototype` and `evidence/issue-10577-parent-fixed`.
[sources/](sources/) retains snapshots. Binaries and raw profiles remain under
the persistent root in [persistent-retention.json](persistent-retention.json),
with verified hashes; no capture relies on `/tmp`.

Reproduce pairs using `scripts/bench/fixed_conversion_paired.py --before
<frozen-before> --after <frozen-after> --output <new-directory>`; add
`--canonical-arithmetic-only` for the canonical cases. The executed
[collector](collector.py) is retained. Reproduce plots with
`scripts/plots/canonical-parent-reuse.py --input <scalar> --canonical
<canonical> --reference reports/bench-results/real-algebraic-scalar-annihilation
--output <plots>`.

## Attribution and verification

The clean changed-source [degree-4 square-root profile](profile/scalar-sqrt.manifest.json)
retains 812 kernel-window samples. Calibration (0.852 ms trimmed residual),
confidence and ±5 ms sensitivity checks pass. The [summary](profile/scalar-sqrt.summary.json)
places isolation at 95.32% inclusive cost, component refinement at 79.93%,
common-field presentation at 39.90%, and powers at 20.81%. Exact-factor work
still accounts for 31.16%. These shares overlap and cannot be added.
The profile explains remaining costs; it is not a per-operation admission quota.

[Verification logs](verification/) retain the successful full Lake build,
196 real-algebraic and 92 NumberField benchmark checks,
conformance, unchanged emitted fixtures, all 83 exact real-algebraic oracle
cases without skips, and 11 NumberField FLINT/PARI cases without failures.
[Panic verification](panic-verification/manifest.json) records exact commands,
compiled commits and binary/log hashes for the frozen After executables under
`LEAN_ABORT_ON_PANIC=1`. Both verifiers pass all 196/92 cases without panics.
The prototype verifier aborts with its original certification-failure diagnostic,
demonstrating that the guard detects the strict fallback. The existing CI smoke
wrapper now sets this guard for these two audited executables only.
Successful timing children discard stderr, so timing-arm logs establish no
separate panic-free claim; the plot analyzer checks result status and hashes.

The ordinary-kernel admission scan covers 354 roots and 1171 local modules,
with no admissions. Required CI must additionally pass on the final PR head.
All four assigned libraries remain Phase 3 pending the readiness audit.

## Retained failed prototype

The [prototype capture](prototype/metadata.json) records 23 completed arms
against `4dcae979fe`. The total producer passed a panic fallback as a strict
argument, producing panic/backtrace diagnostics under `verify` even when the mathematical
value and hash were correct. Successful `run` children discard these diagnostics. Capture was interrupted after diagnosing this;
the next in-progress arm produced no completed export. All completed exports,
logs and partial diagnostics are retained, including the cancelled full build
and stale conformance-executable attempt. They supply no performance claim.
The final source thunks the fallback and evaluates it only in the `none` branch;
the replacement measurements use changed source, not an unchanged retry.

## Concerns

Addition loses one redundant parent-isolation pass, but degree-8 square root
still costs about 7.1 seconds on this host and isolation dominates its profile.
Proper factors and final root exactification still need their own certified
canonical isolation. The historical polynomial-root comparisons also expose
large external gaps. These require further work under #10577; this focused
change does not establish Phase-4 readiness or weaken a performance claim.
