# Remainder-only Sturm value queries

The value-only rational fixture has head `X²−2`, query `X^m+1` and interval
`(-2,2)`. Both arms return `some 2`. Preparation constructs only the rational
head and query; it does not retain an unrelated integer certificate.

The [plot](plots/sturm-reduced-comparison.svg) and [analysis](plots/analysis.json)
show all 32 paired arms: four trial-major blocks at degrees 32768, 65536,
131072 and 262144. Adjacent original/reduced arms alternate AB/BA. Kernel
samples exclude preparation. Linux peak RSS covers the entire native invocation,
including input preparation, child execution and the process baseline.
Every paired signed-result hash matches. No activity threshold, filtering or
unchanged rerun is used.

At degree 262144 the original path uses about 2175 MiB peak RSS and the reduced
path about 137 MiB. The latter remains near the process baseline on this ladder;
this is an observed storage improvement, not a constant-space theorem. Its
input array still has `m+1` slots. Kernel time improves about 1.5× at this rung.

The [declared-ladder result](reduced-declared-ladder.json) uses the unchanged
registration at 131072, 262144, 524288 and 1048576, with four outer trials.
It passes the independently derived quadratic bit-work model with residual
slope −0.063658. All 16 points complete, with no signal exclusion or truncation.
Median kernel times are 1.389, 5.085, 19.384 and 77.998 seconds. At one million
coefficients this remains expensive; avoiding a quotient improves storage but
does not remove quadratic arithmetic work. This statement is family-specific.

The [metadata](metadata.json) records measured source `cd33400340`, executable
SHA-256, CPU 85, host activity, exact commands, immutable source snapshots and
artifact hashes. The frozen executable remains at the recorded persistent
collector path. Reproduce with `scripts/bench/sturm_reduced_comparison.py`.
The comparison requires ordinary compiled code and no Mathlib imports.

The implementation uses the existing `DensePoly.modImpl`/`modArray` worker,
then the existing shared Tarski producer. Whole-result correspondence, prepared
correspondence and ordinary umbrella tests use only Lean's standard logical
axioms. The existing literal certificate API remains available for evidence
bound to the unreduced query.

Two superseded collections remain available:

- [Initial reduction prototype](../sturm-reduced-prototype/): `%` still built a
  quotient; all 32 paired exports are retained.
- [Remainder worker with coupled preparation](../sturm-remainder-certificate-preparation/):
  the unrelated integer certificate dominated RSS; all 32 paired exports are
  retained.

Their scientific parents were stopped before aggregate export when their
measurement boundaries were found unsuitable. Their interruption records,
partial logs and failure metadata remain. They supply no declared-ladder
verdict; unexported per-rung scientific observations are unavailable. Their
original `source_unchanged: false` records are preserved because implementation
or collector edits occurred while those superseded diagnostics ran.

This result addresses the opt-in value-query path. The original `query` and
certificate producer still retain their literal quotient. It does not attest
all coefficient-sign, growing-chain, replay or frontend families.
