# Source-selection quotation allowance

Run `python3 reports/data/hexrcf-source-selection-budget/verify.py --check-head`.
The record pins seven sources and ten retained artifacts. It supplements the
[helper repair record](../hexrcf-replay-helpers/README.md) without changing its pins.

CI 39119984084 failed at head `287f54f01a` because the positive source-selection
reader exhausted the default one-million-node quotation allowance. This path
was absent from the 33-target local selection. The negative reader passed.
The conformance example now supplies an explicit two-million-node allowance;
the public default remains unchanged. Its measured cost is 1,347,886 nodes.
The expanded local selection contains 35 targets, including both source-selection
audit targets. The separate affected source-selection build passes: 14 exported
theorem bodies and 374 actual bodies/97 definitions/438 nonempty kernel traces,
with the existing producer checks and permitted axiom closure intact. The run
takes 4m20.118s and peaks at 4.8G, with no swap. This does not assert that the
entire expanded selection or a new CI run has already passed.

The third full-source experiment exhausts its explicit ten-million-node budget
at 9,983,347 consumed plus 16,654 requested after 1h1m52.765s, peak4.3G/no swap.
Complete packet acceptance, source finishing and its importing audit are not
reached. The exact driver inputs and failed log are retained. A shorter local
phase profile is the next investigation; no new full-prefix retry or larger
full-source allowance is justified by this record alone. No speedup is claimed.

#10358 remains open for its full implementation and evidence requirements.
Own local builds remain serial under aggregate32GiB, swap disabled and two Lean
threads. The test allowance does not alter that memory cap or library defaults.
