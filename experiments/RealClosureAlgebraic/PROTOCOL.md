# Algebraic representation experiment

This is an isolated architecture experiment, not a completed library phase.
Its source is based on c08268dec030a81a5da124a6d8060c1420c779e7.

The selected root is positive sqrt(2), isolated in (1,3/2]. Test both
X²−2 and the squarefree reducible (X²−2)(X²−3). Zero testing uses remainder,
gcd, and the existing integer Sturm root count. Nonzero representatives remain
unreduced. Inversion splits off factors not containing the selected root.
No Field instance is declared on representatives.

Validation: kernel-reduced examples, generic Lean division-transfer theorem,
full executable result vectors checked by python-flint and independent exact
Q(sqrt(2)) pair arithmetic. The transfer theorem is conditional on preservation
and zero reflection: it is not a proof that this prototype supplies those laws.

Measurement schedule fixed before running: 12 cases, six blocks each, adjacent
arms each/batch in even blocks and batch/each in odd blocks. Case order is:
minimal/reducible descriptor; generic/shared-factor coefficients; lengths 4,8,16.
Shared-factor coefficients are multiplied by X²−3, so gcd/Sturm zero testing is
exercised in the reducible descriptor. Inputs are constructed before timing.

Use lean-bench fixed registrations, one retained measurement per arm per block,
one discarded harness warmup, and a 50ms inner-batch floor. Pin to one
automatically leased CPU, record host/load/versions/source hashes, and retain
every completed sample without activity-based exclusions. No rerun is planned.
The orchestration script controls order only; lean-bench owns all timing.

These fixed registrations compare a design choice; they make no Phase-4
complexity claim. Both include a full semantic output digest, which uses an
independent minimal-polynomial reduction. Preparation and instrumentation are
outside timing. Report paired median ratios and their range, plus operation
counts; do not extrapolate these small one-level cases to tower8.

`tracedMul` instruments a shadow of the actual convolution and is checked against
both executable arms. It counts zero tests in the algorithms being compared;
its final reconstruction into typed Elements performs additional checks that
are excluded from these logical counts. It is not itself a timed implementation.
