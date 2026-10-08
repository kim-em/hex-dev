# Reducible-parent control

This control observes `(X²−2)(X²−3)(X²−5)(X²−7)`: a degree-eight parent with
four irreducible factors and eight distinct real roots. The public API and
independent selectors run in the same current binary. Prepared coefficients
and warmup are excluded; lazy root production, selection/exactification,
sorting and complete guards are timed. The guard requires eight strictly
ordered roots, multiplicity one, and exactly two roots of each quadratic
minimal polynomial, exhausting the root set.

Four fixed trial-major adjacent AB/BA pairs on one automatically leased CPU
retain all eight arms. All exact expected hashes match, without truncation,
filtering or reruns. Public median time is 196.296 ms (range 195.550–197.340);
independent selectors cost 198.847 ms (198.042–199.157). The median paired
ratio is 1.012, with individual ratios 1.006–1.017. Public whole-child RSS is
67.68 MiB, including setup/warmup/runtime. This is an observation, not a
speedup claim or allocation bound.

The irreducible-parent cache does not apply: `factorPicker` shares the
parent's factorization but preserves per-entry `exactFactor?` certification.
Factor irreducibility checks, isolation and whole-factor refinement to the
parent's Mahler precision remain repeated until a matching factor is found.
For these eight roots and four two-root factors, the successful selection
folds perform twenty factor attempts. The source identifies this work; the
complete timings do not isolate its share. Caching those certificates is a
possible future optimization with additional dependent cache/proof machinery.

This representative control completes in about 0.2 seconds for the current
bounded degree-eight use. It identifies no new unexplained timing growth or
unmet latency target. The readiness decision accepts the explicit fallback
algorithm and its observed cost; it does not claim that all redundant work
has been removed, that reducible parents gain the irreducible-cache speedup,
or that unrestricted higher degrees are performant. The irreducible
[degree ladder](../README.md) carries the corrected cache evidence separately.

Measured clean source and command/binary/source/host/CPU hashes are in
[metadata.json](metadata.json). Raw JSON/logs, source snapshots and the actual
[collector](collector.py.txt) are retained. The frozen executable remains in
the persistent directory recorded in [persistent-retention.json](persistent-retention.json).
No external comparison is inferred from this native control.
