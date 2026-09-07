# Tower factorization comparison protocol

The hypothesis is that exact rational Euclidean squarefreeness tests inflate
Trager's cost through intermediate coefficient growth. A successful modular
squarefreeness certificate can replace those tests; an unsuccessful trial must
retain the exact fallback. Reconstruction, multiplicities, canonical ordering,
and recursive irreducibility checks remain required.

This experiment uses the existing fixed registrations in
`bench/HexNumberFieldTower/Bench.lean`. It makes no parametric complexity claim
and fits no exponent to timings. The canonical factorization and certificate
replay retain their registered mode-3 budgets of 2 seconds. The six fixed
Selmer comparator rungs (degrees 2, 3, 4, 6, 8, 12) measure constants only.
The headline report explains why the composite algorithm has no independently
derived tight wall-time model; this experiment does not change that assessment.

Before/after measurements use lean-bench on `chungus2`, CPU 13 (selected by
`scripts/bench/idle_core.py` before measurement), with five repeats,
`--min-total-seconds 0.2`, and the registered warmup. Save the baseline binary
before changing executable sources. Run the baseline and candidate on the same
CPU, without overlapping builds or timing runs; record CPU/sibling idle samples
and preserve the complete harness export and source commits. Compare all six
fixed rungs and both canonical degree-24 operations, including result hashes.
The existing PARI comparator remains informational; record fresh PARI pairs and
the protocol-overhead control if the provider is available. Do not compare new
Hex times directly with historical PARI measurements.

Inspect the rational squarefreeness calls and intermediate coefficient heights
to attribute any reduction. An unchanged unsuccessful modular trial must still
reject repeated factors and handle primes dividing the leading coefficient or
discriminant. Verify those branches, rational denominators, the public
factorization/checker regressions, and the Mathlib correspondence proofs.

These local measurements establish before/after constants, not a replacement
release-quality shared-host verdict or a change to Phase-4 coverage.

An attempt whose postflight sample finds either CPU 13 or sibling 61 at least
5% busy is retained as a contaminated diagnostic. Allow at most two retries
with the same settings, after the core and sibling are idle again; rerun both
binaries and PARI in each retry. The first candidate attempt crossed that
host-state threshold, so its export and host metadata are retained separately.
