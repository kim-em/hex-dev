# Direct polynomial-root operational probes

These calls exercise `RealAlgebraicPoly.roots`, rather than filtering supplied
roots or calling the integer-polynomial root helper directly. The complete
ordered minimal-polynomial/sign/multiplicity fingerprint identifies the roots
of `X^n−2` and `X^n−√2` on the recorded even-degree fixtures.

All seven correctness/cap probes are retained, including failed degree-16
rational and degree-8 quadratic calls. Each failed `run` invocation spent about
120 seconds: its separate warmup and measured children each reached the
60-second operational cap without a result. This is censoring of the complete
child, not a measured 120-second root operation. No successful result or lower
bound on operation-only time is inferred. The remaining five calls match their
explicit full-result hashes.

These are unpinned operational probes, not the adjacent shared-host scientific
comparisons. [source.json](source.json) records the dirty benchmark fingerprint,
parent revision, exact executable hash and purpose. [Bench.lean.txt](Bench.lean.txt)
preserves the tested source. The exact executable remains in persistent storage
under `/home/kim/.local/state/hex/issue-10577-verification/poly-roots-smoke/`.
No failed observation was discarded or repeated. The oversized registrations
are absent from the shipped CI smoke ladder; their unresolved cap failures
remain explicit performance concerns, and do not advance the phase counter.
