# Paired complete-root comparison for full Thom words

Compare the generic complete-root route before and after the tower consumes
`Descriptor.fullOrder` for two full derivative encodings of the same literal
head. The fallback for partial encodings or different heads remains the checked
common-product comparison. The ordinary-kernel total-order and equality proofs
retain their statements and the standard three axioms.

Use the unchanged `TrivialMeasurements` benchmark and exact consumer on
`Rational2/4/6/8`, then `Quadratic2/4/6/8`: respectively `∏(X-i)` and the
first N/2 factors `X²-p`, for p=2,3,5,7. Both arms call the registered `.generic`
function, including complete isolation, canonical conversion and the exact
root-count, order, multiplicity and value consumer. Preparation remains outside
inner timing. Degree equals real-root count; these cases do not cover degree
independently of real-root count, nonreal or nondyadic rational roots, selected
algebraic coefficients or arbitrary tower depth.

Freeze clean Before and After sources and copied executables before timing.
The only changed Lean files are the tower comparator, its functional tests,
its correspondence proof and its axiom guards. The computational library
change is the guarded shared Thom call; benchmark inputs and consumer are
identical. Retain exact Git source identities, source snapshots, pinned clean
LeanBench, compiler wrapper/version, generated benchmark and comparator C,
actual C-object traces/hashes, link recipe and binary hashes. Record the whole
linked object cohort. Objects with identical generated C must be byte-identical
across arms. Generated C may differ only in RootOrder and its inlined callers
Trivial and TrivialMeasurements; those three objects must use matching compiler
commands with normalized source paths. Use the same
explicit `LEAN_CC` for both arms; cached dependencies are permitted and
recorded, without calling this a fresh build of the whole graph.

Each frozen executable must emit the identical committed distinct-root fixture.
Pinned python-flint independently reconstructs every emitted canonical root and
checks completeness, values, order and multiplicities before timing.

Collect six trial-major blocks in the registered family/size order. Keep
Before/After arms adjacent, alternate AB/BA between blocks, and use the
unchanged fixed registration with `--repeats 1 --min-total-seconds 0.5`.
There are exactly 96 arms. Keep every export, inner-repeat count, log, command
and failure. Use `LEAN_ABORT_ON_PANIC=1`; retain the registration's 120-second
per-call safeguard and a 3600-second process safeguard. These are operational
limits rather than scientific timing budgets.

Use one automatically leased CPU, record affinity and host load, and do not
wait for quiet cores or discard completed samples. No automatic rerun is
permitted; at most one unchanged rerun may follow an inconclusive completed
capture, retaining both. Report medians, all six paired ratios/differences and
full ranges, without a significance or asymptotic claim. Child RSS remains a
whole-process high-water observation rather than exclusive allocation evidence.

The prior generic-route profiles motivate this comparison. Do not profile the
change by default. This comparison does not replace the remaining #10378
joint-realization, multilevel reconstruction, tower8 or Phase 4 obligations.
