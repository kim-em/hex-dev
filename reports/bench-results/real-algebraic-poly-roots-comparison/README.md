# Actual real-algebraic polynomial roots against degree

These compiled comparisons call `RealAlgebraicPoly.roots` on `X^n−2` at
degrees 2, 4 and 8, and `X^n−√2` at degrees 1, 2 and 4. Coefficient height
is fixed; polynomial degree grows. Degree one returns one positive root;
the even degrees return exactly one negative and one positive root, all
simple. The complete increasing minimal-polynomial/sign/multiplicity array
identifies every root on these fixtures, by Eisenstein at 2.

The independent pinned Z3 RCF and FLINT qqbar drivers solve the corresponding
polynomials, sort their roots and check exact annihilation. Their fingerprint's
minimal polynomial is deduced from this mathematical fixture, rather than
extracted from their internal representation. Z3 returns distinct roots;
simple multiplicity follows from the nonzero constant and characteristic zero.
FLINT supplies multiplicities. This comparison does not claim generic
representation equivalence or time isolated root production.

Input coefficient objects, polynomial preparation and a separate child warmup
are excluded. Native solving, canonical exactification, reality filtering,
sorting and fingerprint construction are timed. External solving, sorting,
annihilation checks, JSON transport and temporary cleanup are timed.
No driver caches roots; persistent backend contexts may retain internal caches.
Protocol controls return the identical fingerprint without solving.

[capture.py](capture.py) fixes four trial-major blocks with adjacent native and
external arms in alternating AB/BA order, followed by a protocol control.
One CPU is automatically leased on the shared host. All completed, failed and
censored arms are retained, without load rejection or an unchanged rerun.
The exact executable is copied to persistent storage; commands, host context
and source fingerprints accompany each collection. Existing collections
cannot be overwritten. The 50 ms batching target and 60-second child cap are
operational settings, not scientific performance budgets or admission claims.

The separate [operational probes](../real-algebraic-poly-roots-probes/README.md)
retain failed degree-16 rational and degree-8 quadratic calls. Those censored
whole-child probes are not plotted as numerical root-operation timings.
No Phase-4 completion or metadata advancement follows from these comparisons.
