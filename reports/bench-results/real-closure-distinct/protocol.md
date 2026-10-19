# Complete root routes with increasing distinct-root counts

Compare `Trivial.Rational.roots` with `RealAlgebraicPoly.roots` on identical
rational polynomials. The generic arm includes complete generic isolation and
canonical conversion of every point or selected root. Input preparation and
rational-to-canonical coefficient lifting are outside timing. Both arms force
the same exact root-count, multiplicity, value and ordering consumer.

The registered case order is `Rational2`, `Rational4`, `Rational6`, `Rational8`,
then `Quadratic2`, `Quadratic4`, `Quadratic6`, `Quadratic8`. For `RationalN`, use
`∏_{i=1}^N (X-i)`. For `QuadraticN`, use the first `N/2` factors `X²-p` with
`p = 2,3,5,7`. All roots are real and simple. Input degrees and distinct-root
counts are 2,4,6,8 in both families. This is a fixed comparison across those
sizes and makes no asymptotic timing claim. It does not cover selected
algebraic coefficients or arbitrary towers.

Each rational root must equal its prescribed integer. Each quadratic root
must have its prescribed sign and square, in the exact order
`-sqrt(p_k),..., -sqrt(p_1), sqrt(p_1),...,sqrt(p_k)`. Explicit adjacent
comparisons also force ordering. Functional output retains canonical root
polynomials and isolating squares. Independently pinned FLINT reconstructs
those roots, factors the original input, and checks exact values, order and
multiplicity one. The native producer's point/selected counts are retained
outside timing. Their sum must equal the root count; the irrational quadratic
cases cannot contain rational point roots. These counts describe native
execution, and are not independent external predictions of its bisection policy.

Freeze source, fixture and this protocol before timing. Check the clean pinned
lean-bench package and capture the build log, compiler configuration, executable
hash, link recipe, toolchain, source snapshots, full Git source commit and
manifest. The compiler is explicit through `LEAN_CC`; the benchmark driver's
actual C-object trace must name it. Retain generated driver C, its compile trace
and the object hash. Lake may
reuse cached dependencies; this is not a fresh dependency rebuild. Source tags
retain the complete implementation beyond the selected source snapshots.
Functional output must match the committed fixture and the independent exact
oracle before timing begins.

Collect six trial-major rounds using lean-bench fixed calls with `--repeats 1
--min-total-seconds 0.5`. Visit all eight cases in registered order each round,
keeping generic/canonical arms adjacent and alternating AB/BA between rounds.
Retain all 96 exports, inner repeat counts, preparation logs, command outcomes
and failures. Warmup, calibration, startup, functional printing and oracle
checking are outside each reported inner timing batch.

Automatically lease one CPU and record host load as context. Do not wait for
quiet cores, discard completed samples or retry until clean. At most one
unchanged rerun is permitted after an inconclusive completed comparison.
Per-call and process limits (120 and 3600 seconds) are operational safeguards.
Enable `LEAN_ABORT_ON_PANIC=1` throughout capture.

GNU time additionally records maximum resident set size, user/system CPU time,
process elapsed time and exit status for each whole benchmark arm. These
include the driver, installation of all fourteen registered inputs, warmup,
calibration and measurement children. Maximum RSS
is the operating system's process/child high-water measure, not simultaneous
aggregate memory or operation-exclusive allocation. Preserve the tool identity
and raw resource records. These observations make no memory-complexity claim.

Report all paired per-call estimates, medians, full ranges, paired differences
and ratios; include input degrees, coefficient bits, root counts and the native
point/selected counts. Report memory in its whole-arm scope. Retain unexpected
costs and explain them from actual source work or a targeted profile. These
measurements do not replace remaining tower, normalization, certificate-depth,
MetiTarski or archived-input obligations in the Phase 4 coverage table.
