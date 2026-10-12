# Matched sector sample protocol

## Question and inputs

Compare construction and exact sign evaluation of three samples in the same
positive sector `(sqrt(2), sqrt(2 + 2^(-k)))`, for `k = 0, 4, 8, 12`.
The original polynomial family is `[X² - 2, X² - (2 + 2^(-k))]`.
Every arm requires a positive point and the exact sign vector `[1, -1]`.
This finite comparison makes no asymptotic claim.

The boundary descriptors and their original selected root contexts are prepared
before timing. Each measured call retrieves its prepared consumer through an
`IO.Ref`, constructs a sample and forces its positivity and both polynomial
signs. The measured construction includes:

- Midpoint: collect the two original boundary roots into their shared context,
  then compute their midpoint with that context's ordinary operations.
- Dyadic: search `(1,2)` by rational bisection, comparing each midpoint against
  the two original selected root handles until both strict inequalities hold.
- Infinitesimal: enlarge the lower boundary's actual algebraic context, including
  checked descriptor rebuilding, and add the new parameter to the transported
  lower root. Evaluate the original coefficients through the composed inclusion.

Original boundary construction, executable startup, one configured warmup,
functional serialization and independent oracle checking occur outside timing.
The infinitesimal sample is native extension data; it is not an ordinary-real
witness. The independent Z3 RCF oracle checks its exact extension semantics.

## Capture schedule

Use the uninstrumented Lake executable `hexrealclosure_samples_bench` and the
pinned lean-bench fixed-call harness. Register six trial-major rounds. In each
round visit gaps `0,4,8,12` in that order. At each gap run the midpoint/infinitesimal
pair and then the dyadic/infinitesimal pair. Each pair's arms are adjacent and
alternate AB/BA order between rounds. Retain both independently measured
infinitesimal arms: one belongs to each matched pair.

Each invocation uses `--repeats 1 --min-total-seconds 0.5`; the harness retains
its batches and repeat counts. Its 120-second per-call cap and the collector's
3600-second process timeout are operational safeguards. Retain every completed
or failed observation. Do not discard samples because of host activity, wait
for a quiet CPU or retry automatically. At most one unchanged rerun is permitted
if the completed comparison is inconclusive.

Select and lease one CPU through `scripts/bench/cpu_lease.py`. Record host load
as context. Freeze and record the source commit, toolchain, package pins,
compiler override and executable/link-recipe digests before collection. Check
fresh functional output against the committed twelve-arm fixture and run the
pinned Z3/FLINT oracle before timing. Require unchanged source after capture.

## Analysis and limits

Report all six paired observations, medians and complete ranges by gap and
pair, with paired ratios formed within each round. Keep harness batch/floor
and failure fields in the raw exports. No significance test or general
complexity bound is inferred from this finite family.

Report exact dyadic cut counts and serialized value/context sizes separately.
These cases have a rational initial base and two positive quadratic boundaries.
They do not measure dyadic search in a non-Archimedean gap, all section/ray
alternatives, arbitrary tower depths, ordinary-real reconstruction or the
remaining whole-library operation counters.
