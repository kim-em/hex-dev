# Shared parent refinement in real root enumeration

The public `RealAlgebraicPoly.roots` API now reuses both factorization and
Mahler-precision refinement across real entries sharing an irreducible parent.
The former cache reused initial isolation but still performed two parent
factorizations and one whole-parent refinement per entry. For a group of k
real entries, the corrected filtering path performs one factorization and
one whole-parent refinement, before constructing its selector closure.
Canonical construction and per-root selection remain. Proper-factor and
failed-certification cases retain the independent fallback.

`parentExact?_eq`, `rootPicker_eq`, `rootSelectors_eq` and the existing
ordinary-kernel `realRoots_eq_impl` prove the complete result equality,
including canonical representatives, ordering, multiplicities and checked
failures. No root representation or number-field arithmetic is duplicated.
The degree-eight conformance case compares independent and cached selectors
on all eight real entries, while existing mixed/reducible cases remain.

These observations compare the current public API with the original
independent selector algorithm **in the same binary**, not with a frozen
previous revision. Both include lazy root production, exactification, sorting
and complete guards. Polynomial preparation and warmup are excluded. Starting
with X and repeatedly squaring and subtracting two gives Eisenstein-at-two
polynomials of degrees 2/4/8, with exactly that many distinct real roots. The
guard checks the complete sorted root identity using the minimal polynomial,
root count, strict ordering and multiplicities.

Four fixed trial-major rounds use adjacent arms in alternating AB/BA order on
one automatically leased CPU. Each arm uses LeanBench's fixed registration
with one batch and a 50 ms minimum. All 24 arms succeed with matching expected
hashes, no truncation, filtering or reruns. Host activity is recorded context.

| Degree / real roots | Shared median ms | Independent median ms | Median paired improvement | Shared whole-child RSS MiB |
| --- | ---: | ---: | ---: | ---: |
| 2 | 1.593 | 2.300 | 1.33× | 67.49 |
| 4 | 9.915 | 22.725 | 2.32× | 67.74 |
| 8 | 202.828 | 905.832 | 4.46× | 67.77 |

[SVG](comparison.svg), [PNG](comparison.png) and [PDF](comparison.pdf) show
all points, median curves and min–max time ranges. RSS includes setup, warmup
and runtime; it is not operation allocation. These are representative
observations, not a fitted law or portable performance budget. Remaining
canonical isolation costs and higher degrees need practical assessment.
Existing FLINT/Z3 plots concern different input polynomials and retain their
own source scope; no external ratio is inferred for this family.

The clean measured source is `1a1375b97940529f12edfe8aa1f03cdffe0670fc`, retained
on `evidence/issue-10577-root-refinement`. [Metadata](metadata.json) records
commands, binary/source hashes, CPU, load and all arms. Raw JSON/logs and source
snapshots are committed; the frozen executable remains at the persistent
location in [persistent-retention.json](persistent-retention.json).
`Roots.c.gz` retains compiled placement evidence: the concrete-pair
`rootSelectors` producer computes cached factors/refinement before the
`rootPicker` closure, whose parent selector reads those arrays. The existing
conformance IR guard checks that the producer has one argument, preventing
compiler uncurrying from moving it into per-entry calls. Presence of a symbol
alone is not a runtime-count proof. Reducible fallback costs are excluded from
the once-per-irreducible-group statement.

The retained [collector](collector.py.txt) records the actual fixed schedule.
Run its commands from the recorded source with a fresh output directory to
reproduce. Regenerate plots with `python reports/bench-results/real-root-refinement-reuse/plot.py.txt` in an
environment with matplotlib.
